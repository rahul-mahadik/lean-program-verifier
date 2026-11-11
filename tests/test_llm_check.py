"""Parser/security unit tests; Lean integration is explicitly opt-in."""

from __future__ import annotations

import hashlib
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("llm_check", ROOT / "scripts/llm_check.py")
assert SPEC and SPEC.loader
checker = importlib.util.module_from_spec(SPEC)
sys.modules["llm_check"] = checker
SPEC.loader.exec_module(checker)

CASE = {"id": "count_up", "lean_name": "MiniVerify.Benchmarks.countUp"}
GOOD = {"invariant": "s.x <= n", "variant": "n - s.x", "solver": "omega"}


def axiom_log(axioms: str = "propext, Classical.choice, Quot.sound") -> str:
    return "\n".join(f"'{name}' depends on axioms: [{axioms}]"
                     for name in checker.REQUIRED_THEOREMS)


class ExpressionTests(unittest.TestCase):
    def test_supported_typed_expressions(self):
        result = checker.parse_expression("s.x + s.y == n + m and not s.i > s.n", "bool")
        self.assertIn("s.x", result)
        self.assertIn("∧", result)
        self.assertIn("¬", result)
        self.assertEqual(checker.parse_expression("(n - s.x) // 2", "nat"), "(((n - s.x) / 2))")
        self.assertIn("%", checker.parse_expression("s.x % 2", "nat"))
        self.assertIn("∧", checker.parse_expression("0 <= s.x < n", "bool"))
        self.assertEqual(checker.parse_expression("True", "bool"), "(True)")

    def test_forbidden_syntax_and_type_confusion(self):
        cases = [
            ("__import__('os').system('echo bad')", "nat"),
            ("s.__class__", "nat"), ("s.data", "nat"), ("s.x.real", "nat"),
            ("s", "nat"), ("x", "nat"), ("a", "nat"), ("s.x[0]", "nat"),
            ("[s.x for s in []]", "nat"), ("lambda s: s.x", "nat"),
            ("n; import os", "nat"), ("by exact True.intro", "bool"),
            ("True\naxiom malicious : False", "bool"), ("n # hidden", "nat"),
            ("-1", "nat"), ("-s.x", "nat"), ("+1", "nat"),
            ("True + 1", "nat"), ("True == 1", "bool"),
            ("s.x and True", "bool"), ("not s.x", "bool"),
            ("1", "bool"), ("s.x < n", "nat"), ("False", "nat"),
            ("n / 2", "nat"), ("n ** 2", "nat"), ("n is m", "bool"),
            ("n if True else m", "nat"), ("(n := 1)", "nat"),
            ("'n'", "nat"), ("1.0", "nat"), ("None", "nat"), ("ｎ", "nat"),
        ]
        for expression, kind in cases:
            with self.subTest(expression=expression), self.assertRaises(checker.CandidateError):
                checker.parse_expression(expression, kind)

    def test_resource_limits(self):
        cases = [
            "n" * (checker.MAX_EXPRESSION_LENGTH + 1),
            "(" * (checker.MAX_DEPTH + 1) + "n" + ")" * (checker.MAX_DEPTH + 1),
            str(1 << checker.MAX_INTEGER_BITS),
            " or ".join(["True"] * 100),
            "+".join(["n"] * 50),
        ]
        for expression in cases:
            with self.subTest(expression=expression[:50]), self.assertRaises(checker.CandidateError):
                checker.parse_expression(expression, "nat")

    def test_schema_is_closed(self):
        for value in [None, [], {}, {**GOOD, "proof": "by sorry"},
                      {**GOOD, "variant": 0}, {**GOOD, "invariant": True},
                      {**GOOD, "solver": "by omega"}]:
            with self.subTest(value=value), self.assertRaises(checker.CandidateError):
                checker.validate_candidate(value)

    def test_render_uses_only_frozen_case_and_trusted_tactics(self):
        rendered = checker.render_candidate(CASE, GOOD)
        self.assertEqual(rendered, checker.render_candidate(CASE, dict(GOOD)))
        self.assertEqual(rendered.count("import "), 1)
        self.assertTrue(rendered.startswith("import MiniVerify.Benchmarks\n"))
        self.assertIn("Case.verify countUp n m", rendered)
        self.assertIn("Case.executable_correct countUp n m", rendered)
        self.assertNotIn("reference.json", rendered)
        for name in ["countUp\naxiom injected : False", "Other.countUp", "arbitrary"]:
            with self.assertRaises(checker.CandidateError):
                checker.render_candidate({"lean_name": name}, GOOD)


class CheckerTests(unittest.TestCase):
    def test_compiler_success_requires_complete_allowed_axiom_reports(self):
        logs = [
            (0, axiom_log(), True),
            (0, axiom_log("sorryAx"), False),
            (0, axiom_log("arbitraryAxiom"), False),
            (0, "", False),
            (0, axiom_log().splitlines()[0], False),
            (0, axiom_log() + "\n" + axiom_log(), False),
            (1, axiom_log(), False),
        ]
        for code, log, success in logs:
            with self.subTest(code=code, log=log), tempfile.TemporaryDirectory() as out:
                with patch.object(checker, "_run_lean", return_value=(code, log, False)):
                    report = checker.check_candidate(CASE, GOOD, ROOT, Path(out), 1)
                self.assertEqual(report["verified"], success)
                self.assertEqual(report["success"], success)
                source = (Path(out) / "candidate.lean").read_text()
                self.assertEqual(report["source_sha256"], hashlib.sha256(source.encode()).hexdigest())
                self.assertEqual((Path(out) / "lean.log").read_text(), log)

    def test_invalid_candidates_never_reach_subprocess(self):
        with tempfile.TemporaryDirectory() as out, patch.object(checker, "_run_lean") as run:
            report = checker.check_candidate(CASE, {**GOOD, "variant": "by sorry"}, ROOT, Path(out), 1)
            run.assert_not_called()
            self.assertFalse(report["verified"])
            self.assertEqual(report["status"], "invalid")
            self.assertEqual((Path(out) / "candidate.lean").read_text(),
                             "-- Candidate rejected before Lean execution.\n")
            self.assertTrue((Path(out) / "lean.log").is_file())

    def test_invalid_timeout_does_not_run(self):
        for timeout in [True, 0, -1, float("inf"), float("nan"), 3601]:
            with self.subTest(timeout=timeout), tempfile.TemporaryDirectory() as out:
                with patch.object(checker, "_run_lean") as run:
                    report = checker.check_candidate(CASE, GOOD, ROOT, Path(out), timeout)
                    run.assert_not_called()
                    self.assertFalse(report["verified"])

    def test_timeout_and_missing_tool_are_not_success(self):
        with tempfile.TemporaryDirectory() as out:
            with patch.object(checker, "_run_lean", return_value=(-9, axiom_log(), True)):
                report = checker.check_candidate(CASE, GOOD, ROOT, Path(out), 1)
            self.assertEqual(report["status"], "timeout")
            self.assertFalse(report["verified"])
            with patch.object(checker, "_run_lean", side_effect=FileNotFoundError("lake")):
                report = checker.check_candidate(CASE, GOOD, ROOT, Path(out), 1)
            self.assertEqual(report["status"], "error")
            self.assertTrue((Path(out) / "lean.log").is_file())

    def test_timeout_kills_process_group_and_uses_no_shell(self):
        with patch.object(checker.subprocess, "Popen") as popen, patch.object(checker.os, "killpg") as kill:
            process = popen.return_value.__enter__.return_value
            process.pid = 12345
            process.returncode = -9
            process.communicate.side_effect = [subprocess.TimeoutExpired("lean", 1), ("timeout", None)]
            self.assertEqual(checker._run_lean(ROOT, Path("/tmp/candidate.lean"), 1), (-9, "timeout", True))
            kill.assert_called_once_with(12345, checker.signal.SIGKILL)
            self.assertEqual(popen.call_args.args[0], ["lake", "env", "lean", "/tmp/candidate.lean"])
            self.assertTrue(popen.call_args.kwargs["start_new_session"])
            self.assertNotIn("shell", popen.call_args.kwargs)


@unittest.skipUnless(os.environ.get("MINIVERIFY_LEAN_INTEGRATION") == "1",
                     "set MINIVERIFY_LEAN_INTEGRATION=1 for actual Lean checks")
class LeanIntegrationTests(unittest.TestCase):
    def test_good_candidate_and_real_negative_vcs(self):
        candidates = [
            (GOOD, True),
            ({**GOOD, "invariant": "True"}, False),
            ({**GOOD, "variant": "0"}, False),
        ]
        for candidate, expected in candidates:
            with self.subTest(candidate=candidate), tempfile.TemporaryDirectory() as out:
                report = checker.check_candidate(CASE, candidate, ROOT, Path(out), 45)
                self.assertEqual(report["verified"], expected,
                                 (report, (Path(out) / "lean.log").read_text()))


if __name__ == "__main__":
    unittest.main()
