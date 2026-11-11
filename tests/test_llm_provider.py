"""Provider and denominator regressions, using local fake CLIs only.

These tests never call a model or Lean. They test the boundary that decides
whether an annotation can be attributed to a fresh, tool-free model attempt.
"""

from __future__ import annotations

from contextlib import ExitStack
import importlib
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
provider = importlib.import_module("llm_provider")
benchmark = importlib.import_module("llm_benchmark")

CANDIDATE = {"invariant": "s.x <= n", "variant": "n - s.x", "solver": "omega"}
USAGE = {"input_tokens": 100, "output_tokens": 25, "cached_input_tokens": 0}


def events(candidate=CANDIDATE, extra=()) -> list[dict]:
    return [
        {"type": "thread.started", "thread_id": "fixture-thread"},
        {"type": "turn.started"},
        *extra,
        {"type": "item.completed", "item": {
            "id": "final", "type": "agent_message", "text": json.dumps(candidate)}},
        {"type": "turn.completed", "usage": USAGE},
    ]


def jsonl(items) -> str:
    return "".join(json.dumps(item) + "\n" for item in items)


class AuditEventsTests(unittest.TestCase):
    def test_accepts_completed_response_with_usage(self):
        result = provider.audit_events(jsonl(events()))
        self.assertEqual(result["tool_items"], 0)
        self.assertEqual(result["usage"], USAGE)
        self.assertEqual(json.loads(result["last_message"]), CANDIDATE)

    def test_accepts_reasoning_summary_items(self):
        extra = [{"type": "item.completed", "item": {
            "id": "reason", "type": "reasoning", "text": "A short summary."}}]
        self.assertEqual(provider.audit_events(jsonl(events(extra=extra)))["tool_items"], 0)

    def test_rejects_every_tool_kind_in_every_item_phase(self):
        tools = ("command_execution", "file_change", "mcp_tool_call", "web_search",
                 "todo_list", "plan", "collab_tool_call", "future_unknown_tool")
        for tool in tools:
            for phase in ("started", "updated", "completed"):
                with self.subTest(tool=tool, phase=phase):
                    item = {"type": f"item.{phase}", "item": {"id": "tool", "type": tool}}
                    with self.assertRaises(ValueError):
                        provider.audit_events(jsonl(events(extra=[item])))

    def test_rejects_failed_and_unknown_events(self):
        for kind in ("error", "turn.failed", "unknown.event"):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                provider.audit_events(jsonl(events(extra=[{"type": kind}])))

    def test_rejects_empty_or_truncated_streams(self):
        for stream in ("", jsonl(events()[:-1]), jsonl(events()[:2]), "not json\n"):
            with self.subTest(stream=stream), self.assertRaises(ValueError):
                provider.audit_events(stream)

    def test_rejects_missing_message_or_duplicate_completion(self):
        no_message = [events()[0], events()[1], events()[-1]]
        duplicated = events() + [events()[-1]]
        after_completion = events() + [{"type": "turn.started"}]
        for stream in (no_message, duplicated, after_completion):
            with self.subTest(stream=stream), self.assertRaises(ValueError):
                provider.audit_events(jsonl(stream))

    def test_requires_one_thread_and_one_started_turn(self):
        streams = [events()[1:], [events()[0], *events()[2:]],
                   [events()[0], events()[0], *events()[1:]],
                   [events()[0], events()[1], events()[1], *events()[2:]]]
        for stream in streams:
            with self.subTest(stream=stream), self.assertRaises(ValueError):
                provider.audit_events(jsonl(stream))

    def test_malformed_item_shapes_are_value_errors(self):
        for malformed in (None, [], "not an item", 7):
            item = {"type": "item.completed", "item": malformed}
            with self.subTest(item=malformed), self.assertRaises(ValueError):
                provider.audit_events(jsonl(events(extra=[item])))

    def test_agent_messages_require_text_strings(self):
        for value in (None, [], {}, 4):
            stream = events()
            stream[-2]["item"]["text"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                provider.audit_events(jsonl(stream))


class FakeCliTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="miniverify-provider-test-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)

    def fake_cli(self, mode="valid") -> str:
        """An executable fixture implementing only the CLI surface we consume."""
        path = self.base / ("fake-codex-" + mode)
        script = '''#!/usr/bin/env python3
import json
from pathlib import Path
import sys
import time
MODE = __MODE__
CANDIDATE = __CANDIDATE__
USAGE = __USAGE__
args = sys.argv[1:]
if "--version" in args:
    print("fake-codex 1.0")
    raise SystemExit(0)
output = Path(args[args.index("--output-last-message") + 1])
isolated = Path(args[args.index("-C") + 1])
prompt = sys.stdin.read()
observed = {"args": args, "prompt": prompt,
            "cwd_was_empty": not any(isolated.iterdir())}
(output.parent / "observed.json").write_text(json.dumps(observed))
def emit(event):
    print(json.dumps(event), flush=True)
emit({"type": "thread.started", "thread_id": "fake-thread"})
emit({"type": "turn.started"})
if MODE == "timeout":
    time.sleep(2)
if MODE == "tool":
    emit({"type": "item.started", "item": {"id": "tool", "type": "command_execution"}})
if MODE == "malformed":
    emit({"type": "item.completed", "item": None})
if MODE != "missing-output":
    value = dict(CANDIDATE)
    if MODE == "mismatch":
        value["variant"] = "0"
    output.write_text(json.dumps(value))
emit({"type": "item.completed", "item": {
     "id": "final", "type": "agent_message", "text": json.dumps(CANDIDATE)}})
emit({"type": "turn.completed", "usage": USAGE})
if MODE == "nonzero":
    raise SystemExit(17)
'''
        script = script.replace("__MODE__", repr(mode)).replace("__CANDIDATE__", repr(CANDIDATE))
        script = script.replace("__USAGE__", repr(USAGE))
        path.write_text(script)
        path.chmod(0o700)
        return str(path)

    def proposal(self, mode="valid", timeout=5, directory=None):
        return provider.propose("FIXED TEST PROMPT\n", directory or self.base / "attempt",
                                "fixture-model", timeout, self.fake_cli(mode), "medium")

    def test_actual_subprocess_roundtrip_is_isolated_and_logged(self):
        result = self.proposal()
        self.assertEqual(result["status"], "ok")
        self.assertEqual(result["candidate"], CANDIDATE)
        self.assertEqual(result["tool_items"], 0)
        self.assertEqual(result["reasoning_effort"], "medium")
        attempt = self.base / "attempt"
        observed = json.loads((attempt / "observed.json").read_text())
        self.assertTrue(observed["cwd_was_empty"])
        self.assertEqual(observed["prompt"], "FIXED TEST PROMPT\n")
        self.assertEqual((attempt / "prompt.txt").read_text(), observed["prompt"])
        self.assertEqual(json.loads((attempt / "schema.json").read_text()), provider.SCHEMA)
        self.assertEqual(provider.audit_events((attempt / "events.jsonl").read_text())["tool_items"], 0)
        self.assertIn("--ignore-user-config", observed["args"])
        self.assertIn("--ephemeral", observed["args"])
        self.assertIn("--output-schema", observed["args"])
        self.assertEqual(len(result["cli_sha256"]), 64)

    def test_tool_attempt_is_never_returned_as_candidate(self):
        result = self.proposal("tool")
        self.assertEqual(result["status"], "invalid_response")
        self.assertNotIn("candidate", result)

    def test_output_must_equal_final_model_event(self):
        result = self.proposal("mismatch")
        self.assertEqual(result["status"], "invalid_response")
        self.assertNotIn("candidate", result)

    def test_missing_output_is_not_a_candidate(self):
        result = self.proposal("missing-output")
        self.assertEqual(result["status"], "invalid_response")
        self.assertNotIn("candidate", result)

    def test_stale_response_cannot_be_reused(self):
        directory = self.base / "attempt"
        directory.mkdir()
        (directory / "response.json").write_text(json.dumps(CANDIDATE))
        try:
            result = self.proposal("missing-output", directory=directory)
        except ValueError:
            return  # Refusing a nonempty attempt directory is also correct.
        self.assertNotEqual(result["status"], "ok")
        self.assertNotIn("candidate", result)

    def test_nonzero_exit_cannot_become_success(self):
        result = self.proposal("nonzero")
        self.assertEqual(result["status"], "provider_error")
        self.assertNotIn("candidate", result)
        self.assertTrue((self.base / "attempt/events.jsonl").exists())

    def test_timeout_is_retained_with_partial_event_log(self):
        result = self.proposal("timeout", timeout=0.5)
        self.assertEqual(result["status"], "provider_timeout")
        self.assertNotIn("candidate", result)
        self.assertIn("thread.started", (self.base / "attempt/events.jsonl").read_text())

    def test_malformed_event_is_a_failed_attempt_not_an_exception(self):
        result = self.proposal("malformed")
        self.assertEqual(result["status"], "invalid_response")
        self.assertNotIn("candidate", result)


class BenchmarkBookkeepingTests(unittest.TestCase):
    def test_summary_counts_all_programs_including_unattempted_cases(self):
        cases = [{"id": str(i), "attempts": []} for i in range(12)]
        cases[0]["attempts"] = [{"verified": True}]
        cases[1]["attempts"] = [{"verified": False}, {"verified": True}]
        for case in cases[2:11]:
            case["attempts"] = [{"verified": False, "status": "provider_timeout"}]
        report = {"kind": "live_model", "completed": True, "cases": cases}
        benchmark.summarize(report)
        self.assertEqual(report["summary"]["programs"], 12)
        self.assertEqual(report["summary"]["verified_first_attempt"], 1)
        self.assertEqual(report["summary"]["verified_within_budget"], 2)
        self.assertEqual(report["summary"]["attempts"], 12)
        self.assertAlmostEqual(report["summary"]["success_rate"], 2 / 12)
        self.assertTrue(report["summary"]["model_claim_eligible"])

    def test_incomplete_run_is_not_claim_eligible(self):
        report = {"kind": "live_model", "completed": False, "cases": [
            {"id": "unattempted", "attempts": []}]}
        benchmark.summarize(report)
        self.assertFalse(report["summary"]["model_claim_eligible"])
        self.assertEqual(report["summary"]["programs"], 1)
        self.assertEqual(report["summary"]["success_rate"], 0)

    def test_reference_controls_are_never_model_results(self):
        report = {"kind": "reference_control", "cases": [
            {"id": "reference", "attempts": [{"verified": True}]}]}
        benchmark.summarize(report)
        self.assertFalse(report["summary"]["model_claim_eligible"])

    def args(self, output):
        return SimpleNamespace(command="run", case=None, output=output, model="fixture-model",
                               effort="medium", max_attempts=2, provider_timeout=1,
                               lean_timeout=1, codex="fake-codex")

    def test_run_keeps_failures_and_retry_budget_in_denominator(self):
        cases = [{"id": name} for name in ("a", "b", "c")]
        calls = {name: 0 for name in ("a", "b", "c")}
        def fake_propose(prompt, directory, *_args):
            name = directory.parent.name
            calls[name] += 1
            if name == "b":
                return {"status": "provider_timeout", "error": "fixture timeout"}
            candidate = {**CANDIDATE, "variant": "0" if name == "a" and calls[name] == 1 else "n - s.x"}
            return {"status": "ok", "candidate": candidate}
        def fake_check(_case, candidate, *_args):
            return {"verified": candidate["variant"] != "0", "status": "fixture_checked"}
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            stack.enter_context(mock.patch.object(benchmark, "load_cases", return_value=cases))
            stack.enter_context(mock.patch.object(benchmark, "fingerprint", return_value={"fixture": "hash"}))
            stack.enter_context(mock.patch.object(benchmark, "propose", side_effect=fake_propose))
            stack.enter_context(mock.patch.object(benchmark, "check_candidate", side_effect=fake_check))
            stack.enter_context(mock.patch.object(benchmark.shutil, "which", return_value=sys.executable))
            stack.enter_context(mock.patch.object(benchmark.subprocess, "check_output", return_value="fixture codex\n"))
            stack.enter_context(mock.patch("sys.stdout", new=io.StringIO()))
            output = Path(tmp) / "run"
            self.assertEqual(benchmark.run(self.args(output)), 0)
            report = json.loads((output / "report.json").read_text())
        self.assertEqual([c["id"] for c in report["cases"]], ["a", "b", "c"])
        self.assertEqual(calls, {"a": 2, "b": 2, "c": 1})
        self.assertEqual(report["summary"]["programs"], 3)
        self.assertEqual(report["summary"]["attempts"], 5)
        self.assertEqual(report["summary"]["verified_first_attempt"], 1)
        self.assertEqual(report["summary"]["verified_within_budget"], 2)

    def test_interrupted_run_still_declares_full_selected_denominator(self):
        cases = [{"id": name} for name in ("a", "b", "c")]
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            stack.enter_context(mock.patch.object(benchmark, "load_cases", return_value=cases))
            stack.enter_context(mock.patch.object(benchmark, "fingerprint", return_value={"fixture": "hash"}))
            stack.enter_context(mock.patch.object(benchmark, "propose", side_effect=RuntimeError("fixture interruption")))
            stack.enter_context(mock.patch.object(benchmark.shutil, "which", return_value=sys.executable))
            stack.enter_context(mock.patch.object(benchmark.subprocess, "check_output", return_value="fixture codex\n"))
            output = Path(tmp) / "run"
            with self.assertRaises(RuntimeError):
                benchmark.run(self.args(output))
            path = output / "report.json"
            if not path.exists():
                path = output / "manifest.json"
            report = json.loads(path.read_text())
        self.assertEqual([c["id"] for c in report["cases"]], ["a", "b", "c"])

    def make_replay(self, base, with_candidate=True, matching_event=True):
        run = base / "original"
        directory = run / "a/attempt-1"
        directory.mkdir(parents=True)
        report = {"kind": "live_model", "source_sha256": {"fixture": "hash"},
                  "max_attempts": 1, "completed": True, "selected_case_ids": ["a"], "cases": [
                      {"id": "a", "attempts": [{"attempt": 1, "verified": True}]}]}
        benchmark.summarize(report)
        (run / "report.json").write_text(json.dumps(report))
        record = {"status": "ok", "candidate": CANDIDATE} if with_candidate else {"status": "provider_error"}
        (directory / "provider.json").write_text(json.dumps(record))
        (directory / "response.json").write_text(json.dumps(CANDIDATE))
        event_candidate = CANDIDATE if matching_event else {**CANDIDATE, "variant": "0"}
        (directory / "events.jsonl").write_text(jsonl(events(event_candidate)))
        return SimpleNamespace(run=run, output=base / "replayed", lean_timeout=1)

    def test_replay_rejects_missing_candidate_marked_as_verified(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            stack.enter_context(mock.patch.object(benchmark, "load_cases", return_value=[{"id": "a"}]))
            stack.enter_context(mock.patch.object(benchmark, "fingerprint", return_value={"fixture": "hash"}))
            args = self.make_replay(Path(tmp), with_candidate=False)
            with self.assertRaises(ValueError):
                benchmark.replay(args)

    def test_replay_rejects_final_event_candidate_mismatch(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            stack.enter_context(mock.patch.object(benchmark, "load_cases", return_value=[{"id": "a"}]))
            stack.enter_context(mock.patch.object(benchmark, "fingerprint", return_value={"fixture": "hash"}))
            args = self.make_replay(Path(tmp), matching_event=False)
            with self.assertRaises(ValueError):
                benchmark.replay(args)

    def test_valid_replay_rechecks_certificate_without_calling_model(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            stack.enter_context(mock.patch.object(benchmark, "load_cases", return_value=[{"id": "a"}]))
            stack.enter_context(mock.patch.object(benchmark, "fingerprint", return_value={"fixture": "hash"}))
            checker = stack.enter_context(mock.patch.object(benchmark, "check_candidate", return_value={
                "verified": True, "status": "fixture_checked"}))
            proposer = stack.enter_context(mock.patch.object(benchmark, "propose", side_effect=AssertionError(
                "Replay must not call the model")))
            stack.enter_context(mock.patch("sys.stdout", new=io.StringIO()))
            args = self.make_replay(Path(tmp))
            self.assertEqual(benchmark.replay(args), 0)
            self.assertTrue(json.loads((args.output / "replay.json").read_text())["matched"])
            checker.assert_called_once()
            proposer.assert_not_called()

    def test_replay_rejects_changed_kernel_outcome(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            stack.enter_context(mock.patch.object(benchmark, "load_cases", return_value=[{"id": "a"}]))
            stack.enter_context(mock.patch.object(benchmark, "fingerprint", return_value={"fixture": "hash"}))
            stack.enter_context(mock.patch.object(benchmark, "check_candidate", return_value={
                "verified": False, "status": "fixture_rejected"}))
            args = self.make_replay(Path(tmp))
            with self.assertRaises(ValueError):
                benchmark.replay(args)


if __name__ == "__main__":
    unittest.main()
