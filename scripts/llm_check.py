#!/usr/bin/env python3
"""Parse annotation data and check generated VCs without executing model Lean.

The expression language has Nat values, truncated subtraction, Nat division
(`//`), comparisons, and Boolean connectives. It deliberately has no calls,
indexing, binding, imports, or arbitrary Lean escape hatch.
"""

from __future__ import annotations

import ast
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import time
import tokenize
from typing import Any

MAX_EXPRESSION_LENGTH = 4096
MAX_DEPTH = 32
MAX_NODES = 256
MAX_INTEGER_BITS = 256
FIELDS = frozenset({"x", "y", "z", "n", "m", "i"})
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REQUIRED_THEOREMS = (
    "MiniVerify.Generated.candidate_vcs",
    "MiniVerify.Generated.candidate_correct",
)
CASE_NAMES = frozenset({
    "countUp", "countDown", "transfer", "doubleCount", "strideTwo",
    "parityDown", "synchronized", "boundedCopy", "twoPhase", "multiply",
    "triangular", "square",
})


class CandidateError(ValueError):
    """The candidate is outside the restricted data language."""


def _parse(text: str) -> ast.AST:
    if type(text) is not str or not text.strip():
        raise CandidateError("expression must be a nonempty string")
    if len(text) > MAX_EXPRESSION_LENGTH:
        raise CandidateError("expression exceeds length limit")
    if not text.isascii():
        raise CandidateError("expression must use ASCII syntax")
    try:
        nesting = 0
        for token in tokenize.generate_tokens(io.StringIO(text).readline):
            if token.type == tokenize.COMMENT:
                raise CandidateError("comments are not supported")
            if token.type == tokenize.OP and token.string in "([{":
                nesting += 1
                if nesting > MAX_DEPTH:
                    raise CandidateError("expression exceeds nesting limit")
            elif token.type == tokenize.OP and token.string in ")]}":
                nesting -= 1
        tree = ast.parse(text.strip(), mode="eval")
    except (SyntaxError, tokenize.TokenError, IndentationError, RecursionError) as exc:
        raise CandidateError("invalid expression syntax") from exc
    count = 0
    pending = [(tree, 0)]
    while pending:
        node, depth = pending.pop()
        count += 1
        if count > MAX_NODES:
            raise CandidateError("expression exceeds node limit")
        if depth > MAX_DEPTH:
            raise CandidateError("expression exceeds AST depth limit")
        pending.extend((child, depth + 1) for child in ast.iter_child_nodes(node))
    return tree.body


def _render(node: ast.AST) -> tuple[str, str]:
    if isinstance(node, ast.Constant):
        if type(node.value) is bool:
            return ("True" if node.value else "False"), "bool"
        if type(node.value) is int and node.value >= 0:
            if node.value.bit_length() > MAX_INTEGER_BITS:
                raise CandidateError("integer exceeds size limit")
            return str(node.value), "nat"
        raise CandidateError("only Nat numerals and Boolean literals are supported")
    if isinstance(node, ast.Name):
        if node.id in {"n", "m"}:
            return node.id, "nat"
        raise CandidateError("only immutable inputs n and m are bare names")
    if isinstance(node, ast.Attribute):
        if (isinstance(node.value, ast.Name) and node.value.id == "s"
                and node.attr in FIELDS and isinstance(node.ctx, ast.Load)):
            return "s." + node.attr, "nat"
        raise CandidateError("only whitelisted s.field attributes are supported")
    if isinstance(node, ast.BinOp):
        operators = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
                     ast.FloorDiv: "/", ast.Mod: "%"}
        op = operators.get(type(node.op))
        if op is None:
            raise CandidateError("unsupported arithmetic operator")
        left, lt = _render(node.left)
        right, rt = _render(node.right)
        if lt != "nat" or rt != "nat":
            raise CandidateError("arithmetic operands must be Nat expressions")
        return f"({left} {op} {right})", "nat"
    if isinstance(node, ast.Compare):
        operators = {ast.Eq: "=", ast.NotEq: "≠", ast.Lt: "<", ast.LtE: "≤",
                     ast.Gt: ">", ast.GtE: "≥"}
        values = [_render(node.left)] + [_render(x) for x in node.comparators]
        if any(kind != "nat" for _, kind in values):
            raise CandidateError("comparison operands must be Nat expressions")
        clauses = []
        for i, op in enumerate(node.ops):
            symbol = operators.get(type(op))
            if symbol is None:
                raise CandidateError("unsupported comparison operator")
            clauses.append(f"({values[i][0]} {symbol} {values[i + 1][0]})")
        return "(" + " ∧ ".join(clauses) + ")", "bool"
    if isinstance(node, ast.BoolOp):
        op = {ast.And: "∧", ast.Or: "∨"}.get(type(node.op))
        values = [_render(x) for x in node.values]
        if op is None or any(kind != "bool" for _, kind in values):
            raise CandidateError("Boolean operands must be propositions")
        return "(" + f" {op} ".join(value for value, _ in values) + ")", "bool"
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        value, kind = _render(node.operand)
        if kind != "bool":
            raise CandidateError("not requires a proposition")
        return f"(¬ {value})", "bool"
    raise CandidateError(f"unsupported syntax: {type(node).__name__}")


def parse_expression(text: str, expected: str) -> str:
    """Return Lean generated solely from a type-checked, restricted AST."""
    if expected not in {"nat", "bool"}:
        raise ValueError("expected must be nat or bool")
    rendered, kind = _render(_parse(text))
    if kind != expected:
        raise CandidateError(f"expected a {expected} expression")
    return f"({rendered})"


def validate_candidate(candidate: dict[str, Any]) -> dict[str, str]:
    if type(candidate) is not dict:
        raise CandidateError("candidate must be a JSON object")
    if set(candidate) != {"invariant", "variant", "solver"}:
        raise CandidateError("candidate keys must be invariant, variant, solver")
    if any(type(candidate[k]) is not str for k in candidate):
        raise CandidateError("all candidate fields must be strings")
    if candidate["solver"] not in {"omega", "nonlinear"}:
        raise CandidateError("solver must be omega or nonlinear")
    return {
        "invariant": parse_expression(candidate["invariant"], "bool"),
        "variant": parse_expression(candidate["variant"], "nat"),
        "solver": candidate["solver"],
    }


def _case_name(case: dict[str, Any]) -> str:
    if type(case) is not dict or type(case.get("lean_name")) is not str:
        raise CandidateError("trusted case requires a lean_name string")
    name = case["lean_name"]
    if name.startswith("MiniVerify.Benchmarks."):
        name = name.removeprefix("MiniVerify.Benchmarks.")
    if name not in CASE_NAMES:
        raise CandidateError("case is not in the frozen benchmark catalog")
    return name


def render_candidate(case: dict[str, Any], candidate: dict[str, Any]) -> str:
    """Create a complete Lean check using two fixed, trusted proof recipes."""
    name = _case_name(case)
    parsed = validate_candidate(candidate)
    # This string is trusted code. No model-supplied tactic text is inserted.
    solve = "first | omega | nlinarith" if parsed["solver"] == "nonlinear" else "omega"
    simplifications = f"candidateInvariant, candidateVariant, {name}, Nat.add_mul, Nat.mul_add"
    recipe = f"""    all_goals (try simp_all [{simplifications}])
    all_goals (try split_ifs at *)
    all_goals (try simp_all [{simplifications}])
    all_goals (repeat' apply And.intro)
    all_goals {solve}"""
    return f"""import MiniVerify.Benchmarks

set_option linter.unusedVariables false

namespace MiniVerify.Generated
open MiniVerify MiniVerify.Benchmarks

def candidateInvariant (n m : Nat) (s : State) : Prop := {parsed['invariant']}
def candidateVariant (n m : Nat) (s : State) : Nat := {parsed['variant']}

theorem candidate_vcs (n m : Nat) (hp : {name}.pre n m) :
    vcgen ({name}.program n m (candidateInvariant n m) (candidateVariant n m))
      ({name}.post n m) ({name}.initial n m) := by
  apply Case.verify {name} n m (candidateInvariant n m) (candidateVariant n m)
  ·
{recipe}
  · intro s hs hg
{recipe}
  · intro s hs hg
{recipe}

theorem candidate_correct (n m : Nat) (hp : {name}.pre n m) :
    (∃ t bound, {name}.post n m t ∧ ∀ fuel, bound ≤ fuel →
      run fuel ({name}.program n m (candidateInvariant n m) (candidateVariant n m))
        ({name}.initial n m) = .done t) ∧
    (∀ fuel, run fuel ({name}.program n m (candidateInvariant n m) (candidateVariant n m))
      ({name}.initial n m) ≠ .fault) :=
  Case.executable_correct {name} n m (candidateInvariant n m) (candidateVariant n m)
    (candidate_vcs n m hp)

end MiniVerify.Generated

#print axioms MiniVerify.Generated.candidate_vcs
#print axioms MiniVerify.Generated.candidate_correct
"""


def parse_axioms(log: str) -> tuple[dict[str, list[str]], list[str]]:
    found: dict[str, list[str]] = {}
    errors = []
    pattern = r"'([^']+)' depends on axioms: \[([^\]]*)\]"
    for name, raw in re.findall(pattern, log, re.S):
        if name in found:
            errors.append(f"duplicate axiom report for {name}")
        found[name] = [x.strip() for x in raw.split(",") if x.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        if name in found:
            errors.append(f"duplicate axiom report for {name}")
        found[name] = []
    for name in REQUIRED_THEOREMS:
        if name not in found:
            errors.append(f"missing axiom report for {name}")
        elif set(found[name]) - ALLOWED_AXIOMS:
            errors.append(f"unexpected axioms for {name}: {found[name]}")
    return found, errors


def _run_lean(root: Path, source: Path, timeout: float) -> tuple[int | None, str, bool]:
    """Run without a shell; kill the complete process group on timeout."""
    try:
        argument = str(source.relative_to(root))
    except ValueError:
        argument = str(source)
    with subprocess.Popen(
        ["lake", "env", "lean", argument], cwd=root,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, encoding="utf-8", errors="replace", start_new_session=True,
    ) as process:
        try:
            output, _ = process.communicate(timeout=timeout)
            return process.returncode, output, False
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            output, _ = process.communicate()
            return process.returncode, output, True


def check_candidate(case: dict[str, Any], candidate: dict[str, Any], root: Path,
                    out_dir: Path, timeout: float = 30.0) -> dict[str, Any]:
    """Check one candidate and always save candidate.lean plus lean.log."""
    started = time.monotonic()
    root, out_dir = Path(root).resolve(), Path(out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    source_path, log_path = out_dir / "candidate.lean", out_dir / "lean.log"
    def display_path(path: Path) -> str:
        try:
            return str(path.relative_to(root))
        except ValueError:
            return str(path)

    report: dict[str, Any] = {
        "success": False, "verified": False, "status": "invalid", "exit_code": None,
        "timed_out": False, "error": None, "axioms": {},
        "required_theorems": list(REQUIRED_THEOREMS),
        "source_path": display_path(source_path), "log_path": display_path(log_path),
    }
    source = "-- Candidate rejected before Lean execution.\n"
    output = ""
    try:
        source = render_candidate(case, candidate)
        if (type(timeout) not in {int, float} or not math.isfinite(timeout)
                or not 0 < timeout <= 3600):
            raise CandidateError("timeout must be finite and in (0, 3600]")
        source_path.write_text(source)
        code, output, timed_out = _run_lean(root, source_path, timeout)
        report.update(exit_code=code, timed_out=timed_out)
        axioms, errors = parse_axioms(output)
        report["axioms"] = axioms
        if timed_out:
            report.update(status="timeout", error="Lean check exceeded timeout")
        elif code != 0:
            report.update(status="rejected", error="Lean rejected the generated proof")
        elif errors:
            report.update(status="rejected", error="; ".join(errors))
        else:
            report.update(success=True, verified=True, status="accepted")
    except CandidateError as exc:
        report["error"] = str(exc)
        output = "Candidate validation failed: " + str(exc) + "\n"
    except OSError as exc:
        report.update(status="error", error=str(exc))
        output += "Lean invocation failed: " + str(exc) + "\n"
    finally:
        source_path.write_text(source)
        log_path.write_text(output)
        report["source_sha256"] = hashlib.sha256(source.encode()).hexdigest()
        report["duration_seconds"] = time.monotonic() - started
    return report


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-json", type=Path, required=True)
    parser.add_argument("--candidate-json", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--timeout", type=float, default=30.0)
    args = parser.parse_args()
    report = check_candidate(
        json.loads(args.case_json.read_text()), json.loads(args.candidate_json.read_text()),
        args.root, args.out_dir, args.timeout,
    )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["success"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
