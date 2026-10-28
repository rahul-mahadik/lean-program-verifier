#!/usr/bin/env python3
"""Audit the kernel reports and fingerprint every shipped Lean source."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "MiniVerify.vcgen_sound",
    "MiniVerify.totalCorrect_of_vcs",
    "MiniVerify.Exec.deterministic",
    "MiniVerify.Exec.run_result",
    "MiniVerify.Exec.run_complete",
    "MiniVerify.run_sound",
    "MiniVerify.verified_execution",
    "MiniVerify.Language.verified_program",
    "MiniVerify.Language.absoluteValue_verified",
    "MiniVerify.Examples.BinarySearch.verification_conditions",
    "MiniVerify.Examples.BinarySearch.sortedCheck_correct",
    "MiniVerify.Examples.BinarySearch.executable_correct",
    "MiniVerify.Examples.Reverse.verification_conditions",
    "MiniVerify.Examples.Reverse.executable_correct",
    "MiniVerify.Examples.InsertionSort.vcs",
    "MiniVerify.Examples.InsertionSort.executable_correct",
}


def executable_text(source: str) -> str:
    """Remove nested Lean comments and strings while preserving lines."""
    result: list[str] = []
    i, depth, in_string = 0, 0, False
    while i < len(source):
        pair, char = source[i:i + 2], source[i]
        if depth:
            if pair in {"/-", "-/"}:
                depth += 1 if pair == "/-" else -1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif in_string:
            if char == "\\" and i + 1 < len(source):
                result.extend("  ")
                i += 2
            else:
                if char == '"':
                    in_string = False
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            result.extend(" " * (end - i))
            i = end
        elif char == '"':
            in_string = True
            result.append(" ")
            i += 1
        else:
            result.append(char)
            i += 1
    if depth or in_string:
        raise ValueError("Unterminated comment or string")
    return "".join(result)


def main() -> int:
    problems: list[str] = []
    sources = sorted((ROOT / "MiniVerify").rglob("*.lean"))
    sources += [ROOT / name for name in ("MiniVerify.lean", "Main.lean", "lakefile.lean")]
    forbidden = re.compile(
        r"\b(?:sorry|admit|sorryAx|axiom|unsafe|native_decide|ofReduceBool|implemented_by|extern)\b"
    )
    fingerprints = {}
    for path in sources:
        code = executable_text(path.read_text())
        fingerprints[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        for match in forbidden.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            problems.append(f"{path.relative_to(ROOT)}:{line}: {match.group()}")

    report_path = ROOT / "verification/axioms.txt"
    report = report_path.read_text() if report_path.exists() else ""
    found: dict[str, list[str]] = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", report, re.S):
        axioms = [a.strip() for a in raw.split(",") if a.strip()]
        found[name] = axioms
        extras = set(axioms) - ALLOWED_AXIOMS
        if extras:
            problems.append(f"{name}: unexpected axioms {sorted(extras)}")
    for name in re.findall(r"'([^']+)' does not depend on any axioms", report):
        found[name] = []
    for name in sorted(EXPECTED - found.keys()):
        problems.append(f"Missing kernel report: {name}")
    for name in ("build.log", "demo.txt"):
        if not (ROOT / "verification" / name).is_file():
            problems.append(f"Missing verification/{name}")
    tests = executable_text((ROOT / "MiniVerify/Tests.lean").read_text())
    result = {
        "passed": not problems,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "source_files_scanned": len(sources),
        "exact_regressions": len(re.findall(r"\bexample\b", tests)),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "theorems": found,
        "source_sha256": fingerprints,
        "problems": problems,
    }
    (ROOT / "verification/audit.json").write_text(json.dumps(result, indent=2) + "\n")
    if problems:
        print("Audit FAILED:", *problems, sep="\n  ", file=sys.stderr)
        return 1
    print(f"Audit passed: {len(sources)} Lean files, {len(found)} theorem closures, "
          f"{result['exact_regressions']} exact regressions; only standard axioms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
