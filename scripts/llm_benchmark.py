#!/usr/bin/env python3
"""Generate annotations, kernel-check them, and retain the complete denominator."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

from llm_check import check_candidate
from llm_provider import audit_events, propose

ROOT = Path(__file__).resolve().parents[1]
POLICY = "annotation-synthesis-v1"


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def fingerprint() -> dict:
    paths = list((ROOT / "MiniVerify").rglob("*.lean"))
    paths += [ROOT / p for p in ("MiniVerify.lean", "lakefile.lean", "lake-manifest.json",
                               "lean-toolchain", "benchmarks/cases.json", "benchmarks/reference.json")]
    paths += list((ROOT / "scripts").glob("llm_*.py"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def prompt_for(case: dict, previous: dict | None = None, diagnostic: str = "") -> str:
    prompt = """Propose a loop invariant and a strictly decreasing natural-number termination
variant for the fixed program below. Return exactly the JSON object requested by the schema.
Do not use tools, browse, inspect files, or modify the program/precondition/postcondition.
You only know the supplied program. The checker proves universal VCs in Lean 4.

Expression syntax is a restricted Python expression grammar, NOT Lean syntax:
  immutable Nat inputs: n, m
  Nat state fields: s.x, s.y, s.z, s.n, s.m, s.i
  Nat operations: +, -, *, //, % (subtraction saturates at zero)
  comparisons: ==, !=, <, <=, >, >=
  predicates: and, or, not, True, False
No functions, quantifiers, assignments, additional names, negative literals, or code.
All fields initially unspecified in the supplied case are zero.
Return {"invariant": "...", "variant": "...", "solver": "omega" or "nonlinear"}.
The solver chooses a fixed trusted Lean arithmetic proof recipe; it is not executable code.
Choose omega for linear natural-number arithmetic, nonlinear for polynomial relations.
Your invariant must hold initially, be preserved, imply the postcondition on exit, and
make the variant strictly decrease while the guard is true. Inputs may be arbitrarily large.

FIXED CASE:
""" + json.dumps(case, indent=2, sort_keys=True)
    if previous is not None:
        prompt += "\n\nPREVIOUS CANDIDATE (failed):\n" + json.dumps(previous, sort_keys=True)
        prompt += "\nLEAN DIAGNOSTIC:\n" + diagnostic[-10000:]
        prompt += "\nReturn a corrected annotation object; do not change the fixed case."
    return prompt + "\n"


def load_cases() -> list[dict]:
    value = json.loads((ROOT / "benchmarks/cases.json").read_text())
    cases = value["cases"] if isinstance(value, dict) else value
    ids = [c["id"] for c in cases]
    if len(ids) != len(set(ids)) or not cases:
        raise ValueError("Benchmark cases must have unique IDs and a nonempty denominator")
    return cases


def summarize(report: dict) -> None:
    cases = report["cases"]
    denominator = len(cases)
    first = sum(bool(c["attempts"]) and c["attempts"][0]["verified"] for c in cases)
    eventual = sum(any(a["verified"] for a in c["attempts"]) for c in cases)
    report["summary"] = {
        "programs": denominator, "verified_first_attempt": first,
        "verified_within_budget": eventual,
        "success_rate": eventual / denominator,
        "attempts": sum(len(c["attempts"]) for c in cases),
        "model_claim_eligible": report["kind"] == "live_model" and report.get("completed", False),
    }


def run(args) -> int:
    cases = load_cases()
    if args.case:
        cases = [c for c in cases if c["id"] in args.case]
        if len(cases) != len(set(args.case)):
            raise ValueError("Unknown or duplicate case selection")
    output = args.output.resolve()
    if output.exists() and any(output.iterdir()):
        raise ValueError("Output directory is not empty; use a fresh run directory")
    output.mkdir(parents=True, exist_ok=True)
    references = None
    if args.command == "reference":
        references = json.loads((ROOT / "benchmarks/reference.json").read_text())
    report = {
        "schema_version": 1, "policy": POLICY,
        "kind": "reference_control" if references is not None else "live_model",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "model": args.model if references is None else None,
        "reasoning_effort": args.effort if references is None else None,
        "max_attempts": args.max_attempts if references is None else 1,
        "provider_timeout_seconds": args.provider_timeout,
        "lean_timeout_seconds": args.lean_timeout,
        "source_sha256": fingerprint(),
        "selected_case_ids": [c["id"] for c in cases],
        "cases": [{"id": c["id"], "attempts": []} for c in cases],
        "completed": False,
        "method": "Fixed programs/specifications; model annotations only; fixed arithmetic tactics; all selected cases counted.",
    }
    if references is None:
        cli = shutil.which(args.codex)
        report["codex_version"] = subprocess.check_output([cli or args.codex, "--version"], text=True).strip()
    write_json(output / "manifest.json", report)
    summarize(report)
    write_json(output / "report.json", report)
    for case, entry in zip(cases, report["cases"]):
        previous = None
        diagnostic = ""
        for number in range(1, report["max_attempts"] + 1):
            directory = output / case["id"] / f"attempt-{number}"
            directory.mkdir(parents=True)
            if references is not None:
                candidate = references[case["id"]]
                write_json(directory / "response.json", candidate)
                provider = {"status": "reference", "candidate": candidate}
            else:
                provider = propose(prompt_for(case, previous, diagnostic), directory,
                                   args.model, args.provider_timeout, args.codex, args.effort)
                candidate = provider.get("candidate")
            write_json(directory / "provider.json", provider)
            if candidate is None:
                checked = {"verified": False, "status": provider["status"],
                           "error": provider.get("error")}
            else:
                checked = check_candidate(case, candidate, ROOT, directory, args.lean_timeout)
            checked["attempt"] = number
            write_json(directory / "result.json", checked)
            entry["attempts"].append(checked)
            summarize(report)
            write_json(output / "report.json", report)
            print(f"{case['id']} attempt {number}: {checked.get('status')} "
                  f"({'verified' if checked['verified'] else 'failed'})", flush=True)
            if checked["verified"]:
                break
            previous = candidate
            log = directory / "lean.log"
            diagnostic = log.read_text() if log.exists() else str(checked.get("error", checked))
        # Every case remains in the denominator, including invalid or timed-out responses.
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    report["completed"] = True
    summarize(report)
    write_json(output / "report.json", report)
    summary = report["summary"]
    print(f"{report['kind']}: {summary['verified_within_budget']}/{summary['programs']} "
          f"verified; {summary['verified_first_attempt']}/{summary['programs']} first attempt")
    return 0


def replay(args) -> int:
    original = json.loads((args.run / "report.json").read_text())
    if original["source_sha256"] != fingerprint():
        raise ValueError("Source fingerprints changed; replay requires the recorded source revision")
    if args.output.exists() and any(args.output.iterdir()):
        raise ValueError("Replay output directory must be fresh")
    args.output.mkdir(parents=True, exist_ok=True)
    by_id = {c["id"]: c for c in load_cases()}
    ids = [c["id"] for c in original["cases"]]
    if (not original.get("completed") or ids != original["selected_case_ids"]
            or len(ids) != len(set(ids)) or any(i not in by_id for i in ids)):
        raise ValueError("Incomplete or inconsistent recorded case denominator")
    saved_summary = original["summary"].copy()
    summarize(original)
    if saved_summary != original["summary"]:
        raise ValueError("Recorded summary differs from attempt outcomes")
    results = []
    for case in original["cases"]:
        attempts = case["attempts"]
        if (not 1 <= len(attempts) <= original["max_attempts"]
                or [a["attempt"] for a in attempts] != list(range(1, len(attempts) + 1))
                or any(a["verified"] for a in attempts[:-1])):
            raise ValueError("Inconsistent attempt budget or ordering")
        for attempt in case["attempts"]:
            number = attempt["attempt"]
            directory = args.run / case["id"] / f"attempt-{number}"
            provider = json.loads((directory / "provider.json").read_text())
            if "candidate" not in provider:
                if attempt["verified"] or provider["status"] in {"ok", "reference"}:
                    raise ValueError("Verified attempt is missing a successful model candidate")
                results.append({"id": case["id"], "attempt": number,
                                "verified": False, "status": provider["status"]})
                continue
            candidate = json.loads((directory / "response.json").read_text())
            if candidate != provider["candidate"]:
                raise ValueError("Recorded candidate mismatch")
            if original["kind"] == "live_model":
                if provider["status"] != "ok":
                    raise ValueError("Candidate came from an invalid model attempt")
                audited = audit_events((directory / "events.jsonl").read_text())
                if candidate != json.loads(audited["last_message"]):
                    raise ValueError("Model event differs from recorded candidate")
            result = check_candidate(by_id[case["id"]], candidate, ROOT,
                                     args.output / case["id"] / f"attempt-{number}",
                                     args.lean_timeout)
            if result["verified"] != attempt["verified"]:
                raise ValueError(f"Replay outcome changed for {case['id']} attempt {number}")
            results.append({"id": case["id"], "attempt": number, **result})
    write_json(args.output / "replay.json", {"matched": True, "attempts": results})
    print(f"Replay matched all {len(results)} recorded attempts; no model calls.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("run", "reference"):
        p = sub.add_parser(name)
        p.add_argument("--output", type=Path, required=True)
        p.add_argument("--model", default=None)
        p.add_argument("--codex", default="codex")
        p.add_argument("--effort", choices=("low", "medium", "high", "xhigh", "max", "ultra"), default="medium")
        p.add_argument("--max-attempts", type=int, choices=range(1, 6), default=2)
        p.add_argument("--provider-timeout", type=float, default=180)
        p.add_argument("--lean-timeout", type=float, default=45)
        p.add_argument("--case", action="append")
    p = sub.add_parser("replay")
    p.add_argument("--run", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean-timeout", type=float, default=45)
    args = parser.parse_args()
    if args.command == "run" and args.model is None:
        parser.error("run requires --model to record explicit model provenance")
    try:
        return replay(args) if args.command == "replay" else run(args)
    except (ValueError, OSError, KeyError, subprocess.SubprocessError) as exc:
        print(f"Benchmark error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
