#!/usr/bin/env python3
"""Native CLI regressions; algorithm proofs are checked separately by Lean."""

import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
binary = root / ".lake/build/bin/miniverify"
cases = [
    (["reverse"], 0, "reverse: #[]"),
    (["reverse", "1", "-2", "3"], 0, "reverse: #[3, -2, 1]"),
    (["sort"], 0, "insertion sort: #[]"),
    (["sort", "5", "2", "4", "2", "-1"], 0, "insertion sort: #[-1, 2, 2, 4, 5]"),
    (["search", "3", "1", "3", "3", "8"], 0, "search 3: some 1"),
    (["search", "2"], 0, "search 2: none"),
    (["search", "3", "8", "1"], 1, "input must be sorted"),
    (["sort", "invalid"], 1, "invalid integer"),
    (["unknown"], 1, "Usage:"),
]
results = []
for args, expected_code, expected_text in cases:
    completed = subprocess.run([str(binary), *args], text=True, capture_output=True, timeout=30)
    output = completed.stdout + completed.stderr
    passed = completed.returncode == expected_code and expected_text in output
    results.append({"args": args, "exit_code": completed.returncode,
                    "output": output.strip(), "passed": passed})
(root / "verification/cli-tests.json").write_text(json.dumps(results, indent=2) + "\n")
assert all(row["passed"] for row in results), results
print(f"Native CLI smoke checks passed: {len(results)} cases.")
