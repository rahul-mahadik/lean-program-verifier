#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
if ! command -v lake >/dev/null 2>&1; then
  workspace_env="$project_dir/../../work/lean-env/env.sh"
  if [[ -f "$workspace_env" ]]; then
    source "$workspace_env"
  fi
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "Install elan/Lean, then rerun this script." >&2
  exit 2
fi

mkdir -p verification
lake build MiniVerify miniverify MiniVerify.Tests 2>&1 | tee verification/build.log
lake env lean MiniVerify/Audit.lean 2>&1 | tee verification/axioms.txt
.lake/build/bin/miniverify demo | tee verification/demo.txt
python3 scripts/smoke.py
python3 scripts/audit.py
