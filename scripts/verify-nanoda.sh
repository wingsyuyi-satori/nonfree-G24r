#!/usr/bin/env bash
# Independently recheck the selected theorem(s) and their complete transitive proof dependencies.
# Usage: scripts/verify-nanoda.sh Solution Fully.Qualified.Theorem [Other.Theorem ...]
set -euo pipefail
cd "$(dirname "$0")/.."
source ./env.sh
module="${1:?supply module name, for example Solution}"; shift
[ "$#" -gt 0 ] || { echo 'Supply at least one theorem name' >&2; exit 1; }
exporter="${LEAN4EXPORT_BIN:-$PWD/tools/lean4export/.lake/build/bin/lean4export}"
nanoda="${NANODA_BIN:-$PWD/tools/nanoda/target/release/nanoda_bin}"
[ -x "$exporter" ] && [ -x "$nanoda" ] || { echo 'Build the pinned lean4export and nanoda first' >&2; exit 1; }
mkdir -p logs
lake build "$module"
lake env "$exporter" "$module" -- "$@" > logs/proofs.ndjson
python3 - <<'PY'
import json, pathlib
root=pathlib.Path.cwd()
config={
 'export_file_path': 'logs/proofs.ndjson',
 'use_stdin': False,
 'permitted_axioms': ['propext','Quot.sound','Classical.choice'],
 'unpermitted_axiom_hard_error': True,
 'nat_extension': True,
 'string_extension': True,
 'print_success_message': True,
 'print_axioms': False
}
(root/'logs/nanoda-config.json').write_bytes((json.dumps(config,indent=2)+'\n').encode('utf-8'))
PY
"$nanoda" logs/nanoda-config.json 2>&1 | tee logs/nanoda.log
printf '%s\n' "$@" > logs/nanoda-theorems.txt
printf 'PASS: independent nanoda rechecked the selected declarations.\n'
