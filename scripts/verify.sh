#!/usr/bin/env bash
# Build all proof modules and audit the main declarations. No network needed after cache setup.
set -euo pipefail
cd "$(dirname "$0")/.."
source ./env.sh
mkdir -p logs
python3 scripts/check-trust.py | tee logs/source-audit.log
lean --version | tee logs/lean-version.log
lake build Solution 2>&1 | tee logs/build.log
[ -f AxiomAudit.lean ] || { echo 'AxiomAudit.lean is required for the main-theorem axiom audit' >&2; exit 1; }
lake env lean AxiomAudit.lean 2>&1 | tee logs/axioms.log
python3 scripts/check-trust.py --axioms logs/axioms.log --expect "$@" | tee logs/trust-audit.log
