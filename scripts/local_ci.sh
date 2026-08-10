#!/usr/bin/env bash
set -euo pipefail

# Local mirror of the hosted "Baseline coupling audit" job for this project.
#
# Run this instead of a bare `lake build RHLean --wfail`. A bare build skips
# three things the hosted job does, and each one has produced a green local
# run against a red hosted run:
#
#   * the Mathlib build cache, so a fresh clone silently starts compiling
#     Mathlib from source instead of downloading it;
#   * the source audit, which rejects unfinished proofs and project-local
#     axioms that compile perfectly well;
#   * the axiom gate, which rejects a headline theorem that elaborates but
#     rests on `sorryAx` or has lost its architectural anchors.
#
# The steps below are the same commands, in the same order, as
# .github/workflows/baseline-audit.yml in the published repository.
#
# Usage, from anywhere inside the project:
#
#     bash scripts/local_ci.sh

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

lean_lib='RHLean'
axiom_import='RHLean.Analysis.PrimeSieveQuotientPNTError'
axiom_decl='RHLean.Analysis.primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_reciprocalError'

# The hosted job requires an anchor from each architecture, so that the
# headline statement is a genuine synthesis rather than whatever happened to
# elaborate. Entries are 'label=extended regex'.
anchor_checks=(
  'square-block=squareprefix|squareblock|survivor|lifetime|deathshell|ancestry'
  'prime-wheel=primorial|primewheel|ramanujan|conductor|coconductor'
)

step() { printf '\n==> %s\n' "$1"; }
fail() { printf 'ERROR: %s\n' "$1" >&2; exit 1; }

# Fail on a missing toolchain with the real reason. Otherwise `lake` returning
# 127 is reported below as a cache-download failure, which sends you looking at
# the network instead of at PATH.
command -v lake >/dev/null 2>&1 || fail 'lake is not on PATH.
Install elan (https://github.com/leanprover/elan) and reopen the terminal.
On Windows, use the Git Bash that ships with Git for Windows.'

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT
check_lean="$tmp_dir/baseline_check.lean"
check_log="$tmp_dir/baseline_check.log"

step 'Auditing unfinished proofs and project-local axioms'
bash scripts/audit_assumptions.sh

step 'Restoring the Mathlib build cache'
# CI gets this from lean-action's use-mathlib-cache. Locally nothing supplies
# it, and without it `lake build` compiles Mathlib from source: hours, not
# minutes. Stop rather than start that by accident.
if ! lake exe cache get; then
  fail 'could not restore the Mathlib build cache.
Continuing would compile Mathlib from source, which takes hours.
Restore connectivity to the Mathlib cache and rerun.'
fi

step "Building $lean_lib with warnings fatal"
lake build "$lean_lib" --wfail

step 'Printing the headline theorem and its axioms'
cat > "$check_lean" <<EOF
import $axiom_import

set_option pp.fullNames true in
#print $axiom_decl

#print axioms $axiom_decl
EOF

if ! lake env lean "$check_lean" | tee "$check_log"; then
  fail "$axiom_decl did not elaborate."
fi

step 'Asserting the theorem rests only on the standard Lean axioms'
if grep -q 'sorryAx' "$check_log"; then
  fail "$axiom_decl depends on sorryAx: the proof is unfinished."
fi
if ! grep -qE 'depends on axioms|does not depend on any axioms' "$check_log"; then
  fail 'no axiom report was produced; the declaration did not elaborate.'
fi
echo 'Axiom audit passed.'

if [[ ${#anchor_checks[@]} -gt 0 ]]; then
  step 'Asserting the theorem still carries its architectural anchors'
  for check in "${anchor_checks[@]}"; do
    label="${check%%=*}"
    pattern="${check#*=}"
    found="$(grep -oiE "$pattern" "$check_log" | sort -u || true)"
    if [[ -z "$found" ]]; then
      fail "the printed statement carries no $label anchor."
    fi
    printf '%s anchors found:\n%s\n' "$label" "$found"
  done
  echo 'Coupling audit passed.'
fi

printf '\nLocal CI mirror passed. This project matches what the hosted job runs.\n'
