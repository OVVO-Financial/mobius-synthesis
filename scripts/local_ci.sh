#!/usr/bin/env bash
set -euo pipefail

# Local mirror of the hosted "Baseline coupling audit" job.
# It builds the complete repository, audits unfinished proofs and local axioms,
# checks the cross-track synthesis theorem, checks the native PNT endpoint, and
# checks the four quantitative status theorems:
#
#   * strict low-slope affine-envelope contraction;
#   * quadratic-tail-scale-law -> sqrt(N) Chebyshev bridge;
#   * post-crossing coupled tail -> Riemann hypothesis statement;
#   * fixed square-root endpoint amplification -> Mertens energy criterion.
#
# Usage, from anywhere inside the project:
#
#     bash scripts/local_ci.sh

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

lean_lib='RHLean'

synthesis_import='RHLean.Analysis.PrimeSieveQuotientPNTError'
synthesis_decl='RHLean.Analysis.primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_reciprocalError'

pnt_import='RHLean.Analysis.NativePNTSquarePrefixTransfer'
pnt_decl='RHLean.Analysis.nativePNTSquarePrefixPrimeNumberTheorem'

contraction_import='RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge'
contraction_decl='RHLean.Analysis.nativePNTSquarePrefixLowSlope_affineEnvelope_strictly_tighter'

scale_bridge_import='RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence'
scale_bridge_decl='RHLean.Analysis.nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw'

coupled_tail_import='RHLean.Analysis.SquareRootPostCrossingTail'
coupled_tail_decl='RHLean.Proof.riemannHypothesis_of_postCrossingCoupledTailBounded_18800'

amplification_import='RHLean.Proof.SquareRootAmplificationClosure'
amplification_decl='RHLean.Proof.mertensEnergyBounded_of_squareRootEndpointAmplification'

anchor_checks=(
  'square-block=squareprefix|squareblock|survivor|lifetime|deathshell|ancestry'
  'prime-wheel=primorial|primewheel|ramanujan|conductor|coconductor'
)

step() { printf '\n==> %s\n' "$1"; }
fail() { printf 'ERROR: %s\n' "$1" >&2; exit 1; }

command -v lake >/dev/null 2>&1 || fail 'lake is not on PATH.
Install elan and reopen the terminal before running validation.'

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT
check_lean="$tmp_dir/status_check.lean"

step 'Auditing unfinished proofs and project-local axioms'
bash scripts/audit_assumptions.sh

step 'Restoring the Mathlib build cache'
if ! lake exe cache get; then
  fail 'could not restore the Mathlib build cache. Continuing would compile Mathlib from source.'
fi

step "Building $lean_lib with warnings fatal"
lake build "$lean_lib" --wfail

print_and_audit_axioms() {
  local decl_import="$1" decl="$2" log="$3"

  cat > "$check_lean" <<EOF
import $decl_import

set_option pp.fullNames true in
#print $decl

#print axioms $decl
EOF

  if ! lake env lean "$check_lean" | tee "$log"; then
    fail "$decl did not elaborate."
  fi
  if grep -q 'sorryAx' "$log"; then
    fail "$decl depends on sorryAx: the proof is unfinished."
  fi
  if ! grep -qE 'depends on axioms|does not depend on any axioms' "$log"; then
    fail "no axiom report was produced for $decl."
  fi
}

synthesis_log="$tmp_dir/synthesis.log"
pnt_log="$tmp_dir/pnt.log"
contraction_log="$tmp_dir/contraction.log"
scale_bridge_log="$tmp_dir/scale_bridge.log"
coupled_tail_log="$tmp_dir/coupled_tail.log"
amplification_log="$tmp_dir/amplification.log"

step 'Auditing the cross-track synthesis theorem'
print_and_audit_axioms "$synthesis_import" "$synthesis_decl" "$synthesis_log"

if [[ ${#anchor_checks[@]} -gt 0 ]]; then
  step 'Asserting the synthesis theorem still carries both architectural anchors'
  for check in "${anchor_checks[@]}"; do
    label="${check%%=*}"
    pattern="${check#*=}"
    found="$(grep -oiE "$pattern" "$synthesis_log" | sort -u || true)"
    if [[ -z "$found" ]]; then
      fail "the printed synthesis statement carries no $label anchor."
    fi
    printf '%s anchors found:\n%s\n' "$label" "$found"
  done
fi

step 'Auditing the unconditional native prime-number-theorem endpoint'
print_and_audit_axioms "$pnt_import" "$pnt_decl" "$pnt_log"

step 'Auditing the strict affine-envelope contraction'
print_and_audit_axioms "$contraction_import" "$contraction_decl" "$contraction_log"

step 'Auditing the conditional quadratic-scale square-root bridge'
print_and_audit_axioms "$scale_bridge_import" "$scale_bridge_decl" "$scale_bridge_log"

step 'Auditing the post-crossing coupled-tail route to the Riemann hypothesis statement'
print_and_audit_axioms "$coupled_tail_import" "$coupled_tail_decl" "$coupled_tail_log"

step 'Auditing the fixed square-root endpoint amplification closure'
print_and_audit_axioms "$amplification_import" "$amplification_decl" "$amplification_log"

module_count="$(find RHLean RHLean.lean -type f -name '*.lean' | wc -l | tr -d ' ')"
printf '\nLocal CI mirror passed. All %s modules and all six status declarations elaborated cleanly.\n' "$module_count"
