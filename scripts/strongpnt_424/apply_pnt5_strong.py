#!/usr/bin/env python3
"""Port StrongPNT-specific PNT5 proof syntax to Mathlib 4.24.

This layer deliberately preserves the strong zero-free profile.  It only makes
coercions explicit and applies API/tactic repairs that are independent of the
logarithmic exponent used in the zero-free boundary.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STRONGPNT_ROOT = ROOT / ".lake" / "packages" / "StrongPNT"
TARGET = STRONGPNT_ROOT / "StrongPNT" / "PNT5_Strong.lean"
WARNING_POLICY_FILES = (
    STRONGPNT_ROOT / "StrongPNT.lean",
    STRONGPNT_ROOT / "StrongPNT" / "PNT1_ComplexAnalysis.lean",
    STRONGPNT_ROOT / "StrongPNT" / "PNT2_LogDerivative.lean",
    STRONGPNT_ROOT / "StrongPNT" / "PNT3_RiemannZeta.lean",
    STRONGPNT_ROOT / "StrongPNT" / "Z0.lean",
    STRONGPNT_ROOT / "StrongPNT" / "PNT4_ZeroFreeRegion.lean",
    STRONGPNT_ROOT / "StrongPNT" / "ZetaZeroFree.lean",
    TARGET,
)


def replace_exact(label: str, old: str, new: str) -> None:
    text = TARGET.read_text()
    old_count = text.count(old)
    new_count = text.count(new)
    if old_count == 1:
        TARGET.write_text(text.replace(old, new, 1))
        print(f"applied PNT5_Strong.lean: {label}")
    elif old_count == 0 and new_count == 1:
        print(f"already applied PNT5_Strong.lean: {label}")
    else:
        raise SystemExit(
            f"compatibility patch mismatch for {label!r}: "
            f"old_count={old_count}, new_count={new_count}"
        )


def replace_all_exact(label: str, old: str, new: str, expected: int) -> None:
    text = TARGET.read_text()
    old_count = text.count(old)
    if old_count == expected:
        TARGET.write_text(text.replace(old, new))
        print(f"applied PNT5_Strong.lean: {label} ({expected} occurrences)")
    elif old_count == 0 and text.count(new) >= expected:
        print(f"already applied PNT5_Strong.lean: {label}")
    else:
        raise SystemExit(
            f"compatibility patch mismatch for {label!r}: "
            f"old_count={old_count}, expected={expected}, new_count={text.count(new)}"
        )


def keep_external_warnings_nonfatal(path: Path) -> None:
    """Keep RHLean's --wfail policy from being inherited by vendored StrongPNT."""
    directive = "set_option warningAsError false\n"
    text = path.read_text()
    if directive in text:
        print(f"already applied {path.name}: external warning policy")
        return

    lines = text.splitlines(keepends=True)
    import_lines = [i for i, line in enumerate(lines) if line.startswith("import ")]
    if not import_lines:
        raise SystemExit(f"no import boundary found in {path}")

    insert_at = max(import_lines) + 1
    lines.insert(insert_at, "\n" + directive)
    path.write_text("".join(lines))
    print(f"applied {path.name}: external warning policy")


def main() -> None:
    # Lean 4.24 cannot infer the codomain of these Mellin transforms through a
    # surrounding complex expression.  The casts are annotations only.
    replace_all_exact(
        "make remaining SmoothingF Mellin casts explicitly complex",
        "𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x))",
        "𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))",
        24,
    )
    replace_all_exact(
        "make uncast SmoothingF Mellin terms explicitly complex",
        "𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))",
        "𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))",
        2,
    )
    replace_all_exact(
        "make terminal smoothing Mellin terms explicitly complex",
        "𝓜 (fun x ↦ (Smooth1 ν ε x))",
        "𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ))",
        7,
    )
    replace_all_exact(
        "make terminal section-notation Mellin terms explicitly complex",
        "𝓜 ((Smooth1 ν ε) ·)",
        "𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ))",
        2,
    )

    # Lean 4.24 no longer treats an unnamed local `have (x)` as the named
    # rewrite theorem expected by the following `simp_rw`/`rw`.  This is the
    # syntax used by the already-ported 4.24 MediumPNT source.
    replace_all_exact(
        "name terminal pointwise algebra helpers",
        "    have (x) :",
        "    have this (x) :",
        4,
    )

    # `logt_gt_one` now takes a non-strict lower bound at the call sites.
    replace_exact(
        "use non-strict input for logt_gt_one in I3",
        """  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1
""",
        """  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1.le
""",
    )
    replace_exact(
        "use non-strict input for pointwise logt_gt_one",
        "        exact logt_gt_one ht_gt3\n",
        "        exact logt_gt_one ht_gt3.le\n",
    )

    # The denominator comparison in I2 is unchanged mathematically; only the
    # 4.24 monotonicity lemma and goal scoping changed.
    replace_exact(
        "port I2 denominator comparison API",
        """        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_left]
          exact this
          exact ε_pos
          positivity
          apply mul_pos ε_pos
          exact lt_of_lt_of_le (pow_pos Tpos 2) this
          positivity
""",
        """        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          · exact this
          · exact ε_pos
          · positivity
          · apply mul_pos ε_pos
            exact lt_of_lt_of_le (pow_pos Tpos 2) this
          · positivity
""",
    )
    replace_exact(
        "remove redundant ring after I2 field_simp",
        """        _ = C' * X / (ε * T) := by
          field_simp
          ring
""",
        """        _ = C' * X / (ε * T) := by
          field_simp
""",
    )

    # I3: 4.24 exposes simpler residual real-arithmetic goals after the same
    # analytic estimates have already been established.
    replace_exact(
        "discharge I3 negative-interval integrand nonnegativity directly",
        """        · field_simp
          apply div_nonneg
          · linarith
          · apply mul_nonneg
            · linarith
            · rw [Complex.sq_norm]
              exact normSq_nonneg (↑σ₁ + ↑t * I)
""",
        """        · positivity
""",
    )
    replace_exact(
        "finish I3 reciprocal rpow identity by commutativity",
        """    field_simp
    rw[mul_assoc, h₁]
    ring
""",
        """    field_simp
    simpa [mul_comm, neg_div] using h₁.symm
""",
    )
    replace_exact(
        "close normalized I3 terminal arithmetic goal",
        """  apply le_trans this
  ring_nf
  field_simp
""",
        """  apply le_trans this
  ring_nf
  field_simp
  norm_num
""",
    )

    # The repository intentionally enforces --wfail on RHLean itself while
    # treating the pinned external theorem package as an independently audited
    # boundary.  Lake propagates --wfail to dependency modules, so reset only
    # that option inside the StrongPNT sources.  Warnings remain visible; they
    # simply do not become failures of the RHLean target.
    for path in WARNING_POLICY_FILES:
        keep_external_warnings_nonfatal(path)


if __name__ == "__main__":
    main()
