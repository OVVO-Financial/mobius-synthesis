#!/usr/bin/env python3
"""Apply the next StrongPNT PNT5 compatibility layer for Mathlib 4.24.

The replacements are taken from the already-ported PrimeNumberTheoremAnd MediumPNT
source at the pinned 4.24-compatible commit. Markers are exact and fail closed.

Only declarations whose theorem statements are identical after whitespace normalization
are transplanted from MediumPNT. The strong zero-free-profile declarations, whose
statements differ from MediumPNT's weaker log-power profile, are deliberately excluded.
"""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / ".lake" / "packages" / "StrongPNT" / "StrongPNT" / "PNT5_Strong.lean"
ORACLE = (
    ROOT
    / ".lake"
    / "packages"
    / "PrimeNumberTheoremAnd"
    / "PrimeNumberTheoremAnd"
    / "MediumPNT.lean"
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


def replace_between(label: str, start: str, end: str, replacement: str) -> None:
    text = TARGET.read_text()
    start_count = text.count(start)
    end_count = text.count(end)
    if start_count == 1 and end_count == 1:
        i = text.index(start)
        j = text.index(end, i)
        TARGET.write_text(text[:i] + replacement + text[j:])
        print(f"applied PNT5_Strong.lean: {label}")
    elif start_count == 0 and end_count == 1 and replacement in text:
        print(f"already applied PNT5_Strong.lean: {label}")
    else:
        raise SystemExit(
            f"compatibility range mismatch for {label!r}: "
            f"start_count={start_count}, end_count={end_count}"
        )


def remove_between(label: str, start: str, end: str) -> None:
    text = TARGET.read_text()
    start_count = text.count(start)
    end_count = text.count(end)
    if start_count == 1 and end_count == 1:
        i = text.index(start)
        j = text.index(end, i)
        TARGET.write_text(text[:i] + text[j:])
        print(f"removed PNT5_Strong.lean: {label}")
    elif start_count == 0 and end_count == 1:
        print(f"already removed PNT5_Strong.lean: {label}")
    else:
        raise SystemExit(
            f"compatibility range mismatch for {label!r}: "
            f"start_count={start_count}, end_count={end_count}"
        )


def _declaration_span(text: str, name: str, next_name: str) -> tuple[int, int]:
    start_re = re.compile(rf"(?m)^(?:theorem|lemma)\s+{re.escape(name)}\b")
    end_re = re.compile(rf"(?m)^(?:theorem|lemma)\s+{re.escape(next_name)}\b")
    start_matches = list(start_re.finditer(text))
    end_matches = list(end_re.finditer(text))
    if len(start_matches) != 1 or len(end_matches) != 1:
        raise SystemExit(
            f"oracle block mismatch for {name!r}: "
            f"start_count={len(start_matches)}, end_count={len(end_matches)}"
        )
    i = start_matches[0].start()
    j = end_matches[0].start()
    if not i < j:
        raise SystemExit(f"oracle block order mismatch for {name!r}")
    return i, j


def _canonical_statement(block: str) -> str:
    marker = ":= by"
    if marker not in block:
        raise SystemExit("expected theorem proof marker ':= by' in oracle transplant block")
    statement = block.split(marker, 1)[0]
    return re.sub(r"\s+", "", statement)


def transplant_oracle_proof(name: str, next_name: str) -> None:
    target_text = TARGET.read_text()
    oracle_text = ORACLE.read_text()
    ti, tj = _declaration_span(target_text, name, next_name)
    oi, oj = _declaration_span(oracle_text, name, next_name)
    target_block = target_text[ti:tj]
    oracle_block = oracle_text[oi:oj]

    if _canonical_statement(target_block) != _canonical_statement(oracle_block):
        raise SystemExit(
            f"refusing MediumPNT transplant for {name!r}: theorem statements differ"
        )

    if target_block == oracle_block:
        print(f"already transplanted PNT5_Strong.lean: {name}")
        return

    TARGET.write_text(target_text[:ti] + oracle_block + target_text[tj:])
    print(f"transplanted PNT5_Strong.lean proof from 4.24 MediumPNT: {name}")


def main() -> None:
    replace_between(
        "finite-range splitting and initial smoothing block from 4.24 MediumPNT",
        "  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by\n",
        "  have vonBnd1 :\n",
        """  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans <| Nat.le_ceil X
    exact_mod_cast Nat.ceil_le_floor_add_one X

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := by exact Nat.floor_le (by positivity)

  rw [show ∑ x ∈ Finset.range ⌊X + 1⌋₊, Λ x =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) by
    field_simp
    simp only [add_comm _ n₀]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le]
    dsimp only [n₀]
    exact Nat.ceil_le.mpr (by linarith)]

  rw [show ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl|n_zero := eq_or_ne n 0
    · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      exact Nat.lt_ceil.mp hn |>.le]
""",
    )

    remove_between(
        "helper theorems now supplied by PrimeNumberTheoremAnd.ZetaBounds",
        "theorem summable_complex_then_summable_real_part (f : ℕ → ℂ) :\n",
        "def LogDerivZetaHasBound (A C : ℝ) : Prop :=",
    )

    replace_exact(
        "continuousOn_univ API in Pull1 integrability",
        """  · apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousOn_univ]
    intro t _
""",
        """  · apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
""",
    )

    # These are coercion-only statement repairs. They do not change the
    # mathematical content; Mathlib 4.24 no longer infers the real-to-complex
    # coercion through the Mellin notation at these theorem boundaries.
    replace_exact(
        "make Pull1 residue Mellin term explicitly complex-valued",
        "      + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X := by\n",
        "      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by\n",
    )
    replace_exact(
        "make ZetaBoxEval Mellin term explicitly complex-valued",
        "    ‖𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X - X‖ ≤ C * ε * X := by\n",
        "    ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X - X‖ ≤ C * ε * X := by\n",
    )

    # Reuse only proof bodies whose theorem statements are exactly the same as
    # the pinned, already-compiling 4.24 MediumPNT source. In particular, do
    # not transplant I2/I3/I4/I8 or the terminal theorem: those declarations
    # encode MediumPNT's weaker log^9 zero-free profile rather than StrongPNT's
    # strong log profile.
    transplant_oracle_proof("SmoothedChebyshevClose_aux", "SmoothedChebyshevClose")
    transplant_oracle_proof("SmoothedChebyshevPull1", "interval_membership")
    transplant_oracle_proof("I1Bound", "I9I1")
    transplant_oracle_proof("log_pow_over_xsq_integral_bounded", "I3Bound")
    transplant_oracle_proof("I5Bound", "LogDerivZetaBoundedAndHolo")


if __name__ == "__main__":
    main()
