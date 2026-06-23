import Proofs.LawOfCosinesOQ04OQ01

/-
# Law of Cosines — OQ-04-OQ-01: the Angle Bisector Theorem (closing the cevian gap)

## Research Problem: law-of-cosines-oq-04-oq-01

The registered file `LawOfCosinesOQ04OQ01.lean` proves the coordinate-free
Stewart identity and, as a specialization, the internal-bisector length formula
`angle_bisector_length_inner`.  That theorem, however, *assumes* its cevian foot
`D = (1 - s) • B + s • C` already divides `BC` in the ratio `BD : DC = c : b`
(hypothesis `s · (b + c) = c`, with `b = ‖A-C‖`, `c = ‖A-B‖`).  Its own docstring
flags the omission:

> "that this ratio is the one realized by the actual *angle* bisector
>  (equal angles at `A`) is a separate geometric fact, not used or proved here."

This file **proves that separate geometric fact** — the Angle Bisector Theorem —
in the same coordinate-free inner-product setting, and uses it to upgrade the
length formula so it follows from the genuine equal-angle hypothesis.

## Equal angles, cleared of denominators

For the cevian foot `D`, the cosines of the two half-angles at `A` are

    cos ∠BAD = ⟪A-B, A-D⟫ / (‖A-B‖ · ‖A-D‖),
    cos ∠CAD = ⟪A-C, A-D⟫ / (‖A-C‖ · ‖A-D‖).

Equality of the two angles (each in `[0, π]`, where `cos` is injective) is
equivalent — after cancelling the common positive factor `‖A-D‖` — to the
**polynomial** identity

    ‖A-C‖ · ⟪A-B, A-D⟫ = ‖A-B‖ · ⟪A-C, A-D⟫,

which carries no division and is what we take as the equal-angle hypothesis.

## Main results

* `angle_bisector_factor` — the master factorization
    `b·⟪A-B,A-D⟫ − c·⟪A-C,A-D⟫ = (bc − ⟪A-B,A-C⟫)·(c − s(b+c))`.
* `angle_bisector_iff` — the equal-cosine condition holds iff
    `(bc − ⟪A-B,A-C⟫)·(c − s(b+c)) = 0`.
* `angle_bisector_ratio_of_equal_angle` — **Angle Bisector Theorem**: for a
  nondegenerate triangle (`bc ≠ ⟪A-B,A-C⟫`, i.e. strict Cauchy–Schwarz / `A`,`B`,`C`
  not collinear) the equal-angle condition forces the ratio `s·(b+c) = c`,
  i.e. `BD : DC = c : b = AB : AC`.
* `angle_bisector_length_of_equal_angle` — the bisector length formula
  `(b+c)²‖A-D‖² = bc((b+c)² − a²)` now derived from equal angles at `A`, with no
  ad-hoc ratio assumption (combines the Angle Bisector Theorem with the registered
  `angle_bisector_length_inner`).

The factor `bc − ⟪A-B,A-C⟫` is `‖A-C‖‖A-B‖ − ⟪A-B,A-C⟫ ≥ 0` by Cauchy–Schwarz,
vanishing exactly when `A-B` and `A-C` are nonnegatively parallel (degenerate
triangle); `hnd` rules that out.

0 axioms, 0 sorries.

Docker-verified GREEN (7744 jobs) and REGISTERED in `Proofs.lean`. Inner products
use the `RealInnerProductSpace` notation `⟪·, ·⟫` (the field-explicit `inner ℝ`
form under the current Mathlib pin).
-/

namespace StewartsTheoremInner

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Inner product of `A-B` with the cevian direction `A-D`:
    `⟪A-B, A-D⟫ = (1-s)‖A-B‖² + s⟪A-B,A-C⟫`. -/
theorem inner_sub_left_cevian (A B C : V) (s : ℝ) :
    ⟪A - B, A - ((1 - s) • B + s • C)⟫
      = (1 - s) * ‖A - B‖ ^ 2 + s * ⟪A - B, A - C⟫ := by
  have hAD : A - ((1 - s) • B + s • C) = (1 - s) • (A - B) + s • (A - C) := by
    module
  rw [hAD, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]

/-- Inner product of `A-C` with the cevian direction `A-D`:
    `⟪A-C, A-D⟫ = (1-s)⟪A-B,A-C⟫ + s‖A-C‖²`. -/
theorem inner_sub_right_cevian (A B C : V) (s : ℝ) :
    ⟪A - C, A - ((1 - s) • B + s • C)⟫
      = (1 - s) * ⟪A - B, A - C⟫ + s * ‖A - C‖ ^ 2 := by
  have hAD : A - ((1 - s) • B + s • C) = (1 - s) • (A - B) + s • (A - C) := by
    module
  rw [hAD, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm (A - C) (A - B)]

/-- **Master factorization** of the equal-cosine discriminant.  With
`b = ‖A-C‖`, `c = ‖A-B‖`, `p = ⟪A-B,A-C⟫` and the cevian foot
`D = (1-s)•B + s•C`,

    b·⟪A-B,A-D⟫ − c·⟪A-C,A-D⟫ = (b·c − p)·(c − s·(b + c)).

Both inner products are bilinear functions of `s`, and the difference factors
cleanly: the geometric content of the angle bisector lives entirely in the two
factors `b·c − p` (nondegeneracy) and `c − s·(b+c)` (the segment ratio). -/
theorem angle_bisector_factor (A B C : V) (s : ℝ) :
    ‖A - C‖ * ⟪A - B, A - ((1 - s) • B + s • C)⟫
        - ‖A - B‖ * ⟪A - C, A - ((1 - s) • B + s • C)⟫
      = (‖A - C‖ * ‖A - B‖ - ⟪A - B, A - C⟫)
          * (‖A - B‖ - s * (‖A - C‖ + ‖A - B‖)) := by
  rw [inner_sub_left_cevian, inner_sub_right_cevian]
  ring

/-- **Equal-cosine criterion.**  The half-angles at `A` cut off by the cevian
foot `D = (1-s)•B + s•C` have equal cosine (cleared of the common factor `‖A-D‖`)
iff the discriminant `(bc − ⟪A-B,A-C⟫)·(c − s(b+c))` vanishes. -/
theorem angle_bisector_iff (A B C : V) (s : ℝ) :
    ‖A - C‖ * ⟪A - B, A - ((1 - s) • B + s • C)⟫
        = ‖A - B‖ * ⟪A - C, A - ((1 - s) • B + s • C)⟫
      ↔ (‖A - C‖ * ‖A - B‖ - ⟪A - B, A - C⟫)
          * (‖A - B‖ - s * (‖A - C‖ + ‖A - B‖)) = 0 := by
  rw [← angle_bisector_factor, sub_eq_zero]

/-- **Angle Bisector Theorem (coordinate-free).**  In a nondegenerate triangle
(`bc ≠ ⟪A-B,A-C⟫`, i.e. `A`, `B`, `C` not collinear by strict Cauchy–Schwarz),
if the cevian `AD` bisects the angle at `A` — equal cosines, hypothesis `hbis` —
then its foot `D = (1-s)•B + s•C` divides `BC` in the ratio `BD : DC = c : b`:

    s · (‖A-C‖ + ‖A-B‖) = ‖A-B‖,    i.e.    BD : DC = AB : AC.

This is precisely the ratio hypothesis assumed by `angle_bisector_length_inner`. -/
theorem angle_bisector_ratio_of_equal_angle (A B C : V) (s : ℝ)
    (hnd : ‖A - C‖ * ‖A - B‖ ≠ ⟪A - B, A - C⟫)
    (hbis : ‖A - C‖ * ⟪A - B, A - ((1 - s) • B + s • C)⟫
      = ‖A - B‖ * ⟪A - C, A - ((1 - s) • B + s • C)⟫) :
    s * (‖A - C‖ + ‖A - B‖) = ‖A - B‖ := by
  rcases mul_eq_zero.mp ((angle_bisector_iff A B C s).mp hbis) with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hnd
  · exact (sub_eq_zero.mp h0).symm

/-- **Internal-bisector length from genuine equal angles.**  The bisector length
formula `(b+c)²‖A-D‖² = bc((b+c)² − a²)` now follows from the *equal-angle*
hypothesis at `A` (plus nondegeneracy), with no separately-assumed segment ratio:
the Angle Bisector Theorem supplies the ratio, then the registered
`angle_bisector_length_inner` supplies the length. -/
theorem angle_bisector_length_of_equal_angle (A B C : V) (s : ℝ)
    (hnd : ‖A - C‖ * ‖A - B‖ ≠ ⟪A - B, A - C⟫)
    (hbis : ‖A - C‖ * ⟪A - B, A - ((1 - s) • B + s • C)⟫
      = ‖A - B‖ * ⟪A - C, A - ((1 - s) • B + s • C)⟫) :
    (‖A - C‖ + ‖A - B‖) ^ 2 * ‖A - ((1 - s) • B + s • C)‖ ^ 2 =
      ‖A - B‖ * ‖A - C‖ * ((‖A - C‖ + ‖A - B‖) ^ 2 - ‖B - C‖ ^ 2) :=
  angle_bisector_length_inner A B C s
    (angle_bisector_ratio_of_equal_angle A B C s hnd hbis)

end StewartsTheoremInner
