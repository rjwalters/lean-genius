/-
  The Artin–Schreier Obstruction: Totality Is Essential for `sq_nonneg`

  Open Question (sqrt2-examples-oq-01-oq-01):
  "Is `LinearOrderedSemiring` the *minimal* typeclass for `mul_self_nonneg`
   (0 ≤ x²)?  Concretely: can the totality of the order be dropped to a mere
   partial order, or is it essential?  Exhibit a partially-ordered (not totally
   ordered) ordered ring with an element whose square is negative."

  Answer: TOTALITY IS ESSENTIAL.  We pin the obstruction to a single hypothesis.

  Mathlib proves `sq_nonneg` under exactly
      `[Semiring R] [LinearOrder R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]`.
  Its proof (a `le_or_gt 0 a` case split) genuinely uses the `LinearOrder`.  We show
  this `LinearOrder` cannot be weakened to `PartialOrder` by producing an *explicit
  witness*: the complex numbers ℂ with their canonical order (`ComplexOrder`,
  `z ≤ w ↔ w - z` is real and ≥ 0).  This ℂ satisfies **every** other hypothesis of
  `sq_nonneg` — it is a commutative ring carrying `PartialOrder`, `ExistsAddOfLE`,
  `PosMulMono`, and `AddLeftMono` — yet `Complex.I ^ 2 = -1 < 0`.  The single missing
  ingredient is totality of the order, and indeed `I` and `0` are incomparable.

  This is the Artin–Schreier phenomenon: ℂ is not *formally real* (−1 is a square),
  so it admits no order making it a linearly ordered ring.  The parent entry
  (`sqrt2-examples-oq-01`) showed the *positive* direction generalizes freely to any
  linearly ordered ring; this entry shows the *negative* direction — the linearity
  hypothesis is not redundant decoration but the load-bearing assumption.

  Tags: ordered-rings, algebra, artin-schreier, formally-real, counterexample
-/

import Mathlib

open scoped ComplexOrder

namespace Sqrt2OQ01OQ01

/-! ## Part I. The positive result: with a *linear* order, squares are nonnegative.

These are the exact hypotheses Mathlib's `sq_nonneg` / `mul_self_nonneg` carry. They
serve as the baseline against which Part III measures what happens when `LinearOrder`
is removed. -/

/-- Squares are nonnegative in any linearly ordered semiring (the `^2` form). This is
the precise hypothesis set of Mathlib's `sq_nonneg`. -/
theorem sq_nonneg_of_linearOrder {R : Type*} [Semiring R] [LinearOrder R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (x : R) : 0 ≤ x ^ 2 :=
  sq_nonneg x

/-- Squares are nonnegative in any linearly ordered semiring (the `x * x` form). -/
theorem mul_self_nonneg_of_linearOrder {R : Type*} [Semiring R] [LinearOrder R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (x : R) : 0 ≤ x * x :=
  mul_self_nonneg x

/-! ## Part II. ℂ with `ComplexOrder` satisfies every *non-totality* hypothesis.

We record, as machine-checked instance lookups, that ℂ is a commutative ring with a
compatible partial order possessing all three algebraic mixins required by
`sq_nonneg`. The *only* hypothesis it lacks is `LinearOrder`. -/

example : CommRing ℂ := inferInstance
example : PartialOrder ℂ := inferInstance
example : ExistsAddOfLE ℂ := inferInstance
example : AddLeftMono ℂ := inferInstance
example : PosMulMono ℂ := inferInstance

/-- A self-contained checklist: ℂ carries every `sq_nonneg` hypothesis *except*
totality, packaged as a single proposition so the gap is explicit. -/
theorem complex_has_all_but_linearOrder :
    Nonempty (ExistsAddOfLE ℂ) ∧ Nonempty (PosMulMono ℂ) ∧ Nonempty (AddLeftMono ℂ) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-! ## Part III. The obstruction: over ℂ, `sq_nonneg` fails — totality is essential. -/

/-- The imaginary unit has a strictly negative square: `I² = -1 < 0`. -/
theorem I_sq_lt_zero : Complex.I ^ 2 < 0 := by
  rw [Complex.I_sq]
  exact neg_lt_zero.mpr zero_lt_one

/-- **Main counterexample.** Nonnegativity of squares *fails* over ℂ: there is no way
to derive `0 ≤ z²` for every complex `z`, because the imaginary unit violates it.
Equivalently, `mul_self_nonneg` is *false* once `LinearOrder` is dropped to
`PartialOrder`, even with all other `sq_nonneg` hypotheses in force. -/
theorem sq_nonneg_fails_on_complex : ¬ ∀ z : ℂ, 0 ≤ z ^ 2 := by
  intro h
  exact absurd (lt_of_le_of_lt (h Complex.I) I_sq_lt_zero) (lt_irrefl 0)

/-- The `x * x` form fails likewise. -/
theorem mul_self_nonneg_fails_on_complex : ¬ ∀ z : ℂ, 0 ≤ z * z := by
  intro h
  have hle : (0 : ℂ) ≤ Complex.I * Complex.I := h Complex.I
  rw [Complex.I_mul_I] at hle
  have hlt : (-1 : ℂ) < 0 := neg_lt_zero.mpr zero_lt_one
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl 0)

/-! ## Part IV. Locating the obstruction precisely at *totality*.

The failure in Part III is not caused by any algebraic defect — ℂ has all the ring
mixins. It is caused by the order being merely partial: `I` and `0` are incomparable,
so a total-order case split (`le_or_gt 0 I`) is unavailable. -/

/-- `I` and `0` are incomparable under `ComplexOrder`. -/
theorem I_incomparable_zero : ¬ (Complex.I ≤ 0) ∧ ¬ (0 ≤ Complex.I) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.nonpos_iff]; simp [Complex.I_re, Complex.I_im]
  · rw [Complex.nonneg_iff]; simp [Complex.I_re, Complex.I_im]

/-- Therefore the canonical order on ℂ is **not total**: this is the one and only
hypothesis of `sq_nonneg` that ℂ fails to satisfy. -/
theorem complexOrder_not_total : ¬ ∀ z w : ℂ, z ≤ w ∨ w ≤ z := by
  intro h
  rcases h Complex.I 0 with h₁ | h₂
  · exact I_incomparable_zero.1 h₁
  · exact I_incomparable_zero.2 h₂

/-! ## Part V. The Artin–Schreier root cause: ℂ is not formally real.

A field admits a linearly ordered ring structure only if it is *formally real* (−1 is
not a sum of squares). In ℂ, −1 is already a single square, `(-1) = I·I`, so ℂ is not
formally real — which is *why* no compatible linear order can exist. We make both ends
of this explicit. -/

/-- −1 is a square in ℂ (so ℂ is not formally real). -/
theorem neg_one_isSquare_complex : IsSquare (-1 : ℂ) :=
  ⟨Complex.I, Complex.I_mul_I.symm⟩

/-- **Artin–Schreier obstruction, abstract form.** In *any* linearly ordered ring,
−1 is never a square. Contrapositive: a ring in which −1 is a square (such as ℂ)
admits no order making it a linearly ordered ring — the structural reason `sq_nonneg`
cannot hold over ℂ. -/
theorem neg_one_not_isSquare_of_linearOrder {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] : ¬ IsSquare (-1 : R) := by
  rintro ⟨r, hr⟩
  have hnonneg : (0 : R) ≤ r * r := mul_self_nonneg r
  rw [← hr] at hnonneg
  -- `0 ≤ -1` forces `1 ≤ 0`, contradicting `0 < 1`.
  rw [neg_nonneg] at hnonneg
  exact absurd hnonneg (not_le.mpr zero_lt_one)

end Sqrt2OQ01OQ01
