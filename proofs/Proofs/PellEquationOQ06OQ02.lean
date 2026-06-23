/-
Pell's Equation OQ-06-OQ-02: The Negative-Pell Chain as Powers of the
Fundamental Unit of ℤ[√2]

The parent entry (`pell-equation-oq-06`) proves, by an elementary ring identity,
that the substitution

    (x, y) ↦ (3x + 4y, 2x + 3y)

preserves the form x² − 2y² and therefore generates infinitely many solutions of
the negative Pell equation x² − 2y² = −1 starting from (1, 1). It *remarks* that
this map "is multiplication by 3 + 2√2 in ℤ[√2]", but never makes the ring
structure precise. This entry supplies exactly that missing structure, working
inside Mathlib's ring of quadratic integers `ℤ√2 = Zsqrtd 2`.

The fundamental unit is

    ζ = 1 + √2 = ⟨1, 1⟩ ∈ ℤ[√2],   with   N(ζ) = 1² − 2·1² = −1,

so ζ is a unit of norm −1. Its square is the classical norm-`+1` Pell unit

    ζ² = 3 + 2√2 = ⟨3, 2⟩,   with   N(ζ²) = 1,

and *multiplication by ζ²* reproduces the parent's step map exactly. Consequently
the parent's chain is realized by the **odd powers of ζ**:

    ⟨xₙ, yₙ⟩ = ζ^(2n+1)        (negPellSeq_eq_pow)

and the multiplicativity of the quadratic-integer norm gives a conceptual, one-line
re-derivation of the parent's term-by-term computation:

    N(⟨xₙ, yₙ⟩) = N(ζ)^(2n+1) = (−1)^(2n+1) = −1.

This also exposes the full norm dichotomy that the elementary parent cannot see:
the *odd* powers of ζ solve x² − 2y² = −1 (negative Pell) while the *even* powers
solve x² − 2y² = +1 (positive Pell). The norm `+1` case is precisely what Mathlib's
`Pell.Solution₁` machinery models; the norm `−1` case is its still-unformalized
companion, which this lineage handles from scratch.

Main results:
  • `norm_ζ`                  — N(ζ) = −1 (ζ is a unit of norm −1).
  • `isUnit_ζ`                — ζ is a unit of ℤ[√2] (the fundamental unit).
  • `ζ_sq`                    — ζ² = ⟨3,2⟩ = 3 + 2√2, the norm-+1 Pell unit.
  • `negPellSeq_succ_eq_mul`  — the parent's step map is multiplication by ζ².
  • `negPellSeq_eq_pow`       — ⟨xₙ, yₙ⟩ = ζ^(2n+1) (the chain = odd powers of ζ).
  • `negPellSeq_norm_via_unit`— conceptual re-proof of x² − 2y² = −1 via N multiplicative.
  • `norm_ζ_pow_odd` / `norm_ζ_pow_even` — the −1 / +1 norm dichotomy of the powers.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent entry: `pell-equation-oq-06` (elementary chain; infinitude).
- Mathlib `Mathlib/NumberTheory/Zsqrtd/Basic.lean` (`Zsqrtd`, `Zsqrtd.norm`,
  `Zsqrtd.norm_mul`, `Zsqrtd.norm_eq_one_iff`).
- Mathlib `Mathlib/NumberTheory/Pell.lean` (`Pell.Solution₁`: the norm `+1` case).
-/

import Mathlib
import Proofs.PellEquationOQ06

namespace PellEquationOQ06OQ02

open PellEquationOQ06

/-
## The fundamental unit ζ = 1 + √2 of ℤ[√2]
-/

/-- The fundamental solution `(1, 1)` viewed as the unit `1 + √2` of `ℤ[√2]`. -/
def ζ : ℤ√2 := ⟨1, 1⟩

/-- **ζ has norm −1.** `N(1 + √2) = 1² − 2·1² = −1`, so ζ realizes the
    fundamental solution of the *negative* Pell equation. -/
theorem norm_ζ : ζ.norm = -1 := by
  simp [ζ, Zsqrtd.norm_def]

/-- **ζ is a unit of ℤ[√2]** — the fundamental unit. A quadratic integer is a unit
    iff its norm has absolute value `1`, and `|N(ζ)| = |−1| = 1`. -/
theorem isUnit_ζ : IsUnit ζ := by
  rw [← Zsqrtd.norm_eq_one_iff, norm_ζ]
  decide

/-- **ζ² = 3 + 2√2.** Squaring the norm-`−1` unit gives the classical norm-`+1`
    fundamental unit of ℤ[√2], the multiplier behind the parent's step map. -/
theorem ζ_sq : ζ ^ 2 = (⟨3, 2⟩ : ℤ√2) := by
  rw [pow_two]
  refine Zsqrtd.ext ?_ ?_ <;> simp [ζ, Zsqrtd.re_mul, Zsqrtd.im_mul]

/-- **N(ζ²) = +1.** The pair `(3, 2)` solves the positive Pell equation
    `x² − 2y² = 1`; `ζ²` is the fundamental unit of norm `+1`. -/
theorem norm_ζ_sq : (ζ ^ 2).norm = 1 := by
  rw [ζ_sq]; decide

/-
## Multiplicativity of the norm under powers
-/

/-- The quadratic-integer norm is multiplicative under powers:
    `N(zᵏ) = N(z)ᵏ`. (A direct induction off `Zsqrtd.norm_mul`.) -/
theorem norm_pow {d : ℤ} (z : ℤ√d) : ∀ k : ℕ, (z ^ k).norm = z.norm ^ k
  | 0 => by simp
  | (k + 1) => by rw [pow_succ, Zsqrtd.norm_mul, norm_pow z k, pow_succ]

/-
## The parent chain as the odd powers of ζ
-/

/-- **The parent's step map is multiplication by ζ² in ℤ[√2].** The recurrence
    `(x, y) ↦ (3x + 4y, 2x + 3y)` is exactly `· * (3 + 2√2)`. -/
theorem negPellSeq_succ_eq_mul (n : ℕ) :
    (⟨(negPellSeq (n + 1)).1, (negPellSeq (n + 1)).2⟩ : ℤ√2)
      = (⟨(negPellSeq n).1, (negPellSeq n).2⟩ : ℤ√2) * ζ ^ 2 := by
  rw [ζ_sq, negPellSeq_succ]
  refine Zsqrtd.ext ?_ ?_ <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-- **The negative-Pell chain is the odd powers of the fundamental unit:**
    `⟨xₙ, yₙ⟩ = ζ^(2n+1)` in ℤ[√2]. Proved by induction: ζ^(2(n+1)+1) =
    ζ^(2n+1) · ζ², and multiplication by ζ² is the parent's step map. -/
theorem negPellSeq_eq_pow (n : ℕ) :
    (⟨(negPellSeq n).1, (negPellSeq n).2⟩ : ℤ√2) = ζ ^ (2 * n + 1) := by
  induction n with
  | zero => simp [negPellSeq_zero, ζ]
  | succ k ih =>
    have hexp : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [hexp, pow_add, ← ih, ζ_sq, negPellSeq_succ]
    refine Zsqrtd.ext ?_ ?_ <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-
## Conceptual re-derivation of the negative Pell identity
-/

/-- **The norm identity, conceptually.** Multiplicativity of the ℤ[√2] norm turns
    the parent's term-by-term induction (`negPellSeq_norm`) into a single
    computation: `N(⟨xₙ, yₙ⟩) = N(ζ)^(2n+1) = (−1)^(2n+1) = −1`. -/
theorem negPellSeq_norm_via_unit (n : ℕ) :
    (negPellSeq n).1 ^ 2 - 2 * (negPellSeq n).2 ^ 2 = -1 := by
  have hnorm :
      (⟨(negPellSeq n).1, (negPellSeq n).2⟩ : ℤ√2).norm
        = (negPellSeq n).1 ^ 2 - 2 * (negPellSeq n).2 ^ 2 := by
    rw [Zsqrtd.norm_def]; ring
  rw [← hnorm, negPellSeq_eq_pow, norm_pow, norm_ζ, Odd.neg_one_pow ⟨n, by ring⟩]

/-
## The norm dichotomy of the powers of ζ
-/

/-- **Odd powers of ζ solve the negative Pell equation:** `N(ζ^(2n+1)) = −1`.
    These are exactly the entries of the parent's chain. -/
theorem norm_ζ_pow_odd (n : ℕ) : (ζ ^ (2 * n + 1)).norm = -1 := by
  rw [norm_pow, norm_ζ, Odd.neg_one_pow ⟨n, by ring⟩]

/-- **Even powers of ζ solve the positive Pell equation:** `N(ζ^(2n)) = +1`.
    These are the powers of the norm-`+1` unit `3 + 2√2` (the case modeled by
    Mathlib's `Pell.Solution₁`). -/
theorem norm_ζ_pow_even (n : ℕ) : (ζ ^ (2 * n)).norm = 1 := by
  rw [norm_pow, norm_ζ, pow_mul]; simp

/-
## Explicit small powers (sanity checks)
-/

example : ζ ^ 1 = (⟨1, 1⟩ : ℤ√2) := by rw [pow_one]; rfl
example : ζ ^ 3 = (⟨7, 5⟩ : ℤ√2) := by decide
example : ζ ^ 5 = (⟨41, 29⟩ : ℤ√2) := by decide

example : (ζ ^ 1).norm = -1 := norm_ζ_pow_odd 0
example : (ζ ^ 3).norm = -1 := norm_ζ_pow_odd 1
example : (ζ ^ 2).norm = 1 := norm_ζ_pow_even 1
example : (ζ ^ 4).norm = 1 := norm_ζ_pow_even 2

#check @norm_ζ
#check @isUnit_ζ
#check @ζ_sq
#check @negPellSeq_eq_pow
#check @negPellSeq_norm_via_unit
#check @norm_ζ_pow_odd
#check @norm_ζ_pow_even

end PellEquationOQ06OQ02
