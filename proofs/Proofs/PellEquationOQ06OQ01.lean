/-
Pell's Equation OQ-06-OQ-01: Classification of the negative Pell solutions x² − 2y² = −1

The parent entry `pell-equation-oq-06` (`Proofs/PellEquationOQ06.lean`) builds the
explicit chain

    (1, 1) → (7, 5) → (41, 29) → (239, 169) → …,   (x, y) ↦ (3x + 4y, 2x + 3y),

of solutions to the negative Pell equation x² − 2y² = −1 and shows there are
**infinitely many** integer solutions. That leaves open the *converse* question — the
genuine structural content — of whether the chain captures *every* solution.

This entry proves the **classification theorem**: the positive-integer solutions of
x² − 2y² = −1 are *exactly* the terms of the chain. The proof is a descent
(Vieta-jumping) argument:

  • the inverse substitution (x, y) ↦ (3x − 4y, 3y − 2x) also preserves the form
    (it is multiplication by the inverse unit 3 − 2√2 in ℤ[√2]);
  • for every positive solution other than the fundamental (1, 1), this predecessor is
    again a positive solution with a strictly smaller first coordinate;
  • the only positive solutions with x ≤ 6 is the base point — there is none with
    2 ≤ x ≤ 6 — so the descent terminates exactly at (1, 1).

Strong induction on `x.toNat` then shows every positive solution lies on the chain,
giving the set equality

    {(x, y) | x ≥ 1, y ≥ 1, x² − 2y² = −1} = range negPellSeq.

We also record the multiplicative bridge to the *positive* Pell equation: squaring any
norm −1 solution yields a norm +1 solution, since the ℤ[√2]-norm is multiplicative and
(−1)·(−1) = +1.

Main results:
  • `negPell_pred_step`            — the inverse map preserves x² − 2y².
  • `negPell_no_small_solution`    — no positive solution has 2 ≤ x ≤ 6.
  • `negPell_complete`             — every positive solution is a term of the chain.
  • `negPell_solutions_eq_range`   — exact set equality {positive solutions} = range chain.
  • `negPell_sq_is_pos_pell`       — squaring a norm −1 solution gives a norm +1 solution.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent entry `pell-equation-oq-06` (the chain and its infinitude).
- Mathlib `Pell.Solution₁` covers only the norm +1 equation; the norm −1 case and its
  classification are not in Mathlib.
-/

import Mathlib
import Proofs.PellEquationOQ06

namespace PellEquationOQ06

/-
## The inverse step and the descent
-/

/-- **Inverse step preserves the negative-Pell form.** The substitution
    `(x, y) ↦ (3x − 4y, 3y − 2x)` (multiplication by the inverse unit `3 − 2√2`
    of ℤ[√2]) keeps the value of `x² − 2y²` unchanged. -/
theorem negPell_pred_step (x y : ℤ) (h : x ^ 2 - 2 * y ^ 2 = -1) :
    (3 * x - 4 * y) ^ 2 - 2 * (3 * y - 2 * x) ^ 2 = -1 := by
  linear_combination h

/-- **There is no positive solution of `x² − 2y² = −1` with `2 ≤ x ≤ 6`.**
    Combined with the base point `(1, 1)`, this is what makes the descent terminate. -/
theorem negPell_no_small_solution (x y : ℤ) (hx2 : 2 ≤ x) (hx6 : x ≤ 6)
    (hy : 1 ≤ y) : x ^ 2 - 2 * y ^ 2 ≠ -1 := by
  intro h
  have hyle : y ≤ 4 := by
    nlinarith [h, mul_nonneg (by linarith : (0 : ℤ) ≤ 6 - x) (by linarith : (0 : ℤ) ≤ x),
      sq_nonneg (y - 4)]
  interval_cases x <;> interval_cases y <;> omega

/-- **Classification (completeness).** Every positive-integer solution of
    `x² − 2y² = −1` is a term of the chain `negPellSeq`. The proof descends along the
    inverse step until it reaches the fundamental solution `(1, 1) = negPellSeq 0`. -/
theorem negPell_complete (x y : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x ^ 2 - 2 * y ^ 2 = -1) : ∃ n, negPellSeq n = (x, y) := by
  by_cases hx1 : x = 1
  · -- base case: x = 1 forces y = 1
    subst hx1
    have hyle : y ≤ 1 := by nlinarith [sq_nonneg (y - 1)]
    have hy1 : y = 1 := by omega
    exact ⟨0, by rw [negPellSeq_zero, hy1]⟩
  · -- x ≥ 2: rule out 2 ≤ x ≤ 6, then descend
    have hx2 : 2 ≤ x := by omega
    have hx7 : 7 ≤ x := by
      by_contra hc
      push_neg at hc
      exact negPell_no_small_solution x y hx2 (by omega) hy h
    -- y ≥ 5 from x ≥ 7
    have hy5 : 5 ≤ y := by
      nlinarith [h, mul_nonneg (by linarith : (0 : ℤ) ≤ x - 7) (by linarith : (0 : ℤ) ≤ x + 7)]
    -- predecessor is strictly smaller: 3x − 4y < x  (from x < 2y)
    have hx2y : x < 2 * y := by nlinarith [h, hx, hy]
    have hlt : 3 * x - 4 * y < x := by linarith
    -- predecessor is positive: 3x − 4y ≥ 1 and 3y − 2x ≥ 1
    have hxfac : (3 * x - 4 * y - 1) * (3 * x + 4 * y + 1) = 2 * (y - 5) * (y + 1) := by
      linear_combination 9 * h
    have hxprod : 0 ≤ (3 * x - 4 * y - 1) * (3 * x + 4 * y + 1) := by
      rw [hxfac]; nlinarith [hy5]
    have hx'pos : 1 ≤ 3 * x - 4 * y := by
      nlinarith [hxprod, (by linarith : (0 : ℤ) < 3 * x + 4 * y + 1)]
    have hyfac : (3 * y - 2 * x) * (3 * y + 2 * x) = y ^ 2 + 4 := by linear_combination (-4) * h
    have hy'pos0 : 0 < 3 * y - 2 * x := by
      nlinarith [hyfac, sq_nonneg y, (by linarith : (0 : ℤ) < 3 * y + 2 * x)]
    have hy'pos : 1 ≤ 3 * y - 2 * x := by omega
    -- the predecessor is again a solution
    have h' : (3 * x - 4 * y) ^ 2 - 2 * (3 * y - 2 * x) ^ 2 = -1 := negPell_pred_step x y h
    -- recurse
    obtain ⟨n, hn⟩ := negPell_complete (3 * x - 4 * y) (3 * y - 2 * x) hx'pos hy'pos h'
    refine ⟨n + 1, ?_⟩
    rw [negPellSeq_succ, hn]
    dsimp only
    simp only [Prod.mk.injEq]
    constructor <;> ring
termination_by x.toNat
decreasing_by simp_wf; omega

/-
## Exact classification as a set equality
-/

/-- **The positive-integer solution set is exactly the chain.** Combining the parent's
    forward direction (every chain term is a positive solution) with `negPell_complete`
    (every positive solution is a chain term). -/
theorem negPell_solutions_eq_range :
    {p : ℤ × ℤ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 - 2 * p.2 ^ 2 = -1} = Set.range negPellSeq := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨hx, hy, h⟩
    obtain ⟨n, hn⟩ := negPell_complete p.1 p.2 hx hy h
    exact ⟨n, by rw [hn]⟩
  · rintro ⟨n, hn⟩
    rw [← hn]
    exact ⟨(negPellSeq_pos n).1, (negPellSeq_pos n).2, negPellSeq_norm n⟩

/-
## Multiplicative bridge to the positive Pell equation
-/

/-- **Squaring a norm −1 solution gives a norm +1 solution.** Since the ℤ[√2]-norm
    `N(x, y) = x² − 2y²` is multiplicative and `(x + y√2)² = (x² + 2y²) + (2xy)√2`, a
    solution of `x² − 2y² = −1` yields a solution of `X² − 2Y² = +1`, namely
    `(X, Y) = (x² + 2y², 2xy)`. This connects the negative Pell chain to Mathlib's
    `Pell.Solution₁` (the norm +1 equation). -/
theorem negPell_sq_is_pos_pell (x y : ℤ) (h : x ^ 2 - 2 * y ^ 2 = -1) :
    (x ^ 2 + 2 * y ^ 2) ^ 2 - 2 * (2 * x * y) ^ 2 = 1 := by
  have key : (x ^ 2 + 2 * y ^ 2) ^ 2 - 2 * (2 * x * y) ^ 2 = (x ^ 2 - 2 * y ^ 2) ^ 2 := by
    ring
  rw [key, h]; norm_num

/-- The squares of the negative-Pell chain give an explicit family of positive Pell
    solutions: `(x² + 2y², 2xy)` for `(x, y) = negPellSeq n`. -/
theorem negPellSeq_sq_is_pos_pell (n : ℕ) :
    ((negPellSeq n).1 ^ 2 + 2 * (negPellSeq n).2 ^ 2) ^ 2
        - 2 * (2 * (negPellSeq n).1 * (negPellSeq n).2) ^ 2 = 1 :=
  negPell_sq_is_pos_pell _ _ (negPellSeq_norm n)

example : ((7 : ℤ) ^ 2 + 2 * 5 ^ 2) ^ 2 - 2 * (2 * 7 * 5) ^ 2 = 1 := by norm_num

#check @negPell_complete
#check @negPell_solutions_eq_range
#check @negPell_sq_is_pos_pell

end PellEquationOQ06
