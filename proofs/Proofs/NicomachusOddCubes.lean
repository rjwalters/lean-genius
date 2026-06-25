import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-
# Sum of the First n Odd Cubes: ∑ (2k−1)³ = n²(2n²−1)

## Open Question (nicomachus-sum-of-cubes-oq-03)

The odd-cube analogue of Nicomachus's theorem.  Where the parent identity sums
*all* cubes `1³ + 2³ + ⋯ + n³ = (∑k)²`, here we sum only the **odd** cubes:

    1³ + 3³ + 5³ + ⋯ + (2n−1)³ = n²(2n²−1).

Indexing the `n` odd numbers as `2k+1` for `k = 0,…,n−1` (so `range n` produces
`1, 3, …, 2n−1`), the statement reads `∑_{k<n} (2k+1)³ = n²(2n²−1)`.

Check: `n=1 → 1 = 1·1`, `n=2 → 1+27 = 28 = 4·7`, `n=3 → 1+27+125 = 153 = 9·17`.

## Result

A fully machine-checked, self-contained proof by induction.

The closed form `n²(2n²−1)` carries a subtraction, which is the enemy of `ring`
over ℕ (truncated subtraction is not a ring operation).  We sidestep it entirely
by proving the **subtraction-free** equivalent

    `(∑_{k<n} (2k+1)³) + n² = 2·n⁴`        (`sum_odd_cubes_add`),

obtained by adding `n²` to both sides of `n²(2n²−1) = 2n⁴ − n²`.  Every term is a
genuine natural number, so the inductive step closes by a single polynomial
identity (`ring` for the algebra, `omega` to combine it with the hypothesis).
The headline form `n²(2n²−1)` is then recovered over ℤ via `push_cast`, where the
subtraction is honest.

## Novelty

Mathlib has neither the odd-cube identity nor its subtraction-free repackaging.
This file supplies both, mirroring the additive clear-denominator technique used
for the parent Nicomachus and Faulhaber-type sums in the gallery.

0 sorries, 0 axioms.
-/

namespace NicomachusOddCubes

open Finset

/-- **Subtraction-free odd-cube identity.**  Adding `n²` to both sides of the
headline `∑(2k+1)³ = n²(2n²−1) = 2n⁴ − n²` clears the truncated subtraction, so
the whole statement lives cleanly in ℕ:

`(∑_{k<n} (2k+1)³) + n² = 2·n⁴`.

The induction step is a pure polynomial identity; `omega` splices it together
with the inductive hypothesis. -/
theorem sum_odd_cubes_add (n : ℕ) :
    (∑ k ∈ range n, (2 * k + 1) ^ 3) + n ^ 2 = 2 * n ^ 4 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sum_range_succ]
    -- The algebraic heart, a subtraction-free polynomial identity over ℕ:
    have key : 2 * m ^ 4 + (2 * m + 1) ^ 3 + (m + 1) ^ 2
        = 2 * (m + 1) ^ 4 + m ^ 2 := by ring
    -- `ih : (∑ k ∈ range m, (2k+1)³) + m² = 2·m⁴` and `key` are linear in the
    -- nonlinear atoms; `omega` closes the goal.
    omega

/-- **Sum of the first `n` odd cubes** (headline form, over ℤ).  Stating the
identity over ℤ lets the closed form `n²(2n²−1)` use honest subtraction:

`∑_{k<n} (2k+1)³ = n²·(2n²−1)`. -/
theorem sum_odd_cubes (n : ℕ) :
    (∑ k ∈ range n, ((2 * (k : ℤ) + 1) ^ 3)) = (n : ℤ) ^ 2 * (2 * (n : ℤ) ^ 2 - 1) := by
  have h := sum_odd_cubes_add n
  -- Push the ℕ identity into ℤ, isolate the sum, then `ring` clears the product.
  have hℤ := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at hℤ
  -- hℤ : (∑ k ∈ range n, (2·↑k+1)³) + ↑n² = 2·↑n⁴
  have hsum : (∑ k ∈ range n, ((2 * (k : ℤ) + 1) ^ 3)) = 2 * (n : ℤ) ^ 4 - (n : ℤ) ^ 2 := by
    linarith [hℤ]
  rw [hsum]; ring

/-- **Triangular/closed multiplicative form.**  Four times the sum of the first
`n` odd cubes plus `4n²` equals `8n⁴` — the same content as `sum_odd_cubes_add`,
scaled, recorded for callers who prefer the `2n²−1` factor cleared into a
product.  Kept over ℕ and subtraction-free. -/
theorem four_mul_sum_odd_cubes (n : ℕ) :
    4 * (∑ k ∈ range n, (2 * k + 1) ^ 3) + 4 * n ^ 2 = 8 * n ^ 4 := by
  have h := sum_odd_cubes_add n
  omega

end NicomachusOddCubes
