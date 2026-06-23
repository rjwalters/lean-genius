import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-
# Apéry numbers: the central-binomial lower bound and geometric growth

## Context
This is a self-contained, axiom-free companion to the Apéry / ζ(3) lineage
(`BaselProblemOQ01OQ01OQ02.lean`).  That file proves the irrationality of ζ(3)
*from five axioms*, one of which is an exponential **upper** bound on the Apéry
numbers, `bₙ ≤ 34ⁿ`.  The opposite half of the squeeze — that the Apéry numbers
grow *at least* geometrically — has no axiom-free witness there.  This file
supplies it.

## The Apéry numbers
    bₙ = ∑_{k=0}^{n} C(n,k)² · C(n+k,k)²            (1, 5, 73, 1445, 33001, …)

These positive integers drive Apéry's proof: `bₙ ζ(3) − aₙ → 0` geometrically
while `bₙ → ∞`, and the competition forces irrationality.  For that argument the
*divergence* of `bₙ` matters, so a clean lower bound is exactly the structural
fact one wants.

## What is proved (all 0-axiom, 0-sorry)
* `aperyB_centralTerm` — the `k = n` summand is exactly `centralBinom n ²`.
* `centralBinom_sq_le_aperyB` — `C(2n,n)² ≤ bₙ`  (drop every other term).
* `two_pow_le_centralBinom` — `2ⁿ ≤ C(2n,n)`  (short induction, self-contained).
* `four_pow_le_aperyB` — `4ⁿ ≤ bₙ`  (geometric lower bound).
* `sixteen_pow_le_aperyB` — `16ⁿ ≤ 4n²·bₙ`  (sharper rate-16 bound from the
  central term: `bₙ ≳ 16ⁿ / 4n²`, since `C(2n,n)² ≈ 16ⁿ/πn`).
* `aperyB_tendsto_atTop` — `(bₙ : ℝ) → ∞`.

The true growth rate is `(1+√2)⁴ = 17+12√2 ≈ 33.97`; the rigorous bounds here
bracket the exponential base in `[4, 34]` (and `[16, 34]` up to a polynomial
factor), which is all the irrationality squeeze needs from the lower side.

Reference: Apéry (1979); van der Poorten, *A proof that Euler missed* (1979).
-/

open BigOperators Finset Nat Filter

namespace AperyCentralBinom

/-- The Apéry b-sequence `bₙ = ∑_{k≤n} C(n,k)² · C(n+k,k)²`. -/
def aperyB (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

theorem aperyB_zero : aperyB 0 = 1 := by simp [aperyB]

theorem aperyB_one : aperyB 1 = 5 := by simp [aperyB, Finset.sum_range_succ]

theorem aperyB_two : aperyB 2 = 73 := by decide

theorem aperyB_three : aperyB 3 = 1445 := by decide

/-- Every Apéry number is positive. -/
theorem aperyB_pos (n : ℕ) : 0 < aperyB n := by
  unfold aperyB
  apply Finset.sum_pos
  · intro k hk
    have h1 : 0 < n.choose k :=
      Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have h2 : 0 < (n + k).choose k := Nat.choose_pos (Nat.le_add_left k n)
    positivity
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

-- ============================================================================
-- The central term and the central-binomial lower bound
-- ============================================================================

/-- The `k = n` term of the Apéry sum is exactly the square of the central
binomial coefficient: `C(n,n)² · C(2n,n)² = C(2n,n)²`. -/
theorem aperyB_centralTerm (n : ℕ) :
    (n.choose n) ^ 2 * ((n + n).choose n) ^ 2 = (Nat.centralBinom n) ^ 2 := by
  rw [Nat.choose_self, one_pow, one_mul, Nat.centralBinom_eq_two_mul_choose, two_mul]

/-- Dropping every summand except `k = n` gives `C(2n,n)² ≤ bₙ`. -/
theorem centralBinom_sq_le_aperyB (n : ℕ) : (Nat.centralBinom n) ^ 2 ≤ aperyB n := by
  rw [← aperyB_centralTerm]
  unfold aperyB
  exact Finset.single_le_sum (f := fun k => (n.choose k) ^ 2 * ((n + k).choose k) ^ 2)
    (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self n))

-- ============================================================================
-- A self-contained exponential bound on the central binomial coefficient
-- ============================================================================

/-- `2ⁿ ≤ C(2n,n)`.  Proved by induction using the Pascal-type identity
`(n+1)·C(2n+2,n+1) = 2(2n+1)·C(2n,n)` (`Nat.succ_mul_centralBinom_succ`). -/
theorem two_pow_le_centralBinom : ∀ n : ℕ, 2 ^ n ≤ Nat.centralBinom n
  | 0 => by simp [Nat.centralBinom_zero]
  | n + 1 => by
    have ih := two_pow_le_centralBinom n
    -- Multiply the target by (n+1) > 0 and use the central-binomial recurrence.
    have h : (n + 1) * 2 ^ (n + 1) ≤ (n + 1) * Nat.centralBinom (n + 1) := by
      calc (n + 1) * 2 ^ (n + 1)
          = (2 * (n + 1)) * 2 ^ n := by ring
        _ ≤ (2 * (2 * n + 1)) * Nat.centralBinom n := Nat.mul_le_mul (by omega) ih
        _ = (n + 1) * Nat.centralBinom (n + 1) := (Nat.succ_mul_centralBinom_succ n).symm
    exact Nat.le_of_mul_le_mul_left h (Nat.succ_pos n)

/-- Geometric lower bound: `4ⁿ ≤ bₙ`. -/
theorem four_pow_le_aperyB (n : ℕ) : 4 ^ n ≤ aperyB n := by
  calc (4 : ℕ) ^ n
      = (2 ^ n) ^ 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (Nat.centralBinom n) ^ 2 := Nat.pow_le_pow_left (two_pow_le_centralBinom n) 2
    _ ≤ aperyB n := centralBinom_sq_le_aperyB n

/-- Sharper rate-16 bound: `16ⁿ ≤ 4n²·bₙ`, i.e. `bₙ ≳ 16ⁿ / 4n²`.
Uses the Erdős–Bertrand bound `4ⁿ ≤ 2n·C(2n,n)` and squares it. -/
theorem sixteen_pow_le_aperyB (n : ℕ) (hn : 0 < n) :
    16 ^ n ≤ 4 * n ^ 2 * aperyB n := by
  have hC : 4 ^ n ≤ 2 * n * Nat.centralBinom n :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  calc (16 : ℕ) ^ n
      = (4 ^ n) ^ 2 := by
        rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (2 * n * Nat.centralBinom n) ^ 2 := Nat.pow_le_pow_left hC 2
    _ = 4 * n ^ 2 * (Nat.centralBinom n) ^ 2 := by ring
    _ ≤ 4 * n ^ 2 * aperyB n := by
        gcongr
        exact centralBinom_sq_le_aperyB n

-- ============================================================================
-- Divergence of the Apéry numbers
-- ============================================================================

/-- The Apéry numbers diverge to infinity: `(bₙ : ℝ) → ∞`.
Squeeze above `4ⁿ → ∞` using `four_pow_le_aperyB`. -/
theorem aperyB_tendsto_atTop :
    Tendsto (fun n : ℕ => (aperyB n : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (g := fun n : ℕ => (aperyB n : ℝ))
    (f := fun n : ℕ => (4 : ℝ) ^ n) (fun n => ?_)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4))
  have h : (4 : ℕ) ^ n ≤ aperyB n := four_pow_le_aperyB n
  calc (4 : ℝ) ^ n = ((4 ^ n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (aperyB n : ℝ) := by exact_mod_cast h

end AperyCentralBinom
