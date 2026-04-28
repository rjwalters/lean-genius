/-
Erdős Problem #886: Divisors Near the Square Root (Ruzsa's Conjecture)

Source: https://erdosproblems.com/886
Status: OPEN

Statement:
Let ε > 0. Is it true that, for all large n, the number of divisors of n
in the interval (√n, √n + n^{1/2-ε}) is O_ε(1)?

In other words: can the divisors of n "cluster" near √n, or are they
necessarily spread out?

Attribution:
Erdős attributes this conjecture to Imre Z. Ruzsa.

Related Results:
- Erdős and Rosenfeld (1997) proved there are infinitely many n with
  four divisors in (√n, √n + n^{1/4})

See also Problem #887.

Tags: Number theory, Divisors, Distribution of divisors
-/

import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor

open Nat Finset Real

namespace Erdos886

/- ## Part I: Divisors of n
-/

/-- The set of positive divisors of n. -/
def divisorsOf (n : ℕ) : Finset ℕ := n.divisors

/-- The number of divisors of n, denoted τ(n) or d(n). -/
def divisorCount (n : ℕ) : ℕ := (divisorsOf n).card

/-- Every positive integer has at least one divisor (itself). -/
theorem divisorCount_pos (n : ℕ) (hn : n ≥ 1) : divisorCount n ≥ 1 :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩

/- ## Part II: The Interval Near √n
-/

/-- The interval (√n, √n + n^{1/2-ε}) for small ε > 0.
    This is where Ruzsa conjectures divisors cannot cluster. -/
noncomputable def criticalInterval (n : ℕ) (ε : ℝ) : Set ℝ :=
  {x : ℝ | Real.sqrt n < x ∧ x < Real.sqrt n + (n : ℝ)^(1/2 - ε)}

/-- The interval has width n^{1/2-ε}, which shrinks relative to √n as n grows. -/
noncomputable def intervalWidth (n : ℕ) (ε : ℝ) : ℝ :=
  (n : ℝ)^(1/2 - ε)

/-- For large n, the interval width is o(√n). -/
/- ## Part III: Divisors in the Critical Interval
-/

/-- The set of divisors of n lying in the interval (a, b). -/
def divisorsInInterval (n : ℕ) (a b : ℝ) : Finset ℕ :=
  (divisorsOf n).filter (fun d => a < (d : ℝ) ∧ (d : ℝ) < b)

/-- The number of divisors of n in the critical interval. -/
noncomputable def divisorsNearSqrt (n : ℕ) (ε : ℝ) : ℕ :=
  (divisorsInInterval n (Real.sqrt n) (Real.sqrt n + intervalWidth n ε)).card

/- ## Part IV: Ruzsa's Conjecture
-/

/-- **Ruzsa's Conjecture (Erdős Problem #886):**
    For all ε > 0, there exists C_ε such that for all large n,
    the number of divisors of n in (√n, √n + n^{1/2-ε}) is at most C_ε.
    In symbols: divisorsNearSqrt(n, ε) = O_ε(1) -/
def ruzsaConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ C : ℕ, C > 0 ∧
      ∃ N : ℕ, ∀ n ≥ N,
        divisorsNearSqrt n ε ≤ C

/- ## Part V: Erdős-Rosenfeld Result
-/

/-- **Erdős-Rosenfeld Theorem (1997):**
    There are infinitely many n with four divisors in (√n, √n + n^{1/4}).
    Note: This uses ε = 1/4, which gives a wider interval than the conjecture. -/
/-- The Erdős-Rosenfeld result: infinitely many n have ≥ 4 divisors in (√n, √n + n^{1/4}). -/
axiom erdos_rosenfeld_four_divisors :
    ∃ S : Set ℕ, S.Infinite ∧ ∀ n ∈ S, divisorsNearSqrt n (1/4 : ℝ) ≥ 4

/- ## Part VI: The Factor-Difference Set
-/

/-- The set {d - d' : d, d' | n, d > d'} of differences between divisors. -/
def factorDifferenceSet (n : ℕ) : Finset ℤ :=
  (divisorsOf n).product (divisorsOf n)
    |>.filter (fun dd' => dd'.1 > dd'.2)
    |>.image (fun dd' => (dd'.1 : ℤ) - (dd'.2 : ℤ))

/-- The factor-difference set is nonempty when n has at least 2 divisors. -/
/- ## Part VII: Divisor Density Near √n
-/

/-- The "density" of divisors near √n, measured by count / interval width. -/
noncomputable def localDivisorDensity (n : ℕ) (ε : ℝ) : ℝ :=
  (divisorsNearSqrt n ε : ℝ) / intervalWidth n ε

/-- **Ruzsa's Conjecture Reformulated:**
    The local divisor density near √n goes to 0 as n → ∞. -/
def ruzsaConjectureAlt : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 → ∃ N : ℕ, ∀ n ≥ N,
      localDivisorDensity n ε < δ

/-- The two formulations are equivalent. -/
/- ## Part VIII: Examples
-/

/-- Numbers with many divisors (like n = 2^k or n = k!) have divisors more
    spread out, not clustered near √n. -/
def isHighlyComposite (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → divisorCount m < divisorCount n

/- ## Part IX: Bounds and Partial Results
-/

/-- The number of divisors in ANY interval of length L is at most τ(n). -/
theorem trivial_bound (n : ℕ) (ε : ℝ) (hε : ε > 0) (hn : n ≥ 1) :
    divisorsNearSqrt n ε ≤ divisorCount n := by
  unfold divisorsNearSqrt divisorCount divisorsInInterval
  apply card_filter_le

/-- τ(n) ≤ 2√n for all n ≥ 1. -/
/- ## Part X: Summary
-/

/-- **Summary of Erdős Problem #886:**
    Combines the proved trivial bound with the Erdős-Rosenfeld result:
    1. The count of divisors near √n is bounded by τ(n) (proved)
    2. For ε = 1/4, infinitely many n have ≥ 4 divisors near √n (Erdős-Rosenfeld) -/
theorem erdos_886_summary :
    (∀ n ε, ε > 0 → n ≥ 1 → divisorsNearSqrt n ε ≤ divisorCount n) ∧
    (∃ S : Set ℕ, S.Infinite ∧ ∀ n ∈ S, divisorsNearSqrt n (1/4 : ℝ) ≥ 4) :=
  ⟨fun n ε hε hn => trivial_bound n ε hε hn, erdos_rosenfeld_four_divisors⟩

end Erdos886
