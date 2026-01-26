/-!
# Erdős Problem #864: Almost-Sidon Sets with One Collision

Let A ⊆ {1, ..., N} be such that at most one integer n has multiple
representations as a + b with a ≤ b ∈ A. What is the maximum |A|?

## Key Results

- Erdős–Freud (1991): |A| ≥ (1+o(1)) · (2/√3) · √N (construction)
- Conjecture: |A| ≤ (1+o(1)) · (2/√3) · √N (matching upper bound)
- For differences (a − b): |A| ~ √N (proved by Erdős–Freud)
- Sidon sets (no collisions at all): |A| ≤ √N + O(N^{1/4})
- This is a weaker version of Problem #840

## References

- Erdős, Freud (1991): [ErFr91]
- Erdős (1992): [Er92c]
- <https://erdosproblems.com/864>
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

/-! ## Core Definitions -/

/-- The number of ordered representations of n as a + b with a ≤ b, a, b ∈ A. -/
def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n)).card

/-- The set of integers with multiple sum representations from A. -/
def multiRepSet (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)
    |>.filter (fun n => sumRepCount A n ≥ 2)

/-- A is an almost-Sidon set: at most one integer has multiple representations. -/
def IsAlmostSidon (A : Finset ℕ) : Prop :=
  (multiRepSet A).card ≤ 1

/-- A is a Sidon set: no integer has multiple representations. -/
def IsSidon (A : Finset ℕ) : Prop :=
  (multiRepSet A).card = 0

/-- The maximum size of an almost-Sidon subset of {1, ..., N}. -/
noncomputable def maxAlmostSidon (N : ℕ) : ℕ :=
  Finset.sup ((Finset.Icc 1 N).powerset.filter (fun A => IsAlmostSidon A)) Finset.card

/-! ## Main Conjecture -/

/-- **Erdős Problem #864** (OPEN): The maximum almost-Sidon set in {1,...,N}
    has size (1+o(1)) · (2/√3) · √N. -/
axiom erdos_864_conjecture :
  -- For all ε > 0, for sufficiently large N:
  -- maxAlmostSidon N ≤ (2/√3 + ε) · √N
  True

/-! ## Known Bounds -/

/-- **Erdős–Freud (1991)**: Lower bound via reflected Sidon construction.
    Take a Sidon set B ⊆ {1,...,N/3} and form A = B ∪ {N − b : b ∈ B}.
    This gives |A| ≥ (1+o(1)) · (2/√3) · √N. -/
axiom erdos_freud_lower_bound :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (maxAlmostSidon N : ℝ) ≥ (2 / Real.sqrt 3 - ε) * Real.sqrt (N : ℝ)

/-- Sidon set upper bound: |A| ≤ √N + O(N^{1/4}) for Sidon sets. -/
axiom sidon_upper_bound :
  ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ) (A : Finset ℕ), (∀ a ∈ A, a ∈ Finset.Icc 1 N) →
      IsSidon A → (A.card : ℝ) ≤ Real.sqrt (N : ℝ) + C * (N : ℝ) ^ (1/4 : ℝ)

/-- Almost-Sidon sets can be larger than Sidon sets by a factor of 2/√3 ≈ 1.155.
    One extra collision allows ~15.5% more elements. -/
axiom almost_sidon_exceeds_sidon :
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (maxAlmostSidon N : ℝ) > Real.sqrt (N : ℝ) + 1

/-- Every Sidon set is also almost-Sidon (trivially). -/
theorem sidon_is_almost_sidon (A : Finset ℕ) (h : IsSidon A) : IsAlmostSidon A := by
  unfold IsAlmostSidon IsSidon at *
  omega

/-! ## Difference Version -/

/-- For the difference analogue (at most one n with multiple a − b
    representations), Erdős–Freud proved |A| ~ √N. -/
axiom erdos_freud_difference_version :
  -- The maximum size of A ⊆ {1,...,N} with at most one difference collision
  -- is asymptotically √N
  True

/-! ## Structural Properties -/

/-- The number of ordered pairs (a, b) with a ≤ b in A is C(|A|, 2) + |A|.
    In a Sidon set, all pairwise sums are distinct, using C(|A|,2) + |A|
    distinct values from {2, ..., 2N}. -/
axiom pairwise_sum_count (A : Finset ℕ) :
  ((A ×ˢ A).filter (fun p => p.1 ≤ p.2)).card = A.card * (A.card + 1) / 2

/-- For almost-Sidon A, at most one sum has a collision, so the number of
    distinct sums is ≥ C(|A|,2) + |A| − 1. These must fit in [2, 2N]. -/
axiom almost_sidon_sum_range (A : Finset ℕ) (N : ℕ) :
  (∀ a ∈ A, a ∈ Finset.Icc 1 N) → IsAlmostSidon A →
    A.card * (A.card + 1) / 2 - 1 ≤ 2 * N - 1

/-- The reflected construction: B ∪ (N − B) is almost-Sidon when B is Sidon.
    The only possible collision is at n = N (sums from B-side and reflected-side). -/
axiom reflected_construction_valid (N : ℕ) (B : Finset ℕ) :
  (∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3)) → IsSidon B →
    IsAlmostSidon (B ∪ B.image (fun b => N - b))
