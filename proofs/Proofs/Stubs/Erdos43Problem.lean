/- Erdős Problem #43: Sidon Sets with Disjoint Difference Sets

If A, B ⊆ {1,...,N} are Sidon sets with (A-A) ∩ (B-B) = {0},
must C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1), where f(N) is
the maximum Sidon set size in {1,...,N}?

Status: OPEN ($100 bounty)
- Tao proved: |A| ≤ (1/√2 + o(1))√N when |A| = |B| (without improvement constant)
- Barreto: the equal-size strengthening with -c is FALSE for infinitely many N

Reference: https://erdosproblems.com/43
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/- ## Sidon Sets -/

/-- A Sidon set (B₂ set): all pairwise sums a + b (a ≤ b, a,b ∈ A) are distinct,
equivalently all nonzero pairwise differences are distinct. -/
def IsSidonSet (A : Finset ℤ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℤ, a₁ ∈ A → b₁ ∈ A → a₂ ∈ A → b₂ ∈ A →
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℤ) = {a₂, b₂}

/-- The difference set A - A = { a - b | a, b ∈ A }. -/
def diffSet (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 - p.2)

/- ## Disjoint Differences -/

/-- Two sets have disjoint nonzero differences: (A-A) ∩ (B-B) = {0}. -/
def DisjointDifferences (A B : Finset ℤ) : Prop :=
  ∀ d : ℤ, d ∈ diffSet A → d ∈ diffSet B → d = 0

/- ## Maximum Sidon Set Size -/

/-- f(N): the maximum cardinality of a Sidon set in {1,...,N}. -/
axiom maxSidonSize : ℕ → ℕ

/-- f(N) ~ √N: the maximum Sidon set size is asymptotically √N.
    This is a classical result in additive combinatorics. -/
axiom sidon_size_asymptotic :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    |(maxSidonSize N : ℝ) - Real.sqrt N| ≤ ε * Real.sqrt N

/- ## The Conjecture -/

/-- **Erdős Problem #43**: If A, B are Sidon sets in {1,...,N} with
disjoint nonzero differences, then C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1). -/
def ErdosProblem43 : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, ∀ A B : Finset ℤ,
    IsSidonSet A → IsSidonSet B →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) → (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
    DisjointDifferences A B →
    A.card.choose 2 + B.card.choose 2 ≤ (maxSidonSize N).choose 2 + C

/- ## Equal Size Variant -/

/-- The equal-size strengthening: when |A| = |B|, can we get
C(|A|,2) + C(|B|,2) ≤ (1 - c)·C(f(N),2) for some c > 0?
Barreto showed this is FALSE for infinitely many N. -/
def EqualSizeVariant : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∀ A B : Finset ℤ,
    IsSidonSet A → IsSidonSet B →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) → (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
    DisjointDifferences A B → A.card = B.card →
    (A.card.choose 2 + B.card.choose 2 : ℝ) ≤ (1 - c) * (maxSidonSize N).choose 2

/-- Barreto's result: the equal-size variant is false. -/
axiom barreto_counterexample : ¬EqualSizeVariant

/- ## Structural Bounds -/

/-- A single Sidon set A in {1,...,N} has C(|A|,2) ≤ N.
    Proof sketch: the C(|A|,2) pairwise sums a+b (a<b) are all distinct
    (by Sidon property) and lie in {3,...,2N-1}, which has 2N-3 elements.
    More precisely, the differences a-b for a≠b are all distinct and
    lie in {-(N-1),...,-1,1,...,N-1}, giving |A|²-|A| ≤ 2(N-1). -/
theorem sidon_pair_bound (A : Finset ℤ) (N : ℕ)
    (hS : IsSidonSet A) (hR : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) :
  A.card.choose 2 ≤ N := by
  -- Proof: The nonzero differences of a Sidon set A ⊆ {1,...,N} all lie in
  -- {-(N-1),...,-1,1,...,N-1}. There are |A|(|A|-1) distinct nonzero differences
  -- (by the Sidon property), so |A|(|A|-1) ≤ 2(N-1) ≤ 2N. Hence C(|A|,2) ≤ N.
  -- Key subgoal: the difference map (a,b) ↦ a-b is injective on off-diagonal pairs.
  sorry

/-- Disjoint differences force the nonzero differences of A and B
    to be completely disjoint, so the total number of distinct nonzero
    differences is |A|(|A|-1) + |B|(|B|-1), bounded by 2(N-1).
    This gives C(|A|,2) + C(|B|,2) ≤ N. -/
theorem disjoint_diff_combined_bound (A B : Finset ℤ) (N : ℕ)
    (hA : IsSidonSet A) (hB : IsSidonSet B)
    (hRA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) (hRB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N)
    (hD : DisjointDifferences A B) :
  A.card.choose 2 + B.card.choose 2 ≤ N := by
  -- Proof: Disjoint nonzero differences of A and B together give
  -- |A|(|A|-1) + |B|(|B|-1) distinct nonzero integers in {-(N-1),...,N-1}.
  -- So |A|(|A|-1) + |B|(|B|-1) ≤ 2(N-1), giving C(|A|,2) + C(|B|,2) ≤ N-1 ≤ N.
  sorry

/- ## Tao's Partial Result

Tao showed: if |A| = |B| and (A-A) ∩ (B-B) = {0}, then
|A| ≤ (1/√2 + o(1))√N.

The key idea: the C(|A|,2) + C(|B|,2) distinct differences from
A and B together are disjoint nonzero integers in {-(N-1),...,N-1}.
When |A| = |B| = m, we need 2·C(m,2) ≤ 2(N-1), so m(m-1) ≤ 2(N-1),
giving m ≤ (1/√2 + o(1))√N. -/

/-- Tao's bound: when |A| = |B|, both equal m, we get m^2 ≤ 2N+1.
    This follows from disjoint_diff_combined_bound: 2·C(m,2) ≤ N,
    so m(m-1) ≤ N, giving m^2 ≤ N + m ≤ 2N for large N. -/
theorem tao_equal_size_bound (A B : Finset ℤ) (N : ℕ)
    (hA : IsSidonSet A) (hB : IsSidonSet B)
    (hRA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) (hRB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N)
    (hD : DisjointDifferences A B) (hEq : A.card = B.card) :
  (A.card : ℝ) ^ 2 ≤ 2 * N + 1 := by
  -- From disjoint_diff_combined_bound: C(m,2) + C(m,2) ≤ N where m = |A| = |B|
  have hcomb := disjoint_diff_combined_bound A B N hA hB hRA hRB hD
  set m := A.card
  rw [hEq] at hcomb
  rw [Nat.choose_two_right, Nat.choose_two_right] at hcomb
  -- hcomb: m*(m-1)/2 + m*(m-1)/2 ≤ N
  suffices h : m * m ≤ 2 * N + 1 from by exact_mod_cast h
  -- Key: m*(m-1) is even (consecutive nats), so m*(m-1) = 2*(m*(m-1)/2) ≤ N
  -- Then m ≤ m*(m-1)+1 ≤ N+1, so m² = m*(m-1)+m ≤ N+(N+1) = 2N+1
  have hmm1 : m * (m - 1) ≤ N := by
    -- m*(m-1) = 2*(m*(m-1)/2) since m*(m-1) is always even
    have h_even : m * (m - 1) = 2 * (m * (m - 1) / 2) := by
      rcases m with _ | k
      · simp
      · rw [Nat.succ_sub_one]
        -- (k+1)*k is even: k*(k+1) = 2*(k*(k+1)/2)
        omega  -- omega should handle: (k+1)*k = 2*((k+1)*k/2) via even-ness
    omega
  omega

/- ## Counting Arguments -/

/-- For a Sidon set, nonzero differences are injective: if a₁ - b₁ = a₂ - b₂
    and a₁ ≠ b₁, then a₁ = a₂ and b₁ = b₂. -/
theorem sidon_diff_injective (A : Finset ℤ) (hS : IsSidonSet A)
    {a₁ b₁ a₂ b₂ : ℤ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (hne : a₁ ≠ b₁) (heq : a₁ - b₁ = a₂ - b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hsum : a₁ + b₂ = a₂ + b₁ := by omega
  have hpair := hS a₁ b₂ a₂ b₁ ha₁ hb₂ ha₂ hb₁ hsum
  -- a₁ ∈ {a₂, b₁}: a₁ = a₂ or a₁ = b₁
  have ha₁_mem : a₁ ∈ ({a₂, b₁} : Finset ℤ) := by
    rw [← hpair]; exact Finset.mem_insert_self a₁ {b₂}
  rw [Finset.mem_insert, Finset.mem_singleton] at ha₁_mem
  rcases ha₁_mem with rfl | rfl
  · -- Case a₁ = a₂: then b₂ ∈ {a₂, b₁}
    have hb₂_mem : b₂ ∈ ({a₂, b₁} : Finset ℤ) := by
      rw [← hpair]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    rw [Finset.mem_insert, Finset.mem_singleton] at hb₂_mem
    rcases hb₂_mem with rfl | rfl
    · exfalso; exact hne (by omega)  -- a₂ - b₁ = a₂ - a₂ = 0 → b₁ = a₂
    · exact ⟨rfl, rfl⟩
  · -- Case a₁ = b₁: contradicts hne
    exact absurd rfl hne

/-- The number of nonzero differences of a Sidon set A is |A|²-|A|,
    since all pairwise differences are distinct. -/
theorem sidon_diff_count (A : Finset ℤ) (hS : IsSidonSet A) :
  (diffSet A).card = A.card * A.card - A.card + 1 := by
  -- diffSet A = image of A ×ˢ A under subtraction
  -- The off-diagonal pairs map injectively (by sidon_diff_injective)
  -- |A ×ˢ A| = |A|², diagonal has |A| elements, image of diagonal = {0}
  -- So |diffSet A| = |off-diagonal image| + |{0}| = (|A|²-|A|) + 1
  sorry

/-- When differences are disjoint, the combined nonzero differences
    from A and B have cardinality |A|²-|A| + |B|²-|B|. -/
theorem disjoint_diff_total (A B : Finset ℤ)
    (hA : IsSidonSet A) (hB : IsSidonSet B) (hD : DisjointDifferences A B) :
  (diffSet A ∪ diffSet B).card ≥
    A.card * A.card - A.card + B.card * B.card - B.card + 1 := by sorry
