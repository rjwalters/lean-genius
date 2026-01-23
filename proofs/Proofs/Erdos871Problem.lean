/-
  Erdős Problem #871: Partitioning Additive Bases of Order 2

  Source: https://erdosproblems.com/871
  Status: DISPROVED (Larsen 2026)

  Statement:
  Let A be an additive basis of order 2, and suppose r_A(n) → ∞ as n → ∞.
  Can A be partitioned into two disjoint additive bases of order 2?

  Answer: NO

  Background:
  - Erdős-Nathanson (1989): Showed that if we only require r_A(n) ≥ t for all large n
    (for some fixed t), then A cannot necessarily be partitioned into two bases.
  - They also showed partition IS possible when r_A(n) > c log n for some c > (log 4/3)^{-1}

  Counterexample:
  Daniel Larsen (2026) extended the Erdős-Nathanson construction to handle
  the stronger condition r_A(n) → ∞, providing a counterexample to Problem #871.
  The proof was found using AI assistance (Claude Opus 4.5).

  The key insight is a modification of the Erdős-Nathanson strategy that builds
  a basis A with r_A(n) growing to infinity, yet still failing to decompose
  into two disjoint order-2 bases.

  Reference:
  - Erdős, P. & Nathanson, M. (1989). "Partitions of bases into disjoint unions of bases."
  - Larsen, D. (2026). AI-assisted disproof of Erdős Problem #871.
-/

import Mathlib

open Set Filter BigOperators Nat

namespace Erdos871

/-! ## Core Definitions -/

/-- The representation function r_A(n): counts ordered pairs (a,b) ∈ A×A with a + b = n. -/
noncomputable def repFunc (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {n | ∃ a b, a ∈ A ∧ b ∈ A ∧ n = a + b}

notation:65 A " +ₛ " B => sumset A ∪ sumset B

/-- A is an additive basis of order 2 if A + A = ℕ (or misses only finitely many). -/
def IsAdditiveBasis2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset A

/-- Equivalent: A + A covers all but finitely many naturals. -/
def IsAdditiveBasis2' (A : Set ℕ) : Prop :=
  (sumset A)ᶜ.Finite

/-- Two definitions are equivalent. -/
theorem basis2_equiv (A : Set ℕ) : IsAdditiveBasis2 A ↔ IsAdditiveBasis2' A := by
  constructor
  · intro ⟨N₀, h⟩
    have hsub : (sumset A)ᶜ ⊆ Finset.range N₀ := fun n hn => by
      simp only [Set.mem_compl_iff] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      push_neg at h'
      exact hn (h n h')
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  · intro hfin
    by_cases h : (sumset A)ᶜ.Nonempty
    · have hbdd : BddAbove (sumset A)ᶜ := hfin.bddAbove
      let M := sSup (sumset A)ᶜ
      use M + 1
      intro n hn
      by_contra hn'
      have hn_compl : n ∈ (sumset A)ᶜ := hn'
      have h_le : n ≤ M := le_csSup hbdd hn_compl
      omega
    · -- Complement is empty, so sumset A = ℕ
      use 0
      intro n _
      push_neg at h
      have hempty : (sumset A)ᶜ = ∅ := h
      have : sumset A = Set.univ := Set.compl_empty_iff.mp hempty
      rw [this]
      trivial

/-! ## The Condition: r_A(n) → ∞ -/

/-- The representation function tends to infinity. -/
def RepTendsToInfty (A : Set ℕ) : Prop :=
  Tendsto (fun n => (repFunc A n : ℝ)) atTop atTop

/-- Weaker: r_A(n) ≥ t for all large n (for fixed t). -/
def RepEventuallyGe (A : Set ℕ) (t : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, repFunc A n ≥ t

/-- RepTendsToInfty implies RepEventuallyGe for any t.
    Proof: If f(n) → ∞, then eventually f(n) ≥ t for any fixed t. -/
theorem repTendsToInfty_implies_eventuallyGe (A : Set ℕ) (h : RepTendsToInfty A) :
    ∀ t : ℕ, RepEventuallyGe A t := by
  intro t
  -- Unfold the definition of RepTendsToInfty and RepEventuallyGe
  unfold RepTendsToInfty at h
  unfold RepEventuallyGe
  -- Extract the atTop characterization: ∀ b, ∃ N, ∀ n ≥ N, b ≤ f(n)
  rw [Filter.tendsto_atTop_atTop] at h
  -- Apply to t (cast to ℝ)
  obtain ⟨N₀, hN₀⟩ := h (t : ℝ)
  -- Build the witness
  use N₀
  intro n hn
  -- We have (t : ℝ) ≤ (repFunc A n : ℝ), need repFunc A n ≥ t
  have h_le : (t : ℝ) ≤ (repFunc A n : ℝ) := hN₀ n hn
  exact Nat.cast_le.mp h_le

/-! ## Partitions of Bases -/

/-- A set A can be partitioned into two disjoint order-2 bases. -/
def CanPartitionIntoBases (A : Set ℕ) : Prop :=
  ∃ B C : Set ℕ, B ∩ C = ∅ ∧ B ∪ C = A ∧ IsAdditiveBasis2 B ∧ IsAdditiveBasis2 C

/-! ## The Erdős Conjecture (Problem 871) -/

/-- Erdős Problem #871 Conjecture:
    If A is an order-2 basis with r_A(n) → ∞, then A can be partitioned
    into two disjoint order-2 bases. -/
def Erdos871Conjecture : Prop :=
  ∀ A : Set ℕ, IsAdditiveBasis2 A → RepTendsToInfty A → CanPartitionIntoBases A

/-! ## Erdős-Nathanson Weak Version (1989) -/

/-- Erdős-Nathanson (1989): The weaker conjecture (r_A(n) ≥ t for fixed t) is FALSE.
    They constructed a basis A with r_A(n) ≥ t for all large n that cannot be
    partitioned into two disjoint bases. -/
axiom erdos_nathanson_1989 :
  ∀ t : ℕ, ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepEventuallyGe A t ∧ ¬CanPartitionIntoBases A

/-! ## Erdős-Nathanson Positive Result -/

/-- Erdős-Nathanson: Partition IS possible when r_A(n) grows fast enough.
    Specifically, if r_A(n) > c log n for c > (log 4/3)^{-1} ≈ 3.48. -/
axiom erdos_nathanson_positive :
  ∃ c : ℝ, c > 0 ∧ ∀ A : Set ℕ, IsAdditiveBasis2 A →
    (∃ N₀ : ℕ, ∀ n ≥ N₀, (repFunc A n : ℝ) > c * Real.log n) →
    CanPartitionIntoBases A

/-! ## The Counterexample -/

/-- Larsen's counterexample (2026):
    There exists a basis A with r_A(n) → ∞ that cannot be partitioned. -/
axiom larsen_counterexample :
  ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepTendsToInfty A ∧ ¬CanPartitionIntoBases A

/-- Erdős Problem #871 is DISPROVED. -/
theorem erdos_871_disproved : ¬Erdos871Conjecture := by
  intro hconj
  obtain ⟨A, hbasis, hrep, hno_part⟩ := larsen_counterexample
  exact hno_part (hconj A hbasis hrep)

/-! ## Construction Sketch

The Larsen construction modifies the Erdős-Nathanson approach as follows:

**Erdős-Nathanson (1989) Construction:**
- Build A in stages, adding elements to ensure A is a basis
- At each stage, carefully choose elements to ensure r_A(n) ≥ t
- The construction has a "blocking" property that prevents partition

**Larsen Extension (2026):**
- Modify the construction so that r_A(n) grows to infinity
- This requires more careful element selection at each stage
- The key insight: the blocking property can be maintained even as
  representations grow unboundedly

The blocking works roughly as follows:
- For any potential partition B ∪ C = A with B ∩ C = ∅,
- There exist arbitrarily large n such that neither B+B nor C+C contains n
- This contradicts both B and C being order-2 bases
-/

/-- The blocking condition: for any partition of A, some integers fail. -/
def HasBlockingProperty (A : Set ℕ) : Prop :=
  ∀ B C : Set ℕ, B ∩ C = ∅ → B ∪ C = A →
    ∃ᶠ n in atTop, n ∉ sumset B ∨ n ∉ sumset C

/-- A set with the blocking property cannot be partitioned into two bases. -/
theorem blocking_prevents_partition (A : Set ℕ) (h : HasBlockingProperty A) :
    ¬CanPartitionIntoBases A := by
  intro ⟨B, C, hdisjoint, hunion, hB, hC⟩
  obtain ⟨NB, hNB⟩ := hB
  obtain ⟨NC, hNC⟩ := hC
  let N₀ := max NB NC
  -- Get infinitely many n beyond N₀ where one of B+B or C+C fails
  have hblock := h B C hdisjoint hunion
  rw [Filter.Frequently] at hblock
  -- There exists n ≥ N₀ where one fails, contradicting both being bases
  simp only [Filter.eventually_atTop, not_exists, not_forall, not_or] at hblock
  obtain ⟨n, hn_large, hn⟩ := hblock (N₀ + 1)
  -- hn : ¬(n ∈ sumset B) ∨ ¬(n ∈ sumset C) → False
  -- We need to derive a contradiction from the blocking property
  simp only [not_not] at hn
  -- Now hn says both n ∈ sumset B and n ∈ sumset C
  -- But blocking says frequently one fails - contradiction comes from the structure
  -- Actually the blocking property gives us that one must fail
  have hblock' := h B C hdisjoint hunion
  -- Use Filter.Frequently to get concrete witness
  have : ∃ᶠ m in Filter.atTop, m ∉ sumset B ∨ m ∉ sumset C := hblock'
  -- For large enough m ≥ max NB NC, both B and C cover m (since both are bases)
  -- This contradicts the blocking property
  have hcover : ∀ m ≥ N₀, m ∈ sumset B ∧ m ∈ sumset C := fun m hm => by
    constructor
    · exact hNB m (le_trans (le_max_left _ _) hm)
    · exact hNC m (le_trans (le_max_right _ _) hm)
  -- The blocking says infinitely many fail, but after N₀ all succeed - contradiction
  rw [Filter.frequently_atTop] at this
  obtain ⟨m, hm_large, hm_fail⟩ := this N₀
  have ⟨hB_ok, hC_ok⟩ := hcover m hm_large
  cases hm_fail with
  | inl h => exact h hB_ok
  | inr h => exact h hC_ok

/-- The Larsen construction has the blocking property. -/
axiom larsen_construction_blocking :
  ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepTendsToInfty A ∧ HasBlockingProperty A

/-! ## Summary

**Problem Status: DISPROVED**

Erdős Problem #871 asked whether an additive basis A of order 2 with r_A(n) → ∞
can always be partitioned into two disjoint additive bases of order 2.

**Answer: NO** (Larsen 2026)

**Key Results**:
1. Erdős-Nathanson (1989): FALSE for the weaker condition r_A(n) ≥ t (fixed t)
2. Erdős-Nathanson (1989): TRUE when r_A(n) > c log n for large enough c
3. Larsen (2026): FALSE even when r_A(n) → ∞

**The Gap**: The conjecture asked about r_A(n) → ∞, which lies between:
- r_A(n) ≥ t (fixed t) — counterexample exists
- r_A(n) > c log n — partition possible

Larsen showed that r_A(n) → ∞ is not fast enough growth to guarantee partition.

**Technique**:
The proof modifies the Erdős-Nathanson blocking construction to maintain
r_A(n) → ∞ while preserving the partition-blocking property.

References:
- Erdős, P. & Nathanson, M. (1989). "Partitions of bases into disjoint unions of bases."
- Larsen, D. (2026). AI-assisted disproof (Claude Opus 4.5)
-/

end Erdos871
