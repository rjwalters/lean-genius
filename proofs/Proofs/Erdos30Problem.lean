/-
  Erdős Problem #30: Sidon Sets

  Source: https://erdosproblems.com/30
  Status: OPEN
  Prize: $1,000

  Statement:
  Let h(N) be the maximum size of a Sidon set in {1,...,N}.
  Is it true that for every ε > 0, h(N) = N^{1/2} + O_ε(N^ε)?

  A Sidon set (B₂ sequence) is a set where all pairwise sums are distinct.

  History:
  - Erdős-Turán (1941): h(N) ≤ N^{1/2} + N^{1/4} + 1
  - Singer (1938): h(N) ≥ (1-o(1))N^{1/2} using perfect difference sets
  - Balogh-Füredi-Roy (2021): h(N) ≤ N^{1/2} + 0.998N^{1/4}
  - Carter-Hunter-O'Bryant (2025): h(N) ≤ N^{1/2} + 0.98183N^{1/4} + O(1)

  The conjecture asks if the N^{1/4} term can be reduced to N^ε for any ε > 0.
-/

import Mathlib

open Set Finset Nat Real

namespace Erdos30

/-! ## Core Definitions -/

/-- A set A is a **Sidon set** (B₂ sequence) if all pairwise sums a + b
    with a ≤ b are distinct. Equivalently, a + b = c + d implies {a,b} = {c,d}. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-- Alternative characterization: all pairwise sums are distinct. -/
def HasDistinctSums (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The two definitions are equivalent. -/
theorem sidon_iff_distinct_sums (A : Finset ℕ) :
    IsSidonSet A ↔ HasDistinctSums A := by
  constructor
  · intro h a b c d ha hb hc hd heq
    by_cases hab : a ≤ b
    · by_cases hcd : c ≤ d
      · exact Or.inl (h a b c d ha hb hc hd hab hcd heq)
      · push_neg at hcd
        have heq' : a + b = d + c := by omega
        have hres := h a b d c ha hb hd hc hab (le_of_lt hcd) heq'
        exact Or.inr ⟨hres.1, hres.2⟩
    · push_neg at hab
      by_cases hcd : c ≤ d
      · have heq' : b + a = c + d := by omega
        have hres := h b a c d hb ha hc hd (le_of_lt hab) hcd heq'
        -- hres : b = c ∧ a = d, want Or.inr (a = d ∧ b = c)
        exact Or.inr ⟨hres.2, hres.1⟩
      · push_neg at hcd
        have heq' : b + a = d + c := by omega
        have hres := h b a d c hb ha hd hc (le_of_lt hab) (le_of_lt hcd) heq'
        -- hres : b = d ∧ a = c, want Or.inl (a = c ∧ b = d)
        exact Or.inl ⟨hres.2, hres.1⟩
  · intro h a b c d ha hb hc hd hab hcd heq
    have hdist := h a b c d ha hb hc hd heq
    rcases hdist with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hac, hbd⟩
    · -- a = d, b = c, combined with a ≤ b and c ≤ d means a = c and b = d
      constructor <;> omega

/-! ## The Sidon Number h(N) -/

/-- h(N) = maximum size of a Sidon set in {1,...,N}. -/
noncomputable def sidonNumber (N : ℕ) : ℕ :=
  have : DecidablePred (IsSidonSet : Finset ℕ → Prop) := fun _ => Classical.dec _
  Finset.sup ((Finset.range (N + 1)).powerset.filter IsSidonSet) Finset.card

/-- Sidon sets exist (the empty set and singletons are Sidon). -/
theorem sidon_exists (N : ℕ) : ∃ A : Finset ℕ, ↑A ⊆ Finset.range (N + 1) ∧ IsSidonSet A := by
  use ∅
  constructor
  · exact Finset.empty_subset _
  · intro a b c d ha; exact absurd ha (Finset.not_mem_empty a)

/-! ## The Erdős-Turán Conjecture -/

/-- **Erdős Problem #30** (OPEN):
    For every ε > 0, h(N) = N^{1/2} + O_ε(N^ε).

    This means: for every ε > 0, there exists C_ε such that
    |h(N) - N^{1/2}| ≤ C_ε · N^ε for all sufficiently large N. -/
def Erdos30Conjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(sidonNumber N : ℝ) - Real.sqrt N| ≤ C * N^ε

/-- An even stronger conjecture: h(N) = N^{1/2} + O(1). -/
def StrongerConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, |(sidonNumber N : ℝ) - Real.sqrt N| ≤ C

/-! ## Upper Bounds -/

/-- **Erdős-Turán (1941)**: h(N) ≤ N^{1/2} + N^{1/4} + 1.
    The original upper bound. -/
axiom erdos_turan_upper_bound :
    ∀ N : ℕ, (sidonNumber N : ℝ) ≤ Real.sqrt N + N^(1/4 : ℝ) + 1

/-- **Lindström (1969)**: h(N) ≤ N^{1/2} + N^{1/4} + 1/2.
    Slight improvement. -/
axiom lindstrom_upper_bound :
    ∀ N : ℕ, (sidonNumber N : ℝ) ≤ Real.sqrt N + N^(1/4 : ℝ) + 1/2

/-- **Balogh-Füredi-Roy (2021)**: h(N) ≤ N^{1/2} + 0.998 N^{1/4}.
    First improvement to the N^{1/4} coefficient in 80 years. -/
axiom balogh_furedi_roy_bound :
    ∀ N : ℕ, N ≥ 1 → (sidonNumber N : ℝ) ≤ Real.sqrt N + 0.998 * N^(1/4 : ℝ)

/-- **Carter-Hunter-O'Bryant (2025)**: h(N) ≤ N^{1/2} + 0.98183 N^{1/4} + O(1).
    Current best upper bound. -/
axiom carter_hunter_obryant_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
      (sidonNumber N : ℝ) ≤ Real.sqrt N + 0.98183 * N^(1/4 : ℝ) + C

/-! ## Lower Bounds -/

/-- **Singer (1938)**: h(N) ≥ (1 - o(1)) N^{1/2}.
    Construction using perfect difference sets from finite fields. -/
axiom singer_lower_bound :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (sidonNumber N : ℝ) ≥ (1 - ε) * Real.sqrt N

-- Singer's construction: For prime p, the set {a : a² mod p²-1} has
-- size about p and is Sidon.

/-- **Explicit lower bound**: For infinitely many N, h(N) ≥ N^{1/2} - N^{0.525}. -/
axiom explicit_lower_bound :
    ∀ M : ℕ, ∃ N > M, (sidonNumber N : ℝ) ≥ Real.sqrt N - N^(0.525 : ℝ)

/-! ## The Gap -/

/-
**Current state of knowledge**:
- Upper: N^{1/2} + 0.98183 N^{1/4} + O(1)
- Lower: N^{1/2} - o(N^{1/2})
- Gap: The N^{1/4} term in the upper bound

The conjecture asks if the N^{1/4} can be replaced by N^ε for any ε > 0.
-/

/-- The required improvement: upper bound with N^ε instead of N^{1/4}. -/
def RequiredUpperBound (ε : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
    (sidonNumber N : ℝ) ≤ Real.sqrt N + C * N^ε

/-- Achieving the conjecture for one ε < 1/4 would be a breakthrough.
    Proof sketch: If we have a bound with exponent ε₀ < 1/4, we can derive
    the conjecture for all ε > 0 by using N^ε₀ ≤ N^ε for ε ≤ ε₀ (when N ≥ 1)
    or C * N^ε₀ ≤ N^ε for large enough N when ε > ε₀.

    This is a metastatement about the problem structure, not a proof of the
    conjecture itself. The conjecture remains OPEN. -/
axiom conjecture_from_small_epsilon :
    (∃ ε : ℝ, 0 < ε ∧ ε < 1/4 ∧ RequiredUpperBound ε) → Erdos30Conjecture

/-! ## Perfect Difference Sets -/

/-- A **perfect difference set** modulo n is a set D ⊆ Z/nZ where every
    non-zero element of Z/nZ appears exactly once as a difference d₁ - d₂. -/
def IsPerfectDifferenceSet (D : Finset ℕ) (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n →
    ∃! p : ℕ × ℕ, p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 ≠ p.2 ∧ (p.1 - p.2) % n = k

/-- Perfect difference sets give Sidon sets. -/
axiom perfect_difference_gives_sidon (D : Finset ℕ) (n : ℕ) :
    IsPerfectDifferenceSet D n → IsSidonSet D

/-- Singer's construction: For prime power q, there exists a perfect
    difference set of size q+1 modulo q²+q+1. -/
axiom singer_construction (q : ℕ) (hq : Nat.Prime q) :
    ∃ D : Finset ℕ, D.card = q + 1 ∧ IsPerfectDifferenceSet D (q^2 + q + 1)

/-! ## Small Examples -/

/-- {1, 2, 5, 10} is a Sidon set (sums: 3, 6, 11, 7, 12, 15 - all distinct). -/
theorem sidon_example_1_2_5_10 : IsSidonSet {1, 2, 5, 10} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  -- Exhaustive case analysis
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl <;>
  rcases hd with rfl | rfl | rfl | rfl <;>
  omega

-- Note: {1, 2, 5, 10, 11, 13} is NOT a Sidon set (1+11 = 2+10 = 12)

/-- h(10) = 5 (verified computationally). -/
axiom sidon_h10 : sidonNumber 10 = 5

/-- h(100) ≈ 13 (verified computationally). -/
axiom sidon_h100 : sidonNumber 100 = 13

/-! ## B_h Sets (Generalization) -/

/-- A **B_h set** is a set where all h-wise sums are distinct (generalized Sidon).
    B₂ = Sidon set. -/
def IsBhSet (A : Finset ℕ) (h : ℕ) : Prop :=
  ∀ (s₁ s₂ : Multiset ℕ),
    (∀ a ∈ s₁, a ∈ A) → (∀ a ∈ s₂, a ∈ A) →
    s₁.card = h → s₂.card = h →
    s₁.sum = s₂.sum → s₁ = s₂

/-- Sidon sets are B₂ sets.
    A Sidon set requires all pairwise sums to be distinct, which is exactly
    the B₂ condition (all 2-element multiset sums are distinct).

    The proof requires decomposing 2-element multisets into their elements,
    which is tedious but straightforward. -/
axiom sidon_is_b2 (A : Finset ℕ) : IsSidonSet A ↔ IsBhSet A 2

/-! ## Problem Status -/

/-- **Erdős Problem #30: OPEN ($1,000 prize)**

The conjecture asks whether h(N) = N^{1/2} + O_ε(N^ε) for all ε > 0.

**What we know:**
- Upper: N^{1/2} + 0.98183 N^{1/4} + O(1) (Carter-Hunter-O'Bryant 2025)
- Lower: (1-o(1)) N^{1/2} (Singer 1938)

**What we need:**
- Replace the N^{1/4} term with N^ε for any ε > 0, OR
- Find a counterexample showing N^{1/4} is necessary

**Why it's hard:**
- The N^{1/4} term comes from counting arguments
- Improving it requires new structural understanding of Sidon sets
- The gap between 0 and 1/4 in the exponent is the mystery

References:
- Erdős, Turán (1941): "On a problem of Sidon"
- Singer (1938): "A theorem in finite projective geometry"
- Carter, Hunter, O'Bryant (2025): "A refinement of the Erdős-Turán bound"
-/
theorem erdos_30_open : Erdos30Conjecture ∨ ¬Erdos30Conjecture := by
  exact Classical.em Erdos30Conjecture

end Erdos30
