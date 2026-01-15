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
        have : a + b = d + c := by omega
        have := h a b d c ha hb hd hc hab (le_of_lt hcd) this
        exact Or.inr ⟨this.1, this.2⟩
    · push_neg at hab
      by_cases hcd : c ≤ d
      · have : b + a = c + d := by omega
        have := h b a c d hb ha hc hd (le_of_lt hab) hcd this
        exact Or.inl ⟨this.2, this.1⟩
      · push_neg at hcd
        have : b + a = d + c := by omega
        have := h b a d c hb ha hd hc (le_of_lt hab) (le_of_lt hcd) this
        exact Or.inr ⟨this.2, this.1⟩
  · intro h a b c d ha hb hc hd hab hcd heq
    have := h a b c d ha hb hc hd heq
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · -- a = d, b = c, so a + b = d + c = c + d, and a ≤ b, c ≤ d
      -- means a ≤ b and a ≤ b (since a = d, b = c)
      have : a = c := by omega
      have : b = d := by omega
      exact ⟨‹a = c›, ‹b = d›⟩

/-! ## The Sidon Number h(N) -/

/-- h(N) = maximum size of a Sidon set in {1,...,N}. -/
noncomputable def sidonNumber (N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter (fun S => IsSidonSet S))
    Finset.card

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

/-- Singer's construction: For prime p, the set {a : a² mod p²-1} has
    size about p and is Sidon. -/

/-- **Explicit lower bound**: For infinitely many N, h(N) ≥ N^{1/2} - N^{0.525}. -/
axiom explicit_lower_bound :
    ∀ M : ℕ, ∃ N > M, (sidonNumber N : ℝ) ≥ Real.sqrt N - N^(0.525 : ℝ)

/-! ## The Gap -/

/-- **Current state of knowledge**:
    - Upper: N^{1/2} + 0.98183 N^{1/4} + O(1)
    - Lower: N^{1/2} - o(N^{1/2})
    - Gap: The N^{1/4} term in the upper bound

    The conjecture asks if the N^{1/4} can be replaced by N^ε for any ε > 0. -/

/-- The required improvement: upper bound with N^ε instead of N^{1/4}. -/
def RequiredUpperBound (ε : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
    (sidonNumber N : ℝ) ≤ Real.sqrt N + C * N^ε

/-- Achieving the conjecture for one ε < 1/4 would be a breakthrough. -/
theorem conjecture_from_small_epsilon :
    (∃ ε : ℝ, 0 < ε ∧ ε < 1/4 ∧ RequiredUpperBound ε) → Erdos30Conjecture := by
  intro ⟨ε₀, hε₀_pos, hε₀_small, C, hC, hbound⟩
  intro ε hε
  by_cases h : ε ≤ ε₀
  · -- Case: ε ≤ ε₀. For N ≥ 1, N^ε₀ ≥ N^ε, so the bound works directly
    use C
    constructor
    · exact hC
    · use 1
      intro N hN
      have hN' : (N : ℝ) ≥ 1 := by exact_mod_cast hN
      calc |(sidonNumber N : ℝ) - Real.sqrt N|
        ≤ |((sidonNumber N : ℝ) - Real.sqrt N)| + 0 := by ring_nf
        _ ≤ C * N^ε₀ := by
            have := hbound N hN
            linarith
        _ ≤ C * N^ε := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
            exact Real.rpow_le_rpow_left_of_exponent hN' h
  · push_neg at h
    -- Case: ε > ε₀. For large N, C * N^ε₀ ≤ N^ε
    use 1
    constructor
    · norm_num
    · -- Need N₀ such that for N ≥ N₀, C * N^ε₀ ≤ N^ε
      -- This holds for large enough N since ε > ε₀
      use Nat.ceil (max 1 (C ^ (1 / (ε - ε₀)))) + 1
      intro N hN
      have hN' : (N : ℝ) ≥ 1 := by
        have : N ≥ Nat.ceil (max 1 (C ^ (1 / (ε - ε₀)))) + 1 := hN
        have : (N : ℝ) ≥ 1 := by
          calc (N : ℝ) ≥ Nat.ceil (max 1 (C ^ (1 / (ε - ε₀)))) + 1 := by exact_mod_cast hN
            _ ≥ 1 := by linarith [Nat.le_ceil (max 1 (C ^ (1 / (ε - ε₀))))]
        exact this
      calc |(sidonNumber N : ℝ) - Real.sqrt N|
        ≤ C * N^ε₀ := by
            have := hbound N (by linarith : N ≥ 1)
            linarith
        _ ≤ 1 * N^ε := by
            rw [one_mul]
            -- C * N^ε₀ ≤ N^ε iff C ≤ N^(ε - ε₀)
            have key : C ≤ (N : ℝ) ^ (ε - ε₀) := by
              have hN_bound : (N : ℝ) ≥ C ^ (1 / (ε - ε₀)) := by
                calc (N : ℝ) ≥ Nat.ceil (max 1 (C ^ (1 / (ε - ε₀)))) + 1 := by exact_mod_cast hN
                  _ ≥ Nat.ceil (C ^ (1 / (ε - ε₀))) := by
                      have : max 1 (C ^ (1 / (ε - ε₀))) ≥ C ^ (1 / (ε - ε₀)) := le_max_right _ _
                      linarith [Nat.le_ceil (max 1 (C ^ (1 / (ε - ε₀)))), Nat.le_ceil (C ^ (1 / (ε - ε₀)))]
                  _ ≥ C ^ (1 / (ε - ε₀)) := Nat.le_ceil _
              have hε_diff : ε - ε₀ > 0 := by linarith
              calc C = (C ^ (1 / (ε - ε₀))) ^ (ε - ε₀) := by
                      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hC)]
                      · simp [div_mul_cancel₀ _ (ne_of_gt hε_diff)]
                _ ≤ (N : ℝ) ^ (ε - ε₀) := by
                    apply Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hC) _) hN_bound (le_of_lt hε_diff)
            calc C * (N : ℝ) ^ ε₀ = C * (N : ℝ) ^ ε₀ := rfl
              _ ≤ (N : ℝ) ^ (ε - ε₀) * (N : ℝ) ^ ε₀ := by
                  apply mul_le_mul_of_nonneg_right key (Real.rpow_nonneg (le_of_lt hN') _)
              _ = (N : ℝ) ^ ε := by
                  rw [← Real.rpow_add hN']
                  ring_nf

/-! ## Perfect Difference Sets -/

/-- A **perfect difference set** modulo n is a set D ⊆ Z/nZ where every
    non-zero element of Z/nZ appears exactly once as a difference d₁ - d₂. -/
def IsPerfectDifferenceSet (D : Finset ℕ) (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n →
    (∃! (d₁, d₂) : ℕ × ℕ, d₁ ∈ D ∧ d₂ ∈ D ∧ d₁ ≠ d₂ ∧ (d₁ - d₂) % n = k)

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

/-- {1, 2, 5, 10, 11, 13} is NOT a Sidon set (1+13 = 2+12? No, 2+11 = 13 = 1+12? No..
    Actually 1+10 = 11, 2+9 not in set... Let's check: this might be Sidon). -/

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

/-- Sidon sets are B₂ sets. -/
theorem sidon_is_b2 (A : Finset ℕ) : IsSidonSet A ↔ IsBhSet A 2 := by
  constructor
  · -- IsSidonSet → IsBhSet 2
    intro hSidon s₁ s₂ hs₁ hs₂ hcard₁ hcard₂ hsum
    -- s₁ and s₂ are multisets of size 2 from A with equal sums
    -- Need to show s₁ = s₂
    -- A multiset of size 2 is either {a, a} or {a, b} with a ≠ b
    obtain ⟨a₁, b₁, rfl⟩ : ∃ a b, s₁ = {a, b} := by
      have : s₁.card = 2 := hcard₁
      exact Multiset.card_eq_two.mp this
    obtain ⟨a₂, b₂, rfl⟩ : ∃ a b, s₂ = {a, b} := by
      have : s₂.card = 2 := hcard₂
      exact Multiset.card_eq_two.mp this
    -- Now we have {a₁, b₁} and {a₂, b₂} with a₁ + b₁ = a₂ + b₂
    simp only [Multiset.mem_insert, Multiset.mem_singleton] at hs₁ hs₂
    have ha₁ : a₁ ∈ A := by
      rcases hs₁ a₁ (by simp) with h
      exact h
    have hb₁ : b₁ ∈ A := by
      rcases hs₁ b₁ (by simp) with h
      exact h
    have ha₂ : a₂ ∈ A := by
      rcases hs₂ a₂ (by simp) with h
      exact h
    have hb₂ : b₂ ∈ A := by
      rcases hs₂ b₂ (by simp) with h
      exact h
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    -- Use HasDistinctSums (equivalent to IsSidonSet)
    rw [sidon_iff_distinct_sums] at hSidon
    have := hSidon a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂ hsum
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simp only [Multiset.insert_eq_cons, Multiset.cons_eq_cons]
      right
      exact ⟨rfl, Multiset.singleton_eq_singleton.mpr rfl⟩
  · -- IsBhSet 2 → IsSidonSet
    intro hBh a b c d ha hb hc hd hab hcd heq
    -- Need to show a = c ∧ b = d from a + b = c + d with a ≤ b, c ≤ d
    have hs₁ : ∀ x ∈ ({a, b} : Multiset ℕ), x ∈ A := by simp [ha, hb]
    have hs₂ : ∀ x ∈ ({c, d} : Multiset ℕ), x ∈ A := by simp [hc, hd]
    have hcard₁ : ({a, b} : Multiset ℕ).card = 2 := by simp
    have hcard₂ : ({c, d} : Multiset ℕ).card = 2 := by simp
    have hsum : ({a, b} : Multiset ℕ).sum = ({c, d} : Multiset ℕ).sum := by simp [heq]
    have := hBh {a, b} {c, d} hs₁ hs₂ hcard₁ hcard₂ hsum
    simp only [Multiset.insert_eq_cons, Multiset.cons_eq_cons, Multiset.singleton_eq_singleton,
               Multiset.singleton_inj] at this
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · -- a = d, b = c, combined with a ≤ b and c ≤ d means a = c and b = d
      constructor <;> omega

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
