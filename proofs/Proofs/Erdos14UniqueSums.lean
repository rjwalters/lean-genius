/-
  Erdős Problem #14: Unique Representation Sums

  Source: https://erdosproblems.com/14
  Status: OPEN

  Statement:
  Given A ⊆ ℕ, let B be the set of integers representable in exactly one way
  as a sum of two elements from A (with a ≤ b). Let U(N) = |{1,...,N} \ B|
  count the numbers NOT uniquely representable up to N.

  Two Questions:
  (a) Is U(N) >> N^{1/2-ε} for all ε > 0 and large N?
  (b) Is it possible that U(N) = o(N^{1/2})?

  Known Results:
  - Erdős constructed A where U(N) << N^{1/2+ε} for all large N
  - Yet infinitely many N have U(N) >> N^{1/3-ε}
  - Erdős-Freud: ∃ A ⊆ {1,...,N} with U(N) < 2^{3/2} · N^{1/2}
  - Sidon sets (B₂ sequences) have ALL sums unique, but are sparse

  Connection to Sidon Sets:
  - A Sidon set has the property: a + b = c + d implies {a,b} = {c,d}
  - For Sidon sets, B = A + A (all sums are unique)
  - Sidon sets have size O(N^{1/2}), so they can't cover many sums
  - This problem asks about the "opposite" - maximizing unique sums

  Tags: number-theory, additive-combinatorics, sidon-sets, erdos-problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Erdos14

open Filter Set Real

attribute [local instance] Classical.dec Classical.decPred

/-! ## Part I: Representation Counting -/

/-- Count of ways to write n as a + b with a ≤ b and a, b ∈ A. -/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- The set of sums uniquely representable from A (exactly one way). -/
def uniqueSums (A : Set ℕ) : Set ℕ :=
  {n | repCount A n = 1}

/-- Alternative: using ExistsUnique directly. -/
def uniqueSums' (A : Set ℕ) : Set ℕ :=
  {n | ∃! p : ℕ × ℕ, p.1 ≤ p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {n | ∃ a b, a ∈ A ∧ b ∈ A ∧ n = a + b}

/-- Non-uniquely representable sums: either 0 representations or ≥ 2. -/
def nonUniqueSums (A : Set ℕ) : Set ℕ :=
  sumset A \ uniqueSums A

/-! ## Part II: Counting Functions -/

/-- Count of non-unique sums in {1, ..., N}. -/
noncomputable def nonUniqueCount (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard ((Set.Icc 1 N) \ uniqueSums A)

/-- Alternative: count sums that appear but are NOT unique. -/
noncomputable def multiRepCount (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard ((Set.Icc 1 N) ∩ {n | repCount A n ≥ 2})

/-- Count of sums that don't appear at all. -/
noncomputable def missingCount (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard ((Set.Icc 1 N) \ sumset A)

/-! ## Part III: Sidon Sets (B₂ Sequences) -/

/-- A Sidon set (B₂ sequence): all pairwise sums are distinct.
    Equivalently: a + b = c + d with a ≤ b and c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- For Sidon sets, every sum in A + A is unique. -/
theorem sidon_all_unique (A : Set ℕ) (hS : IsSidon A) :
    sumset A ⊆ uniqueSums A := by
  intro n hn
  obtain ⟨a, b, ha, hb, heq⟩ := hn
  unfold uniqueSums repCount
  simp only [Set.mem_setOf_eq]
  -- Normalize to a ≤ b form
  wlog hab : a ≤ b generalizing a b
  · push_neg at hab
    have hab' : b ≤ a := le_of_lt hab
    have heq' : n = b + a := by omega
    exact this b a hb ha heq' hab'
  -- Now a ≤ b and n = a + b; the set is exactly {(a, b)} by Sidon property
  have hset : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} = {(a, b)} := by
    ext ⟨c, d⟩
    simp only [Set.mem_setOf_eq, Prod.mk.injEq, Set.mem_singleton_iff]
    constructor
    · intro ⟨hcd, hcA, hdA, hsum⟩
      have hsum' : c + d = a + b := by omega
      exact hS c d a b hcA hdA ha hb hcd hab hsum'
    · intro ⟨hc, hd⟩
      subst hc hd
      exact ⟨hab, ha, hb, heq.symm⟩
  rw [hset]
  simp

/-- Sidon sets have size at most O(√N) in {1,...,N}.
    This is a fundamental result in additive combinatorics. -/
axiom sidon_size_bound :
  ∀ A : Set ℕ, IsSidon A → ∀ N : ℕ,
    Set.ncard (A ∩ Set.Icc 1 N) ≤ 2 * Nat.sqrt N

/-! ## Part IV: The Main Questions -/

/-- **Erdős Problem #14a**

    For all ε > 0 and all sets A, is it true that:
    |{1,...,N} \ B| >> N^{1/2 - ε} for large N?

    (Here B = uniqueSums A)

    This asks: can we avoid having many non-unique sums? -/
def erdos_14a : Prop :=
  ∀ A : Set ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
      (nonUniqueCount A N : ℝ) ≥ C * (N : ℝ)^((1:ℝ)/2 - ε)

/-- **Erdős Problem #14b**

    Is it possible to construct A such that:
    |{1,...,N} \ B| = o(N^{1/2})?

    This asks: can non-unique sums grow slower than √N? -/
def erdos_14b : Prop :=
  ∃ A : Set ℕ,
    Tendsto (fun N => (nonUniqueCount A N : ℝ) / Real.sqrt N) atTop (nhds 0)

/-! ### Relationship Between 14a and 14b

**Important Formalization Note:**

The natural intuition is that if 14a holds (lower bound N^{1/2-ε}), then 14b fails
(no o(√N) sets exist). However, with the current formulation where C depends on ε,
this implication is NOT directly provable.

**Analysis:** Consider U(N) = √N / log(N) = o(√N).
For any ε > 0: U(N)/N^{1/2-ε} = N^ε/log(N) → ∞.
So ∃ C > 0 with U(N) ≥ C · N^{1/2-ε} eventually.
This U(N) satisfies BOTH condition_a (for each ε separately) AND condition_b!

**The issue:** erdos_14a allows C to depend on ε, potentially shrinking as ε → 0.
For the implication to hold, we would need a UNIFORM lower bound like:
  ∃ C > 0, ∀ ε > 0, ∀ᶠ N, U(N) ≥ C · N^{1/2-ε}
which is equivalent to: U(N) = Ω(√N).

The original Erdős problem uses "≫" notation which typically means "for some constant
depending on the subscripted parameter" - matching our current formulation.
The two questions (14a and 14b) are genuinely independent as stated. -/

/-- A true contradiction requires a lower bound of Ω(√N).
    If U(N) ≥ C · √N for some C > 0 and all large N, then U(N) ≠ o(√N). -/
theorem omega_sqrt_implies_not_little_o :
    (∀ A : Set ℕ, ∃ C : ℝ, C > 0 ∧
      ∀ᶠ N in atTop, (nonUniqueCount A N : ℝ) ≥ C * Real.sqrt N) →
    ¬erdos_14b := by
  intro h_omega ⟨A, hsmallo⟩
  obtain ⟨C, hC, h_bound⟩ := h_omega A
  -- h_bound: eventually U(N) ≥ C · √N
  -- hsmallo: U(N)/√N → 0
  -- These are directly contradictory for C > 0
  rw [Metric.tendsto_atTop] at hsmallo
  obtain ⟨N₁, hN₁⟩ := hsmallo (C/2) (by linarith)
  rw [Filter.Eventually, Filter.mem_atTop_sets] at h_bound
  obtain ⟨N₂, hN₂⟩ := h_bound
  -- For N ≥ max(N₁, N₂) with N > 0:
  set N := max N₁ N₂ + 1 with hN_def
  have hN1' : N ≥ N₁ := le_trans (le_max_left _ _) (by omega : max N₁ N₂ + 1 ≥ max N₁ N₂)
  have hN2' : N ≥ N₂ := le_trans (le_max_right _ _) (by omega : max N₁ N₂ + 1 ≥ max N₁ N₂)
  specialize hN₁ N hN1'
  have hN₂' : (nonUniqueCount A N : ℝ) ≥ C * Real.sqrt N := by
    simp only [Set.mem_setOf_eq] at hN₂
    exact hN₂ N hN2'
  simp only [dist_zero_right] at hN₁
  have hN_pos : (0 : ℝ) < N := by simp [hN_def]; positivity
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  have h2 : (nonUniqueCount A N : ℝ) / Real.sqrt N < C / 2 := by
    have := hN₁
    rw [Real.norm_of_nonneg] at this
    · exact this
    · apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact le_of_lt hsqrt_pos
  have h3 : (nonUniqueCount A N : ℝ) < C / 2 * Real.sqrt N := by
    have := (div_lt_iff₀ hsqrt_pos).mp h2
    linarith
  -- hN₂': U(N) ≥ C · √N
  -- h3: U(N) < C/2 · √N
  -- Contradiction: C · √N ≤ U(N) < C/2 · √N with C > 0
  have h4 : C * Real.sqrt N < C / 2 * Real.sqrt N := by linarith
  have h5 : C < C / 2 := by
    have hsqrt_ne : Real.sqrt N ≠ 0 := ne_of_gt hsqrt_pos
    calc C = C * Real.sqrt N / Real.sqrt N := by field_simp
      _ < C / 2 * Real.sqrt N / Real.sqrt N := by
        apply div_lt_div_of_pos_right h4 hsqrt_pos
      _ = C / 2 := by field_simp
  linarith

/-! ## Part V: Known Constructions -/

/-- Erdős's construction: there exists A with U(N) << N^{1/2+ε}. -/
axiom erdos_upper_construction :
  ∃ A : Set ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, ∀ᶠ N in atTop,
      (nonUniqueCount A N : ℝ) ≤ C * (N : ℝ)^((1:ℝ)/2 + ε)

/-- For the same A, infinitely many N have U(N) >> N^{1/3-ε}. -/
axiom erdos_lower_infinitely_often :
  ∃ A : Set ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧ ∃ᶠ N in atTop,
      (nonUniqueCount A N : ℝ) ≥ C * (N : ℝ)^((1:ℝ)/3 - ε)

/-- Erdős-Freud: For finite A ⊆ {1,...,N}, can achieve U(N) < 2^{3/2} · √N. -/
axiom erdos_freud_finite :
  ∀ N : ℕ, ∃ A : Set ℕ, A ⊆ Set.Icc 1 N ∧
    (nonUniqueCount A N : ℝ) < 2^(3/2 : ℝ) * Real.sqrt N

/-! ## Part VI: Examples -/

/-- The empty set has no representations. -/
theorem empty_repCount (n : ℕ) : repCount ∅ n = 0 := by
  unfold repCount
  simp only [Set.mem_empty_iff_false, false_and, and_false, Set.setOf_false, Set.ncard_empty]

/-- Singleton set {k}: only 2k has a representation (k + k). -/
theorem singleton_uniqueSums (k : ℕ) :
    uniqueSums {k} = {2 * k} := by
  ext n
  unfold uniqueSums repCount
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    -- If n ≠ 2k, no pair (a, b) with a, b ∈ {k} and a + b = n exists
    by_contra hne
    push_neg at hne
    have hempty : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 = k ∧ p.2 = k ∧ p.1 + p.2 = n} = ∅ := by
      ext ⟨a, b⟩
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨_, ha, hb, hab⟩
      rw [ha, hb] at hab
      omega
    rw [hempty] at h
    simp at h
  · intro hn
    subst hn
    -- When n = 2k, the only pair is (k, k)
    have hset : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 = k ∧ p.2 = k ∧ p.1 + p.2 = 2 * k} = {(k, k)} := by
      ext ⟨a, b⟩
      simp only [Set.mem_setOf_eq, Prod.mk.injEq, Set.mem_singleton_iff]
      constructor
      · intro ⟨_, ha, hb, _⟩
        exact ⟨ha, hb⟩
      · intro ⟨ha, hb⟩
        subst ha hb
        omega
    rw [hset]
    simp

/-- Consecutive integers {1, 2, ..., n} - most sums are NOT unique. -/
theorem consecutive_many_nonunique (n : ℕ) (hn : n ≥ 3) :
    ∃ m, m ∈ sumset (Set.Icc 1 n) ∧ repCount (Set.Icc 1 n) m ≥ 2 := by
  -- For example, 4 = 1 + 3 = 2 + 2 when n ≥ 3
  use 4
  constructor
  · exact ⟨1, 3, by simp [Set.mem_Icc]; omega, by simp [Set.mem_Icc]; omega, rfl⟩
  · -- Show repCount (Icc 1 n) 4 ≥ 2 using pairs (1,3) and (2,2)
    unfold repCount
    have h13 : (1, 3) ∈ {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 ∈ Set.Icc 1 n ∧ p.2 ∈ Set.Icc 1 n ∧ p.1 + p.2 = 4} := by
      simp [Set.mem_Icc]; omega
    have h22 : (2, 2) ∈ {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 ∈ Set.Icc 1 n ∧ p.2 ∈ Set.Icc 1 n ∧ p.1 + p.2 = 4} := by
      simp [Set.mem_Icc]; omega
    have hne : (1, 3) ≠ (2, 2) := by decide
    have hfin : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 ∈ Set.Icc 1 n ∧ p.2 ∈ Set.Icc 1 n ∧ p.1 + p.2 = 4}.Finite := by
      apply Set.Finite.subset
      · exact (Set.finite_Icc 1 n).prod (Set.finite_Icc 1 n)
      · intro ⟨a, b⟩ ⟨_, ha, hb, _⟩
        exact ⟨ha, hb⟩
    calc Set.ncard _ ≥ Set.ncard {(1, 3), (2, 2)} := by
           apply Set.ncard_le_ncard
           · intro x hx
             simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
             rcases hx with rfl | rfl <;> assumption
           · exact hfin
         _ = 2 := by simp [hne]

/-! ## Part VII: Perfect Sidon Sets -/

/-- A set is a perfect Sidon set up to N if it's Sidon and its sumset
    covers many integers up to 2N. -/
def IsPerfectSidon (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    Set.ncard (sumset A ∩ Set.Icc 1 (2 * N)) ≥ N

/-- The existence question: are there near-perfect Sidon sets? -/
def perfectSidonExists : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ᶠ N in atTop,
    ∃ A : Set ℕ, A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
      Set.ncard (sumset A ∩ Set.Icc 1 (2 * N)) ≥ (1 - ε) * N

#check erdos_14a
#check erdos_14b
#check IsSidon
#check uniqueSums

end Erdos14
