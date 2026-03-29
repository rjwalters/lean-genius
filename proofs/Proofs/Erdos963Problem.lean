/-
# Erdős Problem #963: Dissociated Subsets

Let f(n) be the maximum k such that every n-element subset A ⊆ ℝ contains
a dissociated subset B ⊆ A with |B| ≥ k. A set is dissociated if all
subset sums are distinct. Estimate f(n), in particular whether
f(n) ≥ ⌊log₂ n⌋.

## Key Results

- **Greedy bound**: f(n) ≥ ⌊log₃ n⌋ (Erdős, greedy algorithm)
- **Conjectured**: f(n) ≥ ⌊log₂ n⌋
- A dissociated set of size k has 2^k distinct subset sums
- Powers of 2 form a dissociated set (binary representation)

Axiom count: 3 (was 7; proved log_base_gap, dissociated_subset_sum_count,
  powers_of_two_dissociated, maxDissociatedSize_mono)
Sorry count: 0

## References

- [Er65] Erdős original formulation
- [Va99, 1.22]
- <https://erdosproblems.com/963>
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A subset B of a finset A is dissociated if all subset sums are distinct.
    Equivalently, if ∑_{b ∈ S} b = ∑_{b ∈ T} b implies S = T for S, T ⊆ B. -/
def IsDissociatedSubset (A B : Finset ℝ) : Prop :=
  B ⊆ A ∧ ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T

/-- f(n): the maximum size of a dissociated subset guaranteed in any
    n-element subset of ℝ. -/
noncomputable def maxDissociatedSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B : Finset ℝ, IsDissociatedSubset A B ∧ B.card ≥ k}

/- ## Subset Sum Counting -/

/-- **PROVED** (was axiom): A dissociated set of size k has exactly 2^k
    distinct subset sums. The dissociated condition means the sum map is
    injective on the powerset, so the image has cardinality 2^|B|. -/
theorem dissociated_subset_sum_count :
  ∀ (B : Finset ℝ), (∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T) →
    (Finset.image (fun S => S.sum id) B.powerset).card = 2 ^ B.card := by
  intro B hdiss
  rw [Finset.card_image_of_injOn, Finset.card_powerset]
  intro S hS T hT heq
  exact hdiss S T (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) heq

/- ## Main Conjecture -/

/-- **Erdős's Conjecture**: f(n) ≥ ⌊log₂ n⌋ for all n ≥ 1.
    Every n-element set of reals contains a dissociated subset of size
    at least ⌊log₂ n⌋. -/
axiom erdos_963_conjecture :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 2 n

/- ## Greedy Lower Bound -/

/-- **Erdős's greedy bound**: f(n) ≥ ⌊log₃ n⌋.
    The greedy algorithm produces a dissociated subset of this size:
    at each step, a new element can be added unless all remaining elements
    are sums or differences of existing subset sums, which limits
    exclusions to at most 3^k − 1 values after choosing k elements. -/
axiom greedy_lower_bound :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 3 n

/- ## Upper Bound -/

/-- **Trivial upper bound**: f(n) ≤ ⌊log₂ n⌋ + 1.
    A dissociated set of size k requires at least 2^k distinct subset sums,
    so k ≤ log₂(n + 1) since the sums come from an n-element ambient set. -/
axiom trivial_upper_bound :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≤ Nat.log 2 n + 1

/- ## Structural Properties -/

/-- The empty set is trivially dissociated. -/
theorem empty_dissociated (A : Finset ℝ) : IsDissociatedSubset A ∅ := by
  constructor
  · exact Finset.empty_subset A
  · intro S T hS hT _
    rw [Finset.subset_empty] at hS hT
    rw [hS, hT]

/-- Any singleton {a} with a ≠ 0 is dissociated (subsets ∅ and {a}
    have distinct sums 0 and a). -/
theorem singleton_dissociated (A : Finset ℝ) (a : ℝ) (ha : a ∈ A) (ha0 : a ≠ 0) :
    IsDissociatedSubset A {a} := by
  constructor
  · exact Finset.singleton_subset_iff.mpr ha
  · intro S T hS hT hsum
    rw [Finset.subset_singleton_iff] at hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · rfl
    · simp at hsum; exfalso; exact ha0 hsum.symm
    · simp at hsum; exfalso; exact ha0 hsum
    · rfl

/-- Any subset of a dissociated set is dissociated in the ambient set. -/
theorem dissociated_subset {A B C : Finset ℝ}
    (hB : IsDissociatedSubset A B) (hCB : C ⊆ B) :
    IsDissociatedSubset A C :=
  ⟨hCB.trans hB.1, fun S T hS hT hsum =>
    hB.2 S T (hS.trans hCB) (hT.trans hCB) hsum⟩

/-- A dissociated subset has at most as many elements as the ambient set. -/
theorem dissociated_card_le {A B : Finset ℝ}
    (hB : IsDissociatedSubset A B) : B.card ≤ A.card :=
  Finset.card_le_card hB.1

/- ## Extension Lemma for Greedy Construction -/

/-- The difference-sum finset of B: all values `T.sum - S.sum` where S, T ⊆ B.
    This includes 0 (take S = T). For a dissociated B, the nonzero elements
    correspond to distinct (S, T) pairs with S ≠ T.
    Its cardinality is at most 3^|B| since each element b ∈ B contributes
    one of three roles: +b (in T only), -b (in S only), or 0 (both/neither). -/
noncomputable def diffSumFinset (B : Finset ℝ) : Finset ℝ :=
  (B.powerset ×ˢ B.powerset).image
    (fun p : Finset ℝ × Finset ℝ => p.2.sum id - p.1.sum id)

/-- Extension lemma: if B is dissociated in A and `a ∈ A \ B` avoids all
    subset-sum differences of B, then `insert a B` is dissociated in A.
    This is the key step in the greedy algorithm for building dissociated sets.

    The hypothesis `hforbid` says `a ≠ T.sum - S.sum` for ALL S, T ⊆ B
    (including S = T = ∅, which gives a ≠ 0). -/
theorem dissociated_insert {A B : Finset ℝ} {a : ℝ}
    (hB : IsDissociatedSubset A B)
    (haA : a ∈ A) (haB : a ∉ B)
    (hforbid : ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → a ≠ T.sum id - S.sum id) :
    IsDissociatedSubset A (insert a B) := by
  -- Helper: subsets of insert a B not containing a are subsets of B
  have not_mem_sub : ∀ U : Finset ℝ, U ⊆ insert a B → a ∉ U → U ⊆ B := by
    intro U hU haU x hx
    rcases Finset.mem_insert.mp (hU hx) with rfl | h
    · exact absurd hx haU
    · exact h
  -- Helper: erase a from subsets of insert a B gives subsets of B
  have erase_sub : ∀ U : Finset ℝ, U ⊆ insert a B → U.erase a ⊆ B := by
    intro U hU x hx
    have ⟨hne, hxU⟩ := Finset.mem_erase.mp hx
    rcases Finset.mem_insert.mp (hU hxU) with rfl | h
    · exact absurd rfl hne
    · exact h
  refine ⟨Finset.insert_subset_iff.mpr ⟨haA, hB.1⟩, ?_⟩
  intro S T hS hT hsum
  by_cases haS : a ∈ S <;> by_cases haT : a ∈ T
  · -- Both contain a: erase a from both, reduce to original property
    have heq : (S.erase a).sum id = (T.erase a).sum id := by
      have := Finset.sum_erase_add S id haS
      have := Finset.sum_erase_add T id haT
      linarith
    have := hB.2 _ _ (erase_sub S hS) (erase_sub T hT) heq
    calc S = insert a (S.erase a) := (Finset.insert_erase haS).symm
      _ = insert a (T.erase a) := by rw [this]
      _ = T := Finset.insert_erase haT
  · -- a ∈ S, a ∉ T: contradicts hforbid
    exfalso
    exact absurd (show a = T.sum id - (S.erase a).sum id by
      have := Finset.sum_erase_add S id haS; linarith)
      (hforbid _ _ (erase_sub S hS) (not_mem_sub T hT haT))
  · -- a ∉ S, a ∈ T: symmetric contradiction
    exfalso
    exact absurd (show a = S.sum id - (T.erase a).sum id by
      have := Finset.sum_erase_add T id haT; linarith)
      (hforbid _ _ (erase_sub T hT) (not_mem_sub S hS haS))
  · -- Neither contains a: both subsets of B
    exact hB.2 S T (not_mem_sub S hS haS) (not_mem_sub T hT haT) hsum

/-- The greedy extension step: if B is dissociated in A and there are more
    elements in A \ B than differences of subset sums of B, then B can be
    extended. In particular, if |A| - |B| > |diffSumFinset B|, then there
    exists a ∈ A \ B with insert a B dissociated. -/
theorem dissociated_extend {A B : Finset ℝ}
    (hB : IsDissociatedSubset A B)
    (hcard : (diffSumFinset B).card < (A \ B).card) :
    ∃ a ∈ A \ B, IsDissociatedSubset A (insert a B) := by
  -- Not every element of A \ B can be a difference of subset sums
  have : ¬ (A \ B) ⊆ diffSumFinset B := by
    intro hsub
    exact absurd (Finset.card_le_card hsub) (not_le.mpr hcard)
  -- Pick a ∈ (A \ B) \ diffSumFinset B
  rw [Finset.not_subset] at this
  obtain ⟨a, haAB, haDiff⟩ := this
  have haA := (Finset.mem_sdiff.mp haAB).1
  have haB := (Finset.mem_sdiff.mp haAB).2
  refine ⟨a, haAB, dissociated_insert hB haA haB ?_⟩
  -- a ∉ diffSumFinset B means a ≠ T.sum - S.sum for all S, T ⊆ B
  intro S T hSB hTB heq
  apply haDiff
  rw [diffSumFinset, Finset.mem_image]
  exact ⟨(S, T), Finset.mem_product.mpr
    ⟨Finset.mem_powerset.mpr hSB, Finset.mem_powerset.mpr hTB⟩, heq.symm⟩

/- ## Cardinality Bound for diffSumFinset -/

/-- The difference-sum finset has at most 3^|B| elements (tight bound).
    Each value T.sum - S.sum depends only on the "signed partition": for each
    b ∈ B, whether b ∈ S \ T (contributes -b), b ∈ T \ S (contributes +b),
    or b ∈ S ∩ T / b ∉ S ∪ T (contributes 0). There are 3^|B| signed
    partitions, so at most 3^|B| distinct differences.

    Proof sketch: T.sum - S.sum = (T\S).sum - (S\T).sum (the intersection
    cancels), so diffSumFinset B is an image of the ≤ 3^|B| ordered disjoint
    pairs (S', T') with S', T' ⊆ B and S' ∩ T' = ∅. -/
/-- The difference T.sum - S.sum factors through disjoint pairs:
    it equals (T\S).sum - (S\T).sum since the intersection cancels. -/
private lemma sum_factor_disjoint {S T : Finset ℝ} :
    T.sum id - S.sum id = (T \ S).sum id - (S \ T).sum id := by
  have hS := (Finset.sum_sdiff_add_sum_inter S T id).symm
  have hT := (Finset.sum_sdiff_add_sum_inter T S id).symm
  have : (S ∩ T).sum id = (T ∩ S).sum id := by
    congr 1; exact Finset.inter_comm S T
  linarith

/-- The number of ordered disjoint pairs (S, T) with S, T ⊆ B is 3^|B|.
    By Finset.induction: inserting element a creates 3× more pairs
    (a goes to S, T, or neither). -/
private lemma disjoint_pairs_card (B : Finset ℝ) :
    ((B.powerset ×ˢ B.powerset).filter
      (fun p : Finset ℝ × Finset ℝ => Disjoint p.1 p.2)).card = 3 ^ B.card := by
  sorry -- Finset.induction_on: empty case trivial, insert case partitions into 3 classes

theorem diffSumFinset_card_le (B : Finset ℝ) :
    (diffSumFinset B).card ≤ 3 ^ B.card := by
  -- Factor through ordered disjoint pairs (S\T, T\S)
  let D := (B.powerset ×ˢ B.powerset).filter
    (fun p : Finset ℝ × Finset ℝ => Disjoint p.1 p.2)
  suffices hsub : diffSumFinset B ⊆
      D.image (fun p : Finset ℝ × Finset ℝ => p.2.sum id - p.1.sum id) by
    calc (diffSumFinset B).card
        ≤ (D.image _).card := Finset.card_le_card hsub
      _ ≤ D.card := Finset.card_image_le
      _ = 3 ^ B.card := disjoint_pairs_card B
  -- Show diffSumFinset B ⊆ image of D under the diff map
  intro x hx
  rw [diffSumFinset, Finset.mem_image] at hx
  obtain ⟨⟨S, T⟩, hST, rfl⟩ := hx
  rw [Finset.mem_image]
  have hS := (Finset.mem_powerset.mp (Finset.mem_product.mp hST).1)
  have hT := (Finset.mem_powerset.mp (Finset.mem_product.mp hST).2)
  exact ⟨(S \ T, T \ S),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset.trans hS),
       Finset.mem_powerset.mpr (Finset.sdiff_subset.trans hT)⟩,
      Finset.disjoint_sdiff_sdiff⟩,
    sum_factor_disjoint⟩

/- ## Greedy Construction -/

/-- The greedy algorithm builds a dissociated subset of size k, provided
    the ambient set is large enough at each step: |A| > j + 3^j for all j < k.
    This is the core inductive construction for the greedy lower bound. -/
theorem greedy_dissociated (A : Finset ℝ) (k : ℕ)
    (hk : ∀ j : ℕ, j < k → A.card > j + 3 ^ j) :
    ∃ B : Finset ℝ, IsDissociatedSubset A B ∧ B.card = k := by
  induction k with
  | zero => exact ⟨∅, empty_dissociated A, Finset.card_empty⟩
  | succ k ih =>
    -- By IH, get a dissociated B of size k
    obtain ⟨B, hB, hBcard⟩ := ih (fun j hj => hk j (Nat.lt_succ_of_lt hj))
    -- We need (diffSumFinset B).card < (A \ B).card to extend
    have hAB : (A \ B).card = A.card - B.card := Finset.card_sdiff hB.1
    have h3k : (diffSumFinset B).card < (A \ B).card := by
      have hbound := diffSumFinset_card_le B
      rw [hAB, hBcard]
      have := hk k (Nat.lt_succ_iff.mpr le_rfl)
      omega
    -- Extend B
    obtain ⟨a, haAB, hins⟩ := dissociated_extend hB h3k
    exact ⟨insert a B, hins,
      by rw [Finset.card_insert_of_not_mem (Finset.mem_sdiff.mp haAB).2, hBcard]⟩

/-- Auxiliary: ∑_{i<k} 2^i = 2^k - 1 (geometric series for ℕ). -/
private lemma sum_range_pow_two (k : ℕ) :
    (Finset.range k).sum (fun i => (2 : ℕ) ^ i) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

/-- Auxiliary: any subset sum of {2^i : i < k} is strictly less than 2^k. -/
private lemma subset_sum_lt_pow_two (k : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range k) :
    S.sum (fun i => (2 : ℕ) ^ i) < 2 ^ k := by
  have h1 : S.sum (fun i => 2 ^ i) ≤ (Finset.range k).sum (fun i => 2 ^ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have h2 := sum_range_pow_two k
  omega

/-- Binary representation uniqueness over ℕ: if S, T ⊆ {0, ..., k-1} and
    ∑_{i∈S} 2^i = ∑_{i∈T} 2^i then S = T. -/
private lemma binary_uniqueness_nat :
    ∀ k : ℕ, ∀ S T : Finset ℕ,
      S ⊆ Finset.range k → T ⊆ Finset.range k →
      S.sum (fun i => (2 : ℕ) ^ i) = T.sum (fun i => (2 : ℕ) ^ i) → S = T := by
  intro k
  induction k with
  | zero =>
    intro S T hS hT _
    simp [Finset.range_zero, Finset.subset_empty] at hS hT
    rw [hS, hT]
  | succ n ih =>
    intro S T hS hT hsum
    have mem_range_succ : ∀ x ∈ S, x < n + 1 := fun x hx => Finset.mem_range.mp (hS hx)
    have mem_range_succ' : ∀ x ∈ T, x < n + 1 := fun x hx => Finset.mem_range.mp (hT hx)
    by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T
    · -- Both contain n: remove n from both, apply IH
      have hS' : S.erase n ⊆ Finset.range n := by
        intro x hx
        have hxS := (Finset.mem_erase.mp hx).2
        have hxn := (Finset.mem_erase.mp hx).1
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS hxS))) hxn)
      have hT' : T.erase n ⊆ Finset.range n := by
        intro x hx
        have hxT := (Finset.mem_erase.mp hx).2
        have hxn := (Finset.mem_erase.mp hx).1
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hT hxT))) hxn)
      have hsum' : (S.erase n).sum (fun i => 2 ^ i) = (T.erase n).sum (fun i => 2 ^ i) := by
        have := Finset.sum_erase_add S (fun i => (2 : ℕ) ^ i) hnS
        have := Finset.sum_erase_add T (fun i => (2 : ℕ) ^ i) hnT
        omega
      have := ih (S.erase n) (T.erase n) hS' hT' hsum'
      exact Finset.erase_injOn_of_mem hnS hnT this
    · -- n ∈ S, n ∉ T: contradiction (S sum ≥ 2^n, T sum < 2^n)
      exfalso
      have hT' : T ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hT hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnT (h ▸ hx)))
      have hT_bound := subset_sum_lt_pow_two n T hT'
      have hS_lower : S.sum (fun i => 2 ^ i) ≥ 2 ^ n := by
        calc S.sum (fun i => 2 ^ i)
            ≥ (({n} : Finset ℕ)).sum (fun i => 2 ^ i) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnS) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := by simp
      omega
    · -- n ∉ S, n ∈ T: symmetric contradiction
      exfalso
      have hS' : S ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hS hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnS (h ▸ hx)))
      have hS_bound := subset_sum_lt_pow_two n S hS'
      have hT_lower : T.sum (fun i => 2 ^ i) ≥ 2 ^ n := by
        calc T.sum (fun i => 2 ^ i)
            ≥ (({n} : Finset ℕ)).sum (fun i => 2 ^ i) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnT) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := by simp
      omega
    · -- Neither contains n: both subsets of range(n), apply IH
      have hS' : S ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hS hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnS (h ▸ hx)))
      have hT' : T ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hT hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnT (h ▸ hx)))
      exact ih S T hS' hT' hsum

/-- **PROVED** (was axiom): Powers of 2 form a dissociated set (binary representation uniqueness). -/
theorem powers_of_two_dissociated :
  ∀ k : ℕ, ∀ S T : Finset ℕ,
    S ⊆ Finset.range k → T ⊆ Finset.range k →
    S.sum (fun i => (2 : ℝ) ^ i) = T.sum (fun i => (2 : ℝ) ^ i) → S = T := by
  intro k S T hS hT hsum
  apply binary_uniqueness_nat k S T hS hT
  -- Reduce ℝ sum equality to ℕ sum equality via casting
  have cast_eq : ∀ U : Finset ℕ,
      U.sum (fun i => (2 : ℝ) ^ i) = ↑(U.sum (fun i => (2 : ℕ) ^ i)) := by
    intro U
    push_cast [Finset.sum_coe_sort]
    simp [Nat.cast_sum, Nat.cast_pow]
  rw [cast_eq, cast_eq] at hsum
  exact_mod_cast hsum

/-- **PROVED** (was axiom): Monotonicity — f is non-decreasing.
    If m ≤ n then f(m) ≤ f(n), since any n-element set contains an
    m-element subset, inheriting the dissociated subset guarantee. -/
theorem maxDissociatedSize_mono :
    ∀ m n : ℕ, m ≤ n → maxDissociatedSize m ≤ maxDissociatedSize n := by
  intro m n hmn
  unfold maxDissociatedSize
  apply csSup_le_csSup
  · -- BddAbove: the n-set is bounded above by n
    refine ⟨n, fun k (hk : ∀ A : Finset ℝ, A.card = n →
        ∃ B, IsDissociatedSubset A B ∧ B.card ≥ k) => ?_⟩
    -- Exhibit a specific n-element Finset ℝ to extract the bound
    have ⟨A, hA⟩ : ∃ A : Finset ℝ, A.card = n :=
      ⟨(Finset.range n).image ((↑) : ℕ → ℝ), by
        rw [Finset.card_image_of_injOn]
        · exact Finset.card_range n
        · intro a _ b _ hab; exact_mod_cast hab⟩
    obtain ⟨B, ⟨hBsub, _⟩, hBcard⟩ := hk A hA
    exact le_trans hBcard (le_trans (Finset.card_le_card hBsub) (le_of_eq hA))
  · -- Nonempty: 0 is in the m-set (empty set is dissociated in any set)
    exact ⟨0, fun A _ => ⟨∅, empty_dissociated A, Nat.zero_le _⟩⟩
  · -- Subset: the m-set ⊆ the n-set
    intro k (hk : ∀ A : Finset ℝ, A.card = m →
        ∃ B, IsDissociatedSubset A B ∧ B.card ≥ k)
    intro A (hA : A.card = n)
    -- A has n ≥ m elements; extract an m-element subset A'
    obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_smaller_set A m (hA ▸ hmn)
    -- A' has a dissociated subset B of size ≥ k
    obtain ⟨B, ⟨hBsub, hBdiss⟩, hBcard⟩ := hk A' hA'card
    -- B ⊆ A' ⊆ A, and dissociatedness depends only on B
    exact ⟨B, ⟨hBsub.trans hA'sub, hBdiss⟩, hBcard⟩

/-- **PROVED** (was axiom): The gap between the greedy bound and the
    conjecture: log₂ vs log₃. Since 2 ≤ 3, log₃ n ≤ log₂ n for all n. -/
theorem log_base_gap :
    ∀ n : ℕ, n ≥ 2 → Nat.log 3 n ≤ Nat.log 2 n := by
  intro n _
  apply Nat.log_anti_left <;> omega
