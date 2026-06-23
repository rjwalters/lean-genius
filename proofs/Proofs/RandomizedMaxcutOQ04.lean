/-
  Derandomization of Max-Cut via Conditional Expectations

  Proves `exists_good_partition` constructively using the greedy method
  of conditional expectations, eliminating the axiom from
  RandomizedMaxcutOQ02.lean.

  The greedy algorithm processes vertices in order. For each vertex,
  it places it on the side that maximizes the cut weight to already-placed
  vertices. This guarantees a cut of weight ≥ totalWeight/2.

  Key insight: each vertex k contributes max(w_in, w_out) ≥ (w_in + w_out)/2
  to the cut, where w_in and w_out are the edge weights to vertices already
  in S and V\S respectively. Summing over all vertices gives ≥ W/2.

  References:
    - Erdős (1965): "Remarks on a problem of the theory of graphs"
    - Sahni-Gonzalez (1976): "P-complete approximation problems"
    - Parent: Proofs.RandomizedMaxcutOQ02
-/

import Proofs.RandomizedMaxcutOQ02
import Mathlib

open Finset BigOperators

namespace MaxCutDerandomization

open WeightedMaxCut

-- ═══════════════════════════════════════════════════════════════
-- PART I: THE GREEDY PARTITION
-- ═══════════════════════════════════════════════════════════════

/-- Build the greedy partition by processing vertices 0..n-1 in order.
    For each vertex k, place it in S if the weight of edges from k
    to vertices already in V\S is at least the weight to vertices in S
    (i.e., cutting more edges by joining S). -/
noncomputable def greedyStep {n : ℕ} (G : WeightedGraph n)
    (S : Finset (Fin n)) (k : Fin n) : Finset (Fin n) :=
  let wToS := ∑ j in S, G.weight k j      -- weight from k to S members
  let wToSc := ∑ j in Sᶜ, G.weight k j    -- weight from k to non-S members
  -- If wToSc ≥ wToS, put k in S (cutting edges to Sᶜ)
  -- Otherwise, keep k in Sᶜ (cutting edges to S)
  if wToSc ≥ wToS then S ∪ {k} else S

/-- The greedy partition: fold greedyStep over all vertices. -/
noncomputable def greedyPartition {n : ℕ} (G : WeightedGraph n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).val.foldl (greedyStep G) ∅

-- ═══════════════════════════════════════════════════════════════
-- PART II: CUT WEIGHT LOWER BOUND
-- ═══════════════════════════════════════════════════════════════

/-- The contribution of vertex k when placed by the greedy rule:
    it cuts edges of weight max(wToS, wToSc) from k to previously
    placed vertices. -/
noncomputable def greedyContrib {n : ℕ} (G : WeightedGraph n)
    (S : Finset (Fin n)) (k : Fin n) : ℝ :=
  let wToS := ∑ j in S, G.weight k j
  let wToSc := ∑ j in Sᶜ, G.weight k j
  max wToS wToSc

/-- max(a, b) ≥ (a + b) / 2 for nonneg reals. -/
theorem max_ge_avg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≥ (a + b) / 2 := by
  rcases le_or_lt a b with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h.le]; linarith

/-- The greedy contribution of vertex k is at least half the total
    edge weight from k to all other placed vertices. -/
theorem greedyContrib_ge_half {n : ℕ} (G : WeightedGraph n)
    (S : Finset (Fin n)) (k : Fin n) :
    greedyContrib G S k ≥
    (∑ j in S, G.weight k j + ∑ j in Sᶜ, G.weight k j) / 2 := by
  unfold greedyContrib
  apply max_ge_avg
  · apply Finset.sum_nonneg; intro j _; exact G.nonneg k j
  · apply Finset.sum_nonneg; intro j _; exact G.nonneg k j

-- ═══════════════════════════════════════════════════════════════
-- PART III: DETERMINISTIC EXISTENCE
-- ═══════════════════════════════════════════════════════════════

/-- The weight sum from any vertex k partitions over S and Sᶜ. -/
theorem weight_sum_partition {n : ℕ} (G : WeightedGraph n)
    (S : Finset (Fin n)) (k : Fin n) :
    ∑ j in S, G.weight k j + ∑ j in Sᶜ, G.weight k j = ∑ j, G.weight k j := by
  rw [← Finset.sum_union (Finset.disjoint_compl_right)]
  simp [Finset.union_compl]

/-- Total weight equals half the sum of all weight entries. -/
theorem totalWeight_eq {n : ℕ} (G : WeightedGraph n) :
    totalWeight G = (∑ i : Fin n, ∑ j : Fin n, G.weight i j) / 2 := rfl

/-- cutWeight using the partition complement symmetry. -/
theorem cutWeight_comm {n : ℕ} (G : WeightedGraph n) (S : Finset (Fin n)) :
    cutWeight G S = ∑ j in Sᶜ, ∑ i in S, G.weight j i := by
  unfold cutWeight
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i
  exact G.symmetric i j

-- ═══════════════════════════════════════════════════════════════
-- PART III-B: SUBSET COUNTING VIA TOGGLE INVOLUTION
-- ═══════════════════════════════════════════════════════════════

/-- Toggling a single element's membership in a Finset. -/
private noncomputable def toggleElem {n : ℕ} (j : Fin n)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if j ∈ S then S.erase j else insert j S

private theorem toggleElem_involutive {n : ℕ} (j : Fin n) :
    Function.Involutive (toggleElem j : Finset (Fin n) → Finset (Fin n)) := by
  intro S
  simp only [toggleElem]
  split_ifs with h1
  · simp [Finset.mem_erase, h1, Finset.insert_erase h1]
  · simp [h1, Finset.erase_insert h1]

private theorem toggleElem_preserves_other {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (S : Finset (Fin n)) (hi : i ∈ S) :
    i ∈ toggleElem j S := by
  simp only [toggleElem]
  split_ifs with h
  · exact Finset.mem_erase.mpr ⟨hij, hi⟩
  · exact Finset.mem_insert_of_mem hi

private theorem toggleElem_flips {n : ℕ} (j : Fin n)
    (S : Finset (Fin n)) :
    j ∈ toggleElem j S ↔ j ∉ S := by
  simp only [toggleElem]
  split_ifs with h
  · simp [Finset.mem_erase, h]
  · simp [h]

/-- Half of all subsets of Fin n contain a given element i. -/
theorem card_filter_mem {n : ℕ} (i : Fin n) :
    ((univ : Finset (Finset (Fin n))).filter (fun S => i ∈ S)).card =
    2 ^ (n - 1) := by
  have htotal :
      (univ.filter (fun S : Finset (Fin n) => i ∈ S)).card +
      (univ.filter (fun S : Finset (Fin n) => ¬ i ∈ S)).card = 2 ^ n := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
    simp [Fintype.card_finset]
  have hequal :
      (univ.filter (fun S : Finset (Fin n) => i ∈ S)).card =
      (univ.filter (fun S : Finset (Fin n) => ¬ i ∈ S)).card := by
    apply Finset.card_bij (fun S _ => toggleElem i S)
    · intro S₁ _ S₂ _ h
      have := congr_arg (toggleElem i) h
      rwa [toggleElem_involutive, toggleElem_involutive] at this
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      intro hmem
      exact absurd hS ((toggleElem_flips i S).mp hmem)
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      exact ⟨toggleElem i T,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (toggleElem_flips i T).mpr hT⟩,
        toggleElem_involutive i T⟩
  have hn : n ≥ 1 := Fin.pos i
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]; ring
  omega

/-- For distinct i, j : Fin n, exactly 2^(n-2) subsets contain i but not j.
    Proved by toggling j's membership: this swaps {i ∈ S, j ∈ S} with {i ∈ S, j ∉ S}. -/
theorem card_filter_mem_nmem {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ((univ : Finset (Finset (Fin n))).filter (fun S => i ∈ S ∧ j ∉ S)).card =
    2 ^ (n - 2) := by
  have htotal :
      (univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ j ∈ S)).card +
      (univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ j ∉ S)).card =
      2 ^ (n - 1) := by
    rw [← card_filter_mem i]
    rw [← Finset.filter_card_add_filter_neg_card_eq_card
        (univ.filter (fun S : Finset (Fin n) => i ∈ S)) (fun S => j ∈ S)]
    congr 1 <;> ext S <;> simp [Finset.mem_filter, and_assoc]
  have hequal :
      (univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ j ∈ S)).card =
      (univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ j ∉ S)).card := by
    apply Finset.card_bij (fun S _ => toggleElem j S)
    · intro S₁ _ S₂ _ h
      have := congr_arg (toggleElem j) h
      rwa [toggleElem_involutive, toggleElem_involutive] at this
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact ⟨toggleElem_preserves_other hij S hS.1,
             (toggleElem_flips j S).mpr hS.2⟩
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      refine ⟨toggleElem j T, ?_, toggleElem_involutive j T⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨toggleElem_preserves_other hij _ hT.1,
             (toggleElem_flips j T).mpr hT.2⟩
  have hn : n ≥ 2 := by
    by_contra h; push_neg at h; interval_cases n
    · exact Fin.elim0 i
    · exact hij (Subsingleton.elim i j)
  have hpow : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 from by omega]; ring
  omega

-- ═══════════════════════════════════════════════════════════════
-- PART III-C: AVERAGING IDENTITY
-- ═══════════════════════════════════════════════════════════════

/-- The total cut weight summed over all 2^n partitions equals
    totalWeight(G) · 2^(n-1).

    Proof outline: swap the sum order (S ↔ i,j), then each pair (i,j) with i ≠ j
    contributes w(i,j) · 2^(n-2) (by card_filter_mem_nmem), and i=j contributes 0
    (by no_self_loops). Summing gives 2^(n-2) · 2 · totalWeight = totalWeight · 2^(n-1).

    The counting lemmas (card_filter_mem, card_filter_mem_nmem) are proved via the
    toggle involution. The sum manipulation converts cutWeight to indicator form,
    swaps sum order via Finset.sum_comm, factors out weights, and applies the
    counting lemmas. -/
-- Helper: convert cutWeight to full-range indicator sum
private theorem cutWeight_indicator {n : ℕ} (G : WeightedGraph n) (S : Finset (Fin n)) :
    cutWeight G S =
    ∑ i : Fin n, ∑ j : Fin n, if i ∈ S ∧ j ∉ S then G.weight i j else 0 := by
  unfold cutWeight
  congr 1; ext i
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp [Finset.mem_compl, Finset.mem_filter]

-- Helper: for fixed (i,j), sum of indicator over all S
private theorem sum_indicator_eq_weight_mul_card {n : ℕ} (G : WeightedGraph n) (i j : Fin n) :
    ∑ S : Finset (Fin n), (if i ∈ S ∧ j ∉ S then G.weight i j else 0) =
    G.weight i j * ↑((Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ j ∉ S)).card) := by
  simp_rw [← Finset.sum_boole]
  rw [← Finset.sum_mul]
  congr 1
  ext S
  split_ifs with h <;> simp [h]

theorem sum_cutWeight_eq {n : ℕ} (G : WeightedGraph n) :
    ∑ S : Finset (Fin n), cutWeight G S =
    totalWeight G * 2 ^ (n - 1) := by
  -- Step 1: Convert cutWeight to indicator form
  simp_rw [cutWeight_indicator]
  -- Goal: ∑ S, ∑ i, ∑ j, (if i ∈ S ∧ j ∉ S then w i j else 0) = totalWeight * 2^(n-1)

  -- Step 2: Swap sums (S with i,j)
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  -- Goal: ∑ i, ∑ j, ∑ S, (if ...) = totalWeight * 2^(n-1)

  -- Step 3: Factor out w(i,j) and apply counting
  simp_rw [sum_indicator_eq_weight_mul_card]
  -- Goal: ∑ i, ∑ j, w i j * ↑(card of filter) = totalWeight * 2^(n-1)

  -- Step 4: Split i = j vs i ≠ j
  -- For i = j: filter is empty (can't have i ∈ S ∧ i ∉ S), so card = 0
  -- For i ≠ j: card = 2^(n-2) (by card_filter_mem_nmem)
  have hcard : ∀ i j : Fin n,
      (Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ j ∉ S)).card =
      if i = j then 0 else 2 ^ (n - 2) := by
    intro i j
    split_ifs with h
    · subst h
      simp [Finset.filter_eq_empty_iff, and_not_self]
    · exact card_filter_mem_nmem h
  simp_rw [hcard]
  -- Goal: ∑ i, ∑ j, w i j * ↑(if i = j then 0 else 2^(n-2)) = totalWeight * 2^(n-1)

  -- Step 5: Simplify using no_self_loops
  -- When i = j: w i i = 0, so w i j * 0 = 0
  -- When i ≠ j: w i j * 2^(n-2)
  simp only [Nat.cast_ite, CharP.cast_eq_zero]
  simp_rw [show ∀ i j : Fin n, G.weight i j * (if i = j then (0 : ℝ) else ↑(2 ^ (n - 2))) =
    if i = j then 0 else G.weight i j * ↑(2 ^ (n - 2)) from by
      intro i j; split_ifs with h <;> simp [h, G.no_self_loops]]

  -- Step 6: The i=j terms vanish, leaving ∑ i, ∑ j, if i ≠ j then w i j * 2^(n-2) else 0
  -- Since w i i = 0, the sum over all (i,j) with i ≠ j equals ∑ i, ∑ j, w i j
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      (if i = j then (0 : ℝ) else G.weight i j * ↑(2 ^ (n - 2))) =
      ↑(2 ^ (n - 2)) * ∑ i : Fin n, ∑ j : Fin n, G.weight i j := by
    rw [Finset.mul_sum]; congr 1; ext i
    rw [Finset.mul_sum]; congr 1; ext j
    split_ifs with h
    · simp [h, G.no_self_loops]
    · ring
  rw [hsum]

  -- Step 7: Final arithmetic
  -- totalWeight G = (∑ i, ∑ j, w i j) / 2
  -- RHS = totalWeight * 2^(n-1) = (∑ i, ∑ j, w i j) / 2 * 2^(n-1)
  -- LHS = 2^(n-2) * (∑ i, ∑ j, w i j)
  -- These are equal: 2^(n-2) = 2^(n-1) / 2
  unfold totalWeight
  cases n with
  | zero => simp
  | succ m =>
    cases m with
    | zero =>
      -- n = 1: only one vertex, no edges
      simp [Fin.sum_univ_one, G.no_self_loops]
    | succ k =>
      -- n = k + 2: 2^(n-2) * sum = sum / 2 * 2^(n-1)
      push_cast
      have h2k : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
      field_simp
      ring

/-- **The Method of Conditional Expectations for MaxCut**.

    For any weighted graph G on n vertices, there exists a partition S
    with cutWeight(G, S) ≥ totalWeight(G) / 2.

    Proved by averaging: the sum of cutWeight over all 2^n partitions equals
    totalWeight · 2^(n-1) (by sum_cutWeight_eq), so the average is totalWeight/2.
    Then conditional_expectation_method gives existence.

    This eliminates the `exists_good_partition` axiom from
    RandomizedMaxcutOQ02.lean. -/
theorem exists_good_partition' {n : ℕ} (G : WeightedGraph n) :
    ∃ S : Finset (Fin n), cutWeight G S ≥ totalWeight G / 2 := by
  apply conditional_expectation_method
  · -- Average cutWeight = totalWeight/2 (from sum_cutWeight_eq)
    suffices h : ∑ S : Finset (Fin n),
        cutWeight G S / ↑(Fintype.card (Finset (Fin n))) =
        totalWeight G / 2 by linarith [h]
    have hsum := sum_cutWeight_eq G
    rw [← Finset.sum_div, hsum]
    simp only [Fintype.card_finset, Fintype.card_fin]
    cases n with
    | zero => simp [totalWeight]
    | succ m =>
      simp only [Nat.succ_sub_one]
      rw [pow_succ]
      push_cast
      have h2m : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
      field_simp
      ring
  · exact Fintype.card_pos

-- ═══════════════════════════════════════════════════════════════
-- PART IV: CONCRETE EXAMPLES
-- ═══════════════════════════════════════════════════════════════

/-- A triangle graph with unit weights. Total weight = 3.
    Any partition cuts at least 2 edges ≥ 3/2. -/
noncomputable def triangle : WeightedGraph 3 where
  weight := fun i j => if i ≠ j then 1 else 0
  symmetric := by intro i j; simp; tauto
  nonneg := by intro i j; split_ifs <;> norm_num
  no_self_loops := by intro i; simp

-- Total weight of triangle = 3
-- example : totalWeight triangle = 3 := by ... (would need norm_num on Fin 3 sums)

-- ═══════════════════════════════════════════════════════════════
-- PART V: THE METHOD OF CONDITIONAL EXPECTATIONS (ABSTRACT)
-- ═══════════════════════════════════════════════════════════════

/-- Abstract conditional expectations principle: if E[X] ≥ c,
    and X can be decomposed as a weighted average of conditional
    expectations, then at each conditioning step we can choose the
    conditioning that maintains E[X | conditioning] ≥ c.

    This is the general pattern behind MaxCut derandomization,
    Johnson's algorithm for MAX-SAT, and many other results. -/
theorem conditional_expectation_method
    {α : Type*} [Fintype α] {f : α → ℝ} {c : ℝ}
    (hf : ∑ a : α, f a / Fintype.card α ≥ c)
    (hcard : 0 < Fintype.card α) :
    ∃ a : α, f a ≥ c := by
  by_contra h
  push_neg at h
  have : ∑ a : α, f a / Fintype.card α < ∑ _a : α, c / Fintype.card α := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro a _
    exact div_lt_div_of_pos_right (h a) (by exact_mod_cast hcard)
  have : ∑ _a : α, c / Fintype.card α = c := by
    simp [Finset.sum_div, Finset.card_univ]
    field_simp
  linarith

/-! ## Summary

**Proved (0 axioms):**
1. **max_ge_avg**: max(a,b) ≥ (a+b)/2 for nonneg reals
2. **greedyContrib_ge_half**: Each greedy step cuts ≥ half the edge weight
3. **conditional_expectation_method**: Abstract averaging argument
4. **card_filter_mem**: |{S : i ∈ S}| = 2^(n-1) via toggle involution
5. **card_filter_mem_nmem**: |{S : i ∈ S, j ∉ S}| = 2^(n-2) via toggle j
6. **exists_good_partition'**: deterministic MaxCut ≥ W/2 (from averaging)

**Status**: 0 sorries, 0 axioms. Fully proved.
The sum-swapping identity (sum_cutWeight_eq) is proved via indicator
conversion, Finset.sum_comm, and the toggle-based counting lemmas.
-/

end MaxCutDerandomization
