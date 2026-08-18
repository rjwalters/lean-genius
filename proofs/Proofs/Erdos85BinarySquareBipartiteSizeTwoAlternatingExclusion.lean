import Proofs.Erdos85BinarySquareRegularParity

/-!
# Bipartite size-two defect components with an alternating internal factor

Let `G` be a `q`-regular `C₄`-free graph on `q²` vertices and `(secondOrderDefectGraph G)` its
second-order defect graph, so `A² = (q-1)I + J - (secondOrderDefectGraph G)` and `A` commutes with `(secondOrderDefectGraph G)`.
Suppose the defect graph has exactly two components: a *size-two* component
`c` (order `2q`) and its complement.  If `(secondOrderDefectGraph G)[c]` is bipartite with classes
`X, Y` and every internal ambient edge of `c` crosses `X–Y` (this is
automatic in the branch `A[c] ⊆ (secondOrderDefectGraph G)[c]`, i.e. when all internal edges are
triangle-free), then no such graph exists.

The proof is a short eigenvector argument.  With `v = 1_X - 1_Y` (zero off
`c`) one has `(secondOrderDefectGraph G) v = -(q-1) v`, `A v = -2v + w` where `w` is supported off `c`
with values in `{-2, 0, 2}` (each outside vertex has exactly two neighbours in
`c`), and `A² v = 2(q-1) v`.  Reading `A w = (2q-6) v + 2w` at a vertex of `c`
forces some outside neighbour with `w = 0`; reading `(secondOrderDefectGraph G) w = -(q-1) w` at a
vertex with `w = ±2` forces all of its defect neighbours to the opposite
extreme, so the zero fibre of `w` is closed under defect adjacency.  Since the
complement of `c` is defect-connected, `w` vanishes identically off `c`, which
contradicts `A w = (2q-6) v + 2w` for `q ≥ 4`.

Everything is uniform in `q`; nothing is enumerated.  In the order-64
degree-eight campaign this kills the `[6,2]` stratum whenever the size-two
component is bipartite (in particular the synchronized `K₈,₈ − PM` model) in
its alternating `H ⊂ (secondOrderDefectGraph G)` branch.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Adjacency-closed predicates propagate along reachability. -/
theorem reachable_induction_of_adj_closed {V : Type*} (D : SimpleGraph V)
    (P : V → Prop) (hP : ∀ x y, D.Adj x y → P x → P y) {u v : V}
    (h : D.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-- **Bipartite size-two component, alternating internal factor, connected
complement: impossible.**  See the module docstring for the argument. -/
theorem binarySquare_regular_sizeTwoPart_bipartite_alternating_connected_complement_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hrest : ∀ x y, x ∉ c.supp → y ∉ c.supp →
      (secondOrderDefectGraph G).Reachable x y)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (halt : ∀ x y, x ∈ c.supp → y ∈ c.supp → G.Adj x y → col x ≠ col y) :
    False := by
  have hq3 : 3 ≤ q := by omega
  -- membership in `c` as an equation of components
  have hmem : ∀ x, x ∈ c.supp ↔ (secondOrderDefectGraph G).connectedComponentMk x = c := fun x =>
    ConnectedComponent.mem_supp_iff c x
  -- defect degree is `q - 1`
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdeg : ∀ y : V, (secondOrderDefectGraph G).degree y = q - 1 := by
    intro y
    have h := secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg hcensus y
    change (secondOrderDefectGraph G).degree y = (q - 3) + 2 at h
    omega
  -- defect adjacency stays inside / outside `c`
  have hDin : ∀ x y, x ∈ c.supp → (secondOrderDefectGraph G).Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [hmem] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hDout : ∀ x y, x ∉ c.supp → (secondOrderDefectGraph G).Adj x y → y ∉ c.supp := by
    intro x y hx hxy hy
    exact hx (hDin y x hy hxy.symm)
  -- every vertex has exactly two ambient neighbours in `c`
  have htwo : ∀ x, ((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card = 2 := by
    intro x
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq3 hreg hcard ((secondOrderDefectGraph G).connectedComponentMk x) c
      (x := x) ((ConnectedComponent.mem_supp_iff _ x).mpr rfl)
    rw [hc] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h
  -- the signed indicator of the bipartition, zero off `c`
  set s : V → ℤ := fun x =>
    if (secondOrderDefectGraph G).connectedComponentMk x = c then (if col x then 1 else -1) else 0 with hs
  have hs_in : ∀ x, x ∈ c.supp → s x = (if col x then 1 else -1) := by
    intro x hx
    simp only [hs, if_pos ((hmem x).mp hx)]
  have hs_out : ∀ x, x ∉ c.supp → s x = 0 := by
    intro x hx
    have : ¬ (secondOrderDefectGraph G).connectedComponentMk x = c := fun h => hx ((hmem x).mpr h)
    simp only [hs, if_neg this]
  have hs_opp : ∀ x y, x ∈ c.supp → y ∈ c.supp → col x ≠ col y → s y = - s x := by
    intro x y hx hy hxy
    rw [hs_in x hx, hs_in y hy]
    cases hcx : col x <;> cases hcy : col y <;> simp_all
  have hs_sq : ∀ x, x ∈ c.supp → s x = 1 ∨ s x = -1 := by
    intro x hx
    rw [hs_in x hx]
    cases col x <;> simp
  -- Step 1: `(secondOrderDefectGraph G) s = -(q-1) s` pointwise
  have hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = -((q : ℤ) - 1) * s x := by
    intro x
    by_cases hx : x ∈ c.supp
    · have hall : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = - s x := by
        intro y hy
        have hxy : (secondOrderDefectGraph G).Adj x y := ((secondOrderDefectGraph G).mem_neighborFinset x y).mp hy
        exact hs_opp x y hx (hDin x y hx hxy) (hbip x y hx (hDin x y hx hxy) hxy)
      rw [Finset.sum_congr rfl hall, Finset.sum_const, (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
        hDdeg x, nsmul_eq_mul]
      have : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q)]; simp
      rw [this]; ring
    · have hall : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = 0 := by
        intro y hy
        exact hs_out y (hDout x y hx (((secondOrderDefectGraph G).mem_neighborFinset x y).mp hy))
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, hs_out x hx]
      ring
  -- Step 2: `w := A s + 2 s`
  set w : V → ℤ := fun x => (∑ y ∈ G.neighborFinset x, s y) + 2 * s x with hw
  have hAs_split : ∀ x, ∑ y ∈ G.neighborFinset x, s y =
      ∑ y ∈ (G.neighborFinset x).filter (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y := by
    intro x
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : (secondOrderDefectGraph G).connectedComponentMk y = c
    · simp [hy]
    · rw [if_neg hy, hs_out y (fun h => hy ((hmem y).mp h))]
  have hw_in : ∀ x, x ∈ c.supp → w x = 0 := by
    intro x hx
    simp only [hw]
    rw [hAs_split x]
    have hall : ∀ y ∈ (G.neighborFinset x).filter (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = - s x := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy.1
      have hyc : y ∈ c.supp := (hmem y).mpr hy.2
      exact hs_opp x y hx hyc (halt x y hx hyc hxy)
    rw [Finset.sum_congr rfl hall, Finset.sum_const, htwo x, nsmul_eq_mul]
    push_cast; ring
  have hw_val : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2 := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact Or.inr (Or.inl (hw_in x hx))
    · simp only [hw]
      rw [hAs_split x, hs_out x hx, mul_zero, add_zero]
      obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp (htwo x)
      rw [hset, Finset.sum_pair hab]
      have ha : a ∈ c.supp := by
        have : a ∈ (G.neighborFinset x).filter (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
          rw [hset]; simp
        exact (hmem a).mpr (Finset.mem_filter.mp this).2
      have hb : b ∈ c.supp := by
        have : b ∈ (G.neighborFinset x).filter (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
          rw [hset]; simp
        exact (hmem b).mpr (Finset.mem_filter.mp this).2
      rcases hs_sq a ha with h1 | h1 <;> rcases hs_sq b hb with h2 | h2 <;>
        simp [h1, h2]
  -- Step 3: `Σ s = 0` (double count the defect degrees against `(secondOrderDefectGraph G) s = -(q-1) s`)
  have hsum_zero : ∑ x, s x = 0 := by
    have hlhs : ∑ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = ((q : ℤ) - 1) * ∑ x, s x := by
      have h1 : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = ∑ y, ((secondOrderDefectGraph G).adjMatrix ℤ) x y * s y := by
        intro x
        rw [← SimpleGraph.adjMatrix_mulVec_apply]
        rfl
      simp_rw [h1]
      rw [Finset.sum_comm]
      have h2 : ∀ y, ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) x y * s y = ((q : ℤ) - 1) * s y := by
        intro y
        rw [← Finset.sum_mul]
        have h3 : ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) x y = ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) y x := by
          apply Finset.sum_congr rfl
          intro x _
          simp [SimpleGraph.adjMatrix_apply, (secondOrderDefectGraph G).adj_comm]
        rw [h3]
        have h4 : ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) y x = ((secondOrderDefectGraph G).degree y : ℤ) := by
          have := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℤ) (G := (secondOrderDefectGraph G)) (a := 1) (v := y)
          simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] at this
          simpa using this
        rw [h4, hDdeg y, Nat.cast_sub (by omega : 1 ≤ q)]
        simp
      simp_rw [h2]
      rw [← Finset.mul_sum]
    have hrhs : ∑ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = -((q : ℤ) - 1) * ∑ x, s x := by
      simp_rw [hDs]
      rw [← Finset.mul_sum]
    have hq1 : ((q : ℤ) - 1) ≠ 0 := by
      have : (4 : ℤ) ≤ q := by exact_mod_cast hq
      omega
    have : 2 * ((q : ℤ) - 1) * ∑ x, s x = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hq1; linarith
    · exact h
  -- Step 4: `A² s = 2(q-1) s` pointwise
  have hAA : ∀ x, ∑ y ∈ G.neighborFinset x, ∑ z ∈ G.neighborFinset y, s z =
      2 * ((q : ℤ) - 1) * s x := by
    intro x
    have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg (d := q)
    have h1 : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ s) x =
        ∑ y ∈ G.neighborFinset x, ∑ z ∈ G.neighborFinset y, s z := by
      rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have h2 : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ s) x =
        ((q : ℤ) - 1) * s x + (∑ y, s y) - ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y := by
      rw [hsq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
      congr 2
      simp [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct]
    rw [← h1, h2, hsum_zero, hDs x]
    ring
  -- Step 5: `A w = (2q-6) s + 2 w` pointwise
  have hAw : ∀ x, ∑ y ∈ G.neighborFinset x, w y = (2 * (q : ℤ) - 6) * s x + 2 * w x := by
    intro x
    have h1 : ∀ y, ∑ z ∈ G.neighborFinset y, s z = w y - 2 * s y := by
      intro y; simp only [hw]; ring
    have h2 := hAA x
    simp_rw [h1] at h2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h2
    have h3 : ∑ y ∈ G.neighborFinset x, s y = w x - 2 * s x := by simp only [hw]; ring
    rw [h3] at h2
    linarith
  -- Step 6: `(secondOrderDefectGraph G) w = -(q-1) w` pointwise (commutation of `A` and `(secondOrderDefectGraph G)`)
  have hDw : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, w y = -((q : ℤ) - 1) * w x := by
    intro x
    have hcomm := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg (d := q)
    have h1 : (((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ s) x =
        ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, ∑ z ∈ G.neighborFinset y, s z := by
      rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have h2 : ((G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ) *ᵥ s) x =
        ∑ y ∈ G.neighborFinset x, ∑ z ∈ (secondOrderDefectGraph G).neighborFinset y, s z := by
      rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have h12 : ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, ∑ z ∈ G.neighborFinset y, s z =
        ∑ y ∈ G.neighborFinset x, ∑ z ∈ (secondOrderDefectGraph G).neighborFinset y, s z := by
      rw [← h1, ← h2, hcomm]
    have h3 : ∀ y, ∑ z ∈ G.neighborFinset y, s z = w y - 2 * s y := by
      intro y; simp only [hw]; ring
    simp_rw [h3, hDs] at h12
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hDs x, ← Finset.mul_sum] at h12
    have h4 : ∑ y ∈ G.neighborFinset x, s y = w x - 2 * s x := by simp only [hw]; ring
    rw [h4] at h12
    linarith
  -- Step 7: the zero fibre of `w` off `c` is closed under defect adjacency
  have hclosed : ∀ u u', u ∉ c.supp → w u = 0 → (secondOrderDefectGraph G).Adj u u' → w u' = 0 := by
    intro u u' hu hwu huu'
    have hu'mem : u ∈ (secondOrderDefectGraph G).neighborFinset u' := ((secondOrderDefectGraph G).mem_neighborFinset u' u).mpr huu'.symm
    have hcardD : ((secondOrderDefectGraph G).neighborFinset u').card = q - 1 := by
      rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDdeg]
    have hq1 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]; simp
    rcases hw_val u' with h | h | h
    · -- `w u' = -2`: all defect neighbours must have `w = 2`, but `u` has `w = 0`
      exfalso
      have hsum := hDw u'
      rw [h] at hsum
      -- `Σ (2 - w y) ≥ 2 - w u = 2` while it equals `2(q-1) - Σ w = 0`
      have hnonneg : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset u', 0 ≤ 2 - w y := by
        intro y _
        rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
      have hle := Finset.single_le_sum hnonneg hu'mem
      rw [hwu] at hle
      rw [Finset.sum_sub_distrib, Finset.sum_const, hcardD, nsmul_eq_mul, hq1, hsum] at hle
      linarith
    · exact h
    · -- `w u' = 2`: all defect neighbours must have `w = -2`, but `u` has `w = 0`
      exfalso
      have hsum := hDw u'
      rw [h] at hsum
      have hnonneg : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset u', 0 ≤ w y + 2 := by
        intro y _
        rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
      have hle := Finset.single_le_sum hnonneg hu'mem
      rw [hwu] at hle
      rw [Finset.sum_add_distrib, Finset.sum_const, hcardD, nsmul_eq_mul, hq1, hsum] at hle
      linarith
  -- Step 8: a vertex of `c` and its outside neighbourhood
  have hne : c.supp.Nonempty := by
    rw [← Set.ncard_pos, hc]; omega
  obtain ⟨z, hz⟩ := hne
  have hzsum : ∑ y ∈ G.neighborFinset z, w y = (2 * (q : ℤ) - 6) * s z := by
    rw [hAw z, hw_in z hz]; ring
  -- outside neighbours of `z`
  set T := (G.neighborFinset z).filter (fun y => ¬ (secondOrderDefectGraph G).connectedComponentMk y = c) with hT
  have hTcard : T.card = q - 2 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset z) (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
    rw [htwo z, G.card_neighborFinset_eq_degree, hreg z] at h
    simp only [hT]
    omega
  have hzsumT : ∑ y ∈ T, w y = (2 * (q : ℤ) - 6) * s z := by
    rw [← hzsum]
    symm
    rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset z)
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)]
    have hzero : ∑ y ∈ (G.neighborFinset z).filter (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        w y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      exact hw_in y ((hmem y).mpr (Finset.mem_filter.mp hy).2)
    rw [hzero, zero_add]
  -- some outside neighbour of `z` has `w = 0`
  have hexists : ∃ u ∈ T, w u = 0 := by
    by_contra hnone
    push Not at hnone
    have hdvd : (4 : ℤ) ∣ ∑ y ∈ T, (w y - 2) := by
      apply Finset.dvd_sum
      intro y hy
      rcases hw_val y with h | h | h
      · rw [h]; norm_num
      · exact absurd h (hnone y hy)
      · rw [h]; norm_num
    rw [Finset.sum_sub_distrib, Finset.sum_const, hTcard, nsmul_eq_mul, hzsumT] at hdvd
    have hq2 : ((q - 2 : ℕ) : ℤ) = (q : ℤ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ q)]; simp
    rw [hq2] at hdvd
    rcases hs_sq z hz with h | h <;> rw [h] at hdvd <;> omega
  obtain ⟨u₀, hu₀T, hwu₀⟩ := hexists
  have hu₀ : u₀ ∉ c.supp := fun h => (Finset.mem_filter.mp hu₀T).2 ((hmem u₀).mp h)
  -- Step 9: propagate to the whole complement, then contradict at `z`
  have hall : ∀ u, u ∉ c.supp → w u = 0 := by
    intro u hu
    have hreach := hrest u₀ u hu₀ hu
    have := reachable_induction_of_adj_closed (secondOrderDefectGraph G) (fun x => x ∉ c.supp ∧ w x = 0)
      (fun x y hxy hx => ⟨hDout x y hx.1 hxy, hclosed x y hx.1 hx.2 hxy⟩) hreach ⟨hu₀, hwu₀⟩
    exact this.2
  have hTzero : ∑ y ∈ T, w y = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    exact hall y (fun h => (Finset.mem_filter.mp hy).2 ((hmem y).mp h))
  rw [hTzero] at hzsumT
  have hq4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
  rcases hs_sq z hz with h | h <;> rw [h] at hzsumT <;> linarith

/-- The `A[c] ⊆ (secondOrderDefectGraph G)[c]` (all internal edges triangle-free) form: if the size-two
component is defect-bipartite and every internal ambient edge is a defect
edge, the alternation hypothesis is automatic. -/
theorem binarySquare_regular_sizeTwoPart_bipartite_internal_subset_defect_connected_complement_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hrest : ∀ x y, x ∉ c.supp → y ∉ c.supp →
      (secondOrderDefectGraph G).Reachable x y)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (hsub : ∀ x y, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (secondOrderDefectGraph G).Adj x y) :
    False :=
  binarySquare_regular_sizeTwoPart_bipartite_alternating_connected_complement_false
    G hfree hq hreg hcard c hc hrest col hbip
    (fun x y hx hy hxy => hbip x y hx hy (hsub x y hx hy hxy))

/-- Two-component form: if the defect graph has exactly two components, the
complement of `c` is automatically defect-connected. -/
theorem binarySquare_regular_sizeTwoPart_bipartite_alternating_two_components_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hcount : Fintype.card (secondOrderDefectGraph G).ConnectedComponent = 2)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (halt : ∀ x y, x ∈ c.supp → y ∈ c.supp → G.Adj x y → col x ≠ col y) :
    False := by
  apply binarySquare_regular_sizeTwoPart_bipartite_alternating_connected_complement_false
    G hfree hq hreg hcard c hc _ col hbip halt
  intro x y hx hy
  have hx' : (secondOrderDefectGraph G).connectedComponentMk x ≠ c := fun h =>
    hx ((ConnectedComponent.mem_supp_iff c x).mpr h)
  have hy' : (secondOrderDefectGraph G).connectedComponentMk y ≠ c := fun h =>
    hy ((ConnectedComponent.mem_supp_iff c y).mpr h)
  -- with exactly two components, the two components other than `c` coincide
  have hthree : ∀ a b : (secondOrderDefectGraph G).ConnectedComponent, a ≠ c → b ≠ c → a = b := by
    intro a b ha hb
    by_contra hab
    have hinj : Function.Injective (fun i : Fin 3 =>
        if i = 0 then c else if i = 1 then a else b) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have := Fintype.card_le_of_injective _ hinj
    rw [hcount, Fintype.card_fin] at this
    omega
  have hxy := hthree _ _ hx' hy'
  exact ConnectedComponent.exact hxy

end

end Erdos85
