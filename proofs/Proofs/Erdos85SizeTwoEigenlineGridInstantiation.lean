import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85SizeTwoEigenlineGridLaws

/-!
# Graph-side instantiation of the eigenline grid (general q)

Node: `SIZE-TWO-EIGENLINE(q)`, graph-side half.  From a size-two defect
component `c` (order `2q`) of a `q`-regular C4-free graph on `q²` vertices,
carrying a signed alternating joint eigenline (`s = ±1` on `c`, zero off,
`A s = -2 s` on `c`, `D s = (q-5) s`), we derive the inputs of
`gridCode_hole_reflectionCirculant`.

First stage: the **same-side census**.  Same-side pairs number `q(q-1)`;
same-side defect pairs number `q(q-3)` (same-side defect degree
`((q-1)+(q-5))/2 = q-3`); pairs with an internal common neighbour number
`2q` (the `H`-neighbour pair of each vertex, distinct by C4-freedom).  The
partition is exact, so **no same-side pair has an exterior common
neighbour**: every exterior vertex adjacent to `c` sees one `+1` and one
`-1` vertex.  This makes the grid labels total with no extra hypothesis.
-/

open Finset SimpleGraph

namespace Erdos85

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

section SignClasses

/-- The two sign classes of a zero-sum `±1` labelling of a `2q`-element
component support have `q` elements each. -/
theorem signClass_card_eq
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {q : ℕ} (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0) :
    (Finset.univ.filter fun x => x ∈ c.supp ∧ s x = 1).card = q ∧
      (Finset.univ.filter fun x => x ∈ c.supp ∧ s x = -1).card = q := by
  classical
  set P := Finset.univ.filter fun x => x ∈ c.supp ∧ s x = 1 with hP
  set N := Finset.univ.filter fun x => x ∈ c.supp ∧ s x = -1 with hN
  -- the support as a finset
  have hsupp_card : (Finset.univ.filter fun x => x ∈ c.supp).card = q * 2 := by
    have h1 : c.supp.ncard = (Finset.univ.filter fun x => x ∈ c.supp).card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext x
      simp
    rw [← h1, hc]
  -- P and N partition the support
  have hPN_disj : Disjoint P N := by
    rw [Finset.disjoint_filter]
    rintro x - ⟨-, h1⟩ ⟨-, h2⟩
    rw [h1] at h2
    norm_num at h2
  have hPN_union : P ∪ N = Finset.univ.filter fun x => x ∈ c.supp := by
    ext x
    simp only [hP, hN, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases hs_in x h with h1 | h1
      · exact Or.inr ⟨h, h1⟩
      · exact Or.inl ⟨h, h1⟩
  have hcard_sum : P.card + N.card = q * 2 := by
    rw [← Finset.card_union_of_disjoint hPN_disj, hPN_union, hsupp_card]
  -- the signed sum splits as P.card - N.card = 0
  have hsplit : (P.card : ℤ) - (N.card : ℤ) = 0 := by
    have h1 : ∑ x ∈ P, s x = (P.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun x hx => ((Finset.mem_filter.mp hx).2).2)]
      simp
    have h2 : ∑ x ∈ N, s x = -(N.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun x hx => ((Finset.mem_filter.mp hx).2).2)]
      simp
    have h3 : ∑ x ∈ P ∪ N, s x = ∑ x, s x := by
      rw [hPN_union]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ c.supp
      · simp [hx]
      · simp [hx, hs_out x hx]
    rw [Finset.sum_union hPN_disj, h1, h2, hsum] at h3
    linarith [h3]
  constructor
  · omega
  · omega

end SignClasses

section DefectDegrees

set_option linter.unusedSectionVars false

variable [DecidableRel (antipodalGraph G).Adj]
variable [DecidableRel (triangleFreeEdgeGraph G).Adj]
variable [Fintype (secondOrderDefectGraph G).ConnectedComponent]
variable [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]

/-- The defect graph of a `q`-regular C4-free graph on `q²` vertices is
`(q-1)`-regular (public restatement of the census computation). -/
theorem defect_degree (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q) (x : V) :
    (secondOrderDefectGraph G).degree x = q - 1 := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have h := secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree hreg hcensus x
  change (secondOrderDefectGraph G).degree x = (q - 3) + 2 at h
  omega

/-- Defect neighbours stay in the component. -/
theorem defect_neighbor_mem_supp
    (c : (secondOrderDefectGraph G).ConnectedComponent) {z y : V}
    (hz : z ∈ c.supp) (hadj : (secondOrderDefectGraph G).Adj z y) :
    y ∈ c.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hz ⊢
  rw [← hz]
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj.symm)

/-- **Same-side defect degree.**  With the joint eigenline
`D s = (q-5) s`, every component vertex has exactly `q-3` same-sign and
`2` opposite-sign defect neighbours. -/
theorem sameSide_defect_degree (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    {z : V} (hz : z ∈ c.supp) :
    (((secondOrderDefectGraph G).neighborFinset z).filter
      fun y => s y = s z).card = q - 3 ∧
    (((secondOrderDefectGraph G).neighborFinset z).filter
      fun y => s y = -(s z)).card = 2 := by
  classical
  set T := (secondOrderDefectGraph G).neighborFinset z with hT
  have hTcard : T.card = q - 1 := by
    have h := defect_degree G hfree (by omega) hreg hcard z
    rwa [SimpleGraph.degree] at h
  have hmem : ∀ y ∈ T, s y = s z ∨ s y = -(s z) := by
    intro y hy
    have hy' : y ∈ c.supp := defect_neighbor_mem_supp G c hz
      ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
    rcases hs_in y hy' with h | h <;> rcases hs_in z hz with h' | h' <;>
      rw [h, h'] <;> norm_num
  have hzsign : s z = -1 ∨ s z = 1 := hs_in z hz
  have hzne : s z ≠ -(s z) := by
    rcases hzsign with h | h <;> rw [h] <;> norm_num
  set A := T.filter fun y => s y = s z with hA
  set B := T.filter fun y => s y = -(s z) with hB
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    rintro y - h1 h2
    rw [h1] at h2
    exact hzne h2
  have hunion : A ∪ B = T := by
    ext y
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases hmem y h with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
  have hcardAB : A.card + B.card = q - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, hTcard]
  have hsum : (A.card : ℤ) * s z + (B.card : ℤ) * (-(s z)) = ((q : ℤ) - 5) * s z := by
    have h1 : ∑ y ∈ A, s y = (A.card : ℤ) * s z := by
      rw [Finset.sum_congr rfl (fun y hy => (Finset.mem_filter.mp hy).2)]
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ y ∈ B, s y = (B.card : ℤ) * (-(s z)) := by
      rw [Finset.sum_congr rfl (fun y hy => (Finset.mem_filter.mp hy).2)]
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 := hDs z
    rw [← hT, ← hunion, Finset.sum_union hdisj, h1, h2] at h3
    exact h3
  have hdiff : (A.card : ℤ) - (B.card : ℤ) = (q : ℤ) - 5 := by
    rcases hzsign with h | h <;> rw [h] at hsum <;> nlinarith [hsum]
  have hq' : (q : ℤ) ≥ 5 := by exact_mod_cast hq
  constructor
  · omega
  · omega

end DefectDegrees

section Alternation

set_option linter.unusedSectionVars false

variable [DecidableRel (antipodalGraph G).Adj]
variable [DecidableRel (triangleFreeEdgeGraph G).Adj]
variable [Fintype (secondOrderDefectGraph G).ConnectedComponent]
variable [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]

/-- **Internal alternation.**  On a size-two component with the alternating
eigenline, every vertex has exactly two internal `G`-neighbours and both
carry the opposite sign. -/
theorem internal_alternation (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    {v : V} (hv : v ∈ c.supp) :
    (componentNeighborFinset G (secondOrderDefectGraph G) c v).card = 2 ∧
    ∀ z ∈ componentNeighborFinset G (secondOrderDefectGraph G) c v,
      s z = -(s v) := by
  classical
  set I := componentNeighborFinset G (secondOrderDefectGraph G) c v with hI
  have hIcard : I.card = 2 := by
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard c c hv
    rw [hc] at h
    have hqpos : 0 < q := by omega
    exact Nat.eq_of_mul_eq_mul_left hqpos h
  have hImem : ∀ z ∈ I, z ∈ c.supp ∧ G.Adj v z := by
    intro z hz
    rw [hI, componentNeighborFinset, Finset.mem_filter] at hz
    exact ⟨(SimpleGraph.ConnectedComponent.mem_supp_iff c z).mpr hz.2,
      (G.mem_neighborFinset v z).mp hz.1⟩
  -- the neighbour sum localizes to I
  have hsum : ∑ z ∈ I, s z = -2 * s v := by
    have h := hA_in v hv
    rw [← h]
    apply Finset.sum_subset
    · intro z hz
      rw [hI, componentNeighborFinset] at hz
      exact Finset.mem_filter.mp hz |>.1
    · intro z hz hzI
      apply hs_out
      intro hzc
      apply hzI
      rw [hI, componentNeighborFinset, Finset.mem_filter]
      exact ⟨hz, (SimpleGraph.ConnectedComponent.mem_supp_iff c z).mp hzc⟩
  -- two ±1 values summing to -2·(±1) are both the opposite sign
  obtain ⟨z₁, z₂, hne, hIeq⟩ := Finset.card_eq_two.mp hIcard
  have h1 := hs_in z₁ (hImem z₁ (by rw [hIeq]; simp)).1
  have h2 := hs_in z₂ (hImem z₂ (by rw [hIeq]; simp)).1
  have hv' := hs_in v hv
  have hsum2 : s z₁ + s z₂ = -2 * s v := by
    rw [hIeq] at hsum
    rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton] at hsum
    exact hsum
  refine ⟨hIcard, ?_⟩
  intro z hz
  rw [hIeq] at hz
  rcases Finset.mem_insert.mp hz with rfl | hz'
  · rcases h1 with h | h <;> rcases h2 with h' | h' <;> rcases hv' with h'' | h'' <;>
      rw [h, h''] <;> rw [h, h', h''] at hsum2 <;> omega
  · rcases Finset.mem_singleton.mp hz' with rfl
    rcases h1 with h | h <;> rcases h2 with h' | h' <;> rcases hv' with h'' | h'' <;>
      rw [h', h''] <;> rw [h, h', h''] at hsum2 <;> omega

/-- Same-side pairs are never `G`-adjacent. -/
theorem sameSign_not_adj (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    {z z' : V} (hz : z ∈ c.supp) (hz' : z' ∈ c.supp)
    (hsign : s z' = s z) : ¬ G.Adj z z' := by
  intro hadj
  have h := (internal_alternation G hfree hq hreg hcard c hc s hs_in hs_out
    hA_in hz).2 z' ?_
  · rcases hs_in z hz with h1 | h1 <;> rw [h1] at h hsign <;> rw [hsign] at h <;>
      norm_num at h
  · rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset z z').mpr hadj,
      (SimpleGraph.ConnectedComponent.mem_supp_iff c z').mp hz'⟩

/-- **The census: every common neighbour of a same-sign pair lies in the
component.**  Equivalently, every exterior vertex adjacent to two component
vertices sees one `+1` and one `-1`. -/
theorem sameSign_common_mem_supp (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    {z z' u : V} (hz : z ∈ c.supp) (hz' : z' ∈ c.supp)
    (hne : z' ≠ z) (hsign : s z' = s z)
    (huz : G.Adj u z) (huz' : G.Adj u z') : u ∈ c.supp := by
  classical
  by_contra huc
  -- the same-sign class of z, without z
  set SC := Finset.univ.filter fun y => y ∈ c.supp ∧ s y = s z with hSC
  have hSCcard : SC.card = q := by
    obtain ⟨hP, hN⟩ := signClass_card_eq G c hc s hs_in hs_out hsum
    rcases hs_in z hz with h | h <;> rw [hSC, h]
    · exact hN
    · exact hP
  have hzSC : z ∈ SC := by
    rw [hSC, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hz, rfl⟩
  set SameZ := SC.erase z with hSameZ
  have hSameZcard : SameZ.card = q - 1 := by
    rw [hSameZ, Finset.card_erase_of_mem hzSC, hSCcard]
  -- A: same-sign defect neighbours of z
  set A := ((secondOrderDefectGraph G).neighborFinset z).filter
    (fun y => s y = s z) with hA
  have hAcard : A.card = q - 3 :=
    (sameSide_defect_degree G hfree hq hreg hcard c s hs_in hDs hz).1
  have hAsub : A ⊆ SameZ := by
    intro y hy
    rw [hA, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨hadj, hsy⟩ := hy
    rw [hSameZ, Finset.mem_erase, hSC, Finset.mem_filter]
    exact ⟨fun h => (secondOrderDefectGraph G).irrefl (h ▸ hadj),
      Finset.mem_univ _, defect_neighbor_mem_supp G c hz hadj, hsy⟩
  -- B: other internal neighbours across z's internal pair
  obtain ⟨hI2, hIsign⟩ := internal_alternation G hfree (by omega) hreg hcard
    c hc s hs_in hs_out hA_in hz
  set I := componentNeighborFinset G (secondOrderDefectGraph G) c z with hI
  set B := (I.biUnion fun w =>
    componentNeighborFinset G (secondOrderDefectGraph G) c w).erase z with hB
  have hImem : ∀ w ∈ I, w ∈ c.supp ∧ G.Adj z w := by
    intro w hw
    rw [hI, componentNeighborFinset, Finset.mem_filter] at hw
    exact ⟨(SimpleGraph.ConnectedComponent.mem_supp_iff c w).mpr hw.2,
      (G.mem_neighborFinset z w).mp hw.1⟩
  have hBmem : ∀ y ∈ B, ∃ w ∈ I, G.Adj w y ∧ y ≠ z := by
    intro y hy
    rw [hB, Finset.mem_erase, Finset.mem_biUnion] at hy
    obtain ⟨hyz, w, hw, hyw⟩ := hy
    rw [componentNeighborFinset, Finset.mem_filter] at hyw
    exact ⟨w, hw, (G.mem_neighborFinset w y).mp hyw.1, hyz⟩
  have hBsub : B ⊆ SameZ := by
    intro y hy
    obtain ⟨w, hw, hadj, hyz⟩ := hBmem y hy
    obtain ⟨hwsupp, hzw⟩ := hImem w hw
    -- y is an internal neighbour of w, so s y = -(s w) = s z
    obtain ⟨-, hwsign⟩ := internal_alternation G hfree (by omega) hreg hcard
      c hc s hs_in hs_out hA_in hwsupp
    have hy1 : s y = -(s w) := by
      apply hwsign
      rw [componentNeighborFinset, Finset.mem_filter]
      refine ⟨(G.mem_neighborFinset w y).mpr hadj, ?_⟩
      have hysupp : y ∈ c.supp := by
        rw [hB, Finset.mem_erase, Finset.mem_biUnion] at hy
        obtain ⟨-, w', hw', hyw'⟩ := hy
        rw [componentNeighborFinset, Finset.mem_filter] at hyw'
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mpr hyw'.2
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mp hysupp
    have hz1 : s w = -(s z) := hIsign w hw
    rw [hSameZ, Finset.mem_erase, hSC, Finset.mem_filter]
    refine ⟨hyz, Finset.mem_univ _, ?_, by rw [hy1, hz1]; ring⟩
    obtain ⟨w', hw', hyw'⟩ := Finset.mem_biUnion.mp (Finset.mem_of_mem_erase (hB ▸ hy))
    rw [componentNeighborFinset, Finset.mem_filter] at hyw'
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mpr hyw'.2
  -- defect adjacency kills all common neighbours
  have hDnoCommon : ∀ y : V, (secondOrderDefectGraph G).Adj z y →
      (G.neighborFinset z ∩ G.neighborFinset y).card = 0 := by
    intro y hadj
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hadj with h | h
    · exact ((mem_antipodalNeighbors G z y).mp
        ((antipodalGraph_adj G z y).mp h)).2.2
    · exact ((mem_triangleFreeNeighbors G z y).mp
        ((triangleFreeEdgeGraph_adj G z y).mp h)).2
  have hBcard : B.card = 2 := by
    obtain ⟨w₁, w₂, hw12, hIeq⟩ := Finset.card_eq_two.mp hI2
    have hw₁I : w₁ ∈ I := by rw [hIeq]; simp
    have hw₂I : w₂ ∈ I := by rw [hIeq]; simp
    have hzmem : ∀ w ∈ I, z ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c w := by
      intro w hw
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset w z).mpr (hImem w hw).2.symm,
        (SimpleGraph.ConnectedComponent.mem_supp_iff c z).mp hz⟩
    have hpair : ∀ w ∈ I, ∃ o, o ≠ z ∧
        componentNeighborFinset G (secondOrderDefectGraph G) c w = {z, o} := by
      intro w hw
      have h2 := (internal_alternation G hfree (by omega) hreg hcard c hc s
        hs_in hs_out hA_in (hImem w hw).1).1
      obtain ⟨a, b, hab, habeq⟩ := Finset.card_eq_two.mp h2
      have hzmem' := hzmem w hw
      rw [habeq, Finset.mem_insert, Finset.mem_singleton] at hzmem'
      rcases hzmem' with rfl | rfl
      · exact ⟨b, fun h => hab h.symm, by rw [habeq]⟩
      · exact ⟨a, fun h => hab h, by
          rw [habeq]
          ext t
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto⟩
    obtain ⟨o₁, ho₁z, heq₁⟩ := hpair w₁ hw₁I
    obtain ⟨o₂, ho₂z, heq₂⟩ := hpair w₂ hw₂I
    have hBeq : B = {o₁, o₂} := by
      rw [hB, hIeq]
      rw [Finset.biUnion_insert, Finset.singleton_biUnion, heq₁, heq₂]
      ext t
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨htz, (rfl | rfl) | (rfl | rfl)⟩
        · exact absurd rfl htz
        · exact Or.inl rfl
        · exact absurd rfl htz
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨ho₁z, Or.inl (Or.inr rfl)⟩
        · exact ⟨ho₂z, Or.inr (Or.inr rfl)⟩
    have ho12 : o₁ ≠ o₂ := by
      intro h
      subst h
      -- w₁ and w₂ are two distinct common neighbours of z and o₁
      have hcommon := common_le_one_of_not_containsC4 hfree z o₁ (Ne.symm ho₁z)
      have hw₁mem : w₁ ∈ G.neighborFinset z ∩ G.neighborFinset o₁ := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          SimpleGraph.mem_neighborFinset]
        constructor
        · exact (hImem w₁ hw₁I).2
        · have : o₁ ∈ componentNeighborFinset G (secondOrderDefectGraph G) c w₁ := by
            rw [heq₁]; simp
          rw [componentNeighborFinset, Finset.mem_filter,
            SimpleGraph.mem_neighborFinset] at this
          exact this.1.symm
      have hw₂mem : w₂ ∈ G.neighborFinset z ∩ G.neighborFinset o₁ := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          SimpleGraph.mem_neighborFinset]
        constructor
        · exact (hImem w₂ hw₂I).2
        · have : o₁ ∈ componentNeighborFinset G (secondOrderDefectGraph G) c w₂ := by
            rw [heq₂]; simp
          rw [componentNeighborFinset, Finset.mem_filter,
            SimpleGraph.mem_neighborFinset] at this
          exact this.1.symm
      have : 2 ≤ (G.neighborFinset z ∩ G.neighborFinset o₁).card := by
        have := Finset.card_le_card (Finset.insert_subset hw₁mem
          (Finset.singleton_subset_iff.mpr hw₂mem))
        rwa [Finset.card_insert_of_notMem (by simpa using hw12),
          Finset.card_singleton] at this
      omega
    rw [hBeq, Finset.card_insert_of_notMem (by simpa using ho12),
      Finset.card_singleton]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    obtain ⟨w, hw, hadj, -⟩ := hBmem y hyB
    rw [hA, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hyA
    have hcz := hDnoCommon y hyA.1
    have hwmem : w ∈ G.neighborFinset z ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨(hImem w hw).2, hadj.symm⟩
    rw [Finset.card_eq_zero] at hcz
    rw [hcz] at hwmem
    exact absurd hwmem (Finset.notMem_empty w)
  -- the union fills SameZ
  have hunion_sub : A ∪ B ⊆ SameZ := Finset.union_subset hAsub hBsub
  have hunion_eq : A ∪ B = SameZ := by
    apply Finset.eq_of_subset_of_card_le hunion_sub
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard, hSameZcard]
    omega
  -- locate z'
  have hz'SameZ : z' ∈ SameZ := by
    rw [hSameZ, Finset.mem_erase, hSC, Finset.mem_filter]
    exact ⟨hne, Finset.mem_univ _, hz', hsign⟩
  rw [← hunion_eq, Finset.mem_union] at hz'SameZ
  rcases hz'SameZ with hz'A | hz'B
  · -- z' defect-adjacent to z: no common neighbours, but u is one
    rw [hA, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hz'A
    have hcz := hDnoCommon z' hz'A.1
    have humem : u ∈ G.neighborFinset z ∩ G.neighborFinset z' := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨huz.symm, huz'.symm⟩
    rw [Finset.card_eq_zero] at hcz
    rw [hcz] at humem
    exact absurd humem (Finset.notMem_empty u)
  · -- z' reached through an internal common neighbour w; u = w ∈ supp
    obtain ⟨w, hw, hadj, -⟩ := hBmem z' hz'B
    have hcommon := common_le_one_of_not_containsC4 hfree z z' (Ne.symm hne)
    have humem : u ∈ G.neighborFinset z ∩ G.neighborFinset z' := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨huz.symm, huz'.symm⟩
    have hwmem : w ∈ G.neighborFinset z ∩ G.neighborFinset z' := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨(hImem w hw).2, hadj.symm⟩
    have huw : u = w := by
      by_contra hne'
      have : 2 ≤ (G.neighborFinset z ∩ G.neighborFinset z').card := by
        have := Finset.card_le_card (Finset.insert_subset humem
          (Finset.singleton_subset_iff.mpr hwmem))
        rwa [Finset.card_insert_of_notMem (by simpa using hne'),
          Finset.card_singleton] at this
      omega
    exact huc (huw ▸ (hImem w hw).1)

/-- **Exterior labels.**  Every vertex outside the block has exactly one
positive and one negative neighbour in it. -/
theorem exterior_labels (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    {u : V} (hu : u ∉ c.supp) :
    ∃ p n : V, p ∈ c.supp ∧ n ∈ c.supp ∧ s p = 1 ∧ s n = -1 ∧
      componentNeighborFinset G (secondOrderDefectGraph G) c u = {p, n} := by
  classical
  have hI2 : (componentNeighborFinset G (secondOrderDefectGraph G) c u).card = 2 := by
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (by omega) hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk u) c
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ u |>.mpr rfl)
    rw [hc] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  obtain ⟨a, b, hab, habeq⟩ := Finset.card_eq_two.mp hI2
  have hmem : ∀ y ∈ componentNeighborFinset G (secondOrderDefectGraph G) c u,
      y ∈ c.supp ∧ G.Adj u y := by
    intro y hy
    rw [componentNeighborFinset, Finset.mem_filter] at hy
    exact ⟨(SimpleGraph.ConnectedComponent.mem_supp_iff c y).mpr hy.2,
      (G.mem_neighborFinset u y).mp hy.1⟩
  have ha := hmem a (by rw [habeq]; simp)
  have hb := hmem b (by rw [habeq]; simp)
  -- the two neighbours cannot share a sign (census)
  have hsigns : s a ≠ s b := by
    intro hsame
    exact hu (sameSign_common_mem_supp G hfree hq hreg hcard c hc s hs_in
      hs_out hsum hA_in hDs hb.1 ha.1 hab hsame hb.2 ha.2)
  rcases hs_in a ha.1 with h1 | h1 <;> rcases hs_in b hb.1 with h2 | h2
  · exact absurd (h1.trans h2.symm) hsigns
  · exact ⟨b, a, hb.1, ha.1, h2, h1, by
      rw [habeq]
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto⟩
  · exact ⟨a, b, ha.1, hb.1, h1, h2, habeq⟩
  · exact absurd (h1.trans h2.symm) hsigns

end Alternation

end Erdos85
