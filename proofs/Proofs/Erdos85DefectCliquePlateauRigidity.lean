import Proofs.Erdos85DefectCliqueEscapeHatch
import Proofs.Erdos85ConflictDefectDuality
import Proofs.Erdos85SafeSetCounting
import Proofs.Erdos85PositiveExcessLocalParity

/-!
# Defect-clique rigidity in a nonextendable graph

The escape-hatch surgery is most naturally triggered by a clique in the
second-order defect graph.  Conflict--defect duality turns such a clique
into the pairwise zero-common-neighbor set required by the surgery.  Hence,
under one-step nonextension, every sufficiently large defect clique must
meet or reach every open neighborhood within two graph edges.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A clique in the second-order defect graph is a safe attachment set in
the original graph. -/
theorem commonNeighborIndependent_of_secondOrderDefect_isClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (C : Finset V)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V)) :
    CommonNeighborIndependent G C := by
  have hdual := commonNeighborConflict_compl_eq_secondOrderDefectGraph
    G hfree
  apply (commonNeighborIndependent_iff_isIndepSet G C).2
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab hconf
  have hD : (secondOrderDefectGraph G).Adj a b := hclique ha hb hab
  have hcomp : (commonNeighborConflict G)ᶜ.Adj a b := by
    rw [hdual]
    exact hD
  rw [SimpleGraph.compl_adj] at hcomp
  exact hcomp.2 hconf

/-- If a safe set is also independent in `G`, then the set itself is
disjoint from all of its already pairwise-disjoint open neighborhoods. -/
theorem CommonNeighborIndependent.card_add_sum_degrees_le_card_of_isIndepSet
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hsafe : CommonNeighborIndependent G C)
    (hind : G.IsIndepSet (C : Set V)) :
    C.card + ∑ x ∈ C, G.degree x ≤ Fintype.card V := by
  classical
  let X := {x : V // x ∈ C}
  let N : X → Type _ := fun x => {v : V // v ∈ G.neighborFinset x.1}
  let f : X ⊕ (Σ x : X, N x) → V := fun p =>
    Sum.elim Subtype.val (fun q => q.2.1) p
  rw [SimpleGraph.isIndepSet_iff] at hind
  have hnoAdj : ∀ x ∈ C, ∀ y ∈ C, ¬ G.Adj x y := by
    intro x hx y hy hxy
    by_cases hne : x = y
    · subst y
      exact G.loopless.irrefl x hxy
    · exact hind hx hy hne hxy
  have hf : Function.Injective f := by
    rintro (x | ⟨x, v⟩) (y | ⟨y, w⟩) heq
    · exact congrArg Sum.inl (Subtype.ext heq)
    · exfalso
      change x.1 = w.1 at heq
      exact hnoAdj y.1 y.2 x.1 x.2
        (by simpa [heq] using (G.mem_neighborFinset y.1 w.1).mp w.2)
    · exfalso
      change v.1 = y.1 at heq
      exact hnoAdj x.1 x.2 y.1 y.2
        (by simpa [heq] using (G.mem_neighborFinset x.1 v.1).mp v.2)
    · have hvw : v.1 = w.1 := heq
      have hxy : x.1 = y.1 := by
        by_contra hxy
        have hz : v.1 ∈ G.neighborFinset x.1 ∩
            G.neighborFinset y.1 := by
          exact Finset.mem_inter.mpr ⟨v.2, hvw ▸ w.2⟩
        have hempty := hsafe x.2 y.2 hxy
        rw [Finset.card_eq_zero] at hempty
        exact Finset.notMem_empty v.1 (hempty ▸ hz)
      have hxySub : x = y := Subtype.ext hxy
      cases hxySub
      have hv : v = w := Subtype.ext hvw
      cases hv
      rfl
  have hcard := Fintype.card_le_of_injective f hf
  change Fintype.card (X ⊕ (Σ x : X, N x)) ≤ Fintype.card V at hcard
  rw [Fintype.card_sum, Fintype.card_sigma] at hcard
  have hCX : Fintype.card X = C.card := by simp [X]
  have hsum : (∑ x : X, Fintype.card (N x)) =
      ∑ x ∈ C, G.degree x := by
    rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [N]
    rw [Fintype.card_coe, ← SimpleGraph.card_neighborFinset_eq_degree]
  rwa [hCX, hsum] at hcard

/-- General packing identity with the exact correction for vertices of the
safe set that lie in one of its open neighborhoods.  This is the form needed
when a defect clique contains triangle-free edges of the original graph. -/
theorem CommonNeighborIndependent.card_add_sum_degrees_le_card_add_overlap
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hsafe : CommonNeighborIndependent G C) :
    C.card + ∑ x ∈ C, G.degree x ≤ Fintype.card V +
      (C ∩ C.biUnion (fun x ↦ G.neighborFinset x)).card := by
  classical
  let U := C.biUnion fun x ↦ G.neighborFinset x
  have hpair : (C : Set V).PairwiseDisjoint fun x ↦ G.neighborFinset x := by
    intro x hx y hy hxy
    change Disjoint (G.neighborFinset x) (G.neighborFinset y)
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hz : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨hzx, hzy⟩
    have hempty := hsafe hx hy hxy
    rw [Finset.card_eq_zero] at hempty
    exact Finset.notMem_empty z (hempty ▸ hz)
  have hUcard : U.card = ∑ x ∈ C, G.degree x := by
    change (C.biUnion fun x ↦ G.neighborFinset x).card = _
    rw [Finset.card_biUnion hpair]
    apply Finset.sum_congr rfl
    intro x _
    exact G.card_neighborFinset_eq_degree x
  have htotal : (C ∪ U).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  have hie := Finset.card_union_add_card_inter C U
  change C.card + ∑ x ∈ C, G.degree x ≤
    Fintype.card V + (C ∩ U).card
  omega

/-- The graph induced on a common-neighbor-independent set has maximum
degree at most one: two internal neighbors would have their center as a
common neighbor. -/
theorem CommonNeighborIndependent.degree_induce_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hsafe : CommonNeighborIndependent G C)
    (x : {z : V // z ∈ (C : Set V)}) :
    (G.induce (C : Set V)).degree x ≤ 1 := by
  classical
  rw [← (G.induce (C : Set V)).card_neighborFinset_eq_degree]
  rw [Finset.card_le_one]
  intro a ha b hb
  apply Subtype.ext
  by_contra hab
  have hxa : G.Adj x.1 a.1 := by
    simpa [SimpleGraph.mem_neighborFinset] using ha
  have hxb : G.Adj x.1 b.1 := by
    simpa [SimpleGraph.mem_neighborFinset] using hb
  have hzero := hsafe (Finset.mem_coe.mp a.2) (Finset.mem_coe.mp b.2)
    hab
  rw [Finset.card_eq_zero] at hzero
  have hxMem : x.1 ∈ G.neighborFinset a.1 ∩ G.neighborFinset b.1 := by
    rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
    exact ⟨hxa.symm, hxb.symm⟩
  exact Finset.notMem_empty x.1 (hzero ▸ hxMem)

/-- The overlap correction in the general safe-packing identity is even:
it is exactly the set of non-isolated vertices of the matching induced on
the safe set. -/
theorem CommonNeighborIndependent.even_card_overlap
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hsafe : CommonNeighborIndependent G C) :
    Even (C ∩ C.biUnion (fun x ↦ G.neighborFinset x)).card := by
  classical
  let H := G.induce (C : Set V)
  let P := (Finset.univ : Finset {z : V // z ∈ (C : Set V)}).filter
    (fun x ↦ H.degree x = 1)
  have hle : ∀ x, H.degree x ≤ 1 :=
    fun x ↦ hsafe.degree_induce_le_one G C x
  have hcard : (C ∩ C.biUnion (fun x ↦ G.neighborFinset x)).card =
      P.card := by
    apply Finset.card_bij
        (fun x hx ↦ (⟨x, Finset.mem_coe.mpr (Finset.mem_inter.mp hx).1⟩ :
          {z : V // z ∈ (C : Set V)}))
    · intro x hx
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      have hxU := (Finset.mem_inter.mp hx).2
      rw [Finset.mem_biUnion] at hxU
      obtain ⟨a, haC, hax⟩ := hxU
      have hpos : 0 < H.degree
          (⟨x, Finset.mem_coe.mpr (Finset.mem_inter.mp hx).1⟩ :
            {z : V // z ∈ (C : Set V)}) := by
        rw [H.degree_pos_iff_exists_adj]
        exact ⟨⟨a, Finset.mem_coe.mpr haC⟩,
          (G.mem_neighborFinset a x).mp hax |>.symm⟩
      have := hle
        (⟨x, Finset.mem_coe.mpr (Finset.mem_inter.mp hx).1⟩ :
          {z : V // z ∈ (C : Set V)})
      omega
    · intro x hx y hy hxy
      exact congrArg Subtype.val hxy
    · intro y hy
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hpos : 0 < H.degree y := by omega
      obtain ⟨a, hya⟩ := (H.degree_pos_iff_exists_adj y).mp hpos
      refine ⟨y.1, ?_, rfl⟩
      rw [Finset.mem_inter, Finset.mem_biUnion]
      exact ⟨Finset.mem_coe.mp y.2,
        ⟨a.1, Finset.mem_coe.mp a.2,
          (G.mem_neighborFinset a.1 y.1).mpr hya.symm⟩⟩
  have hPodd : P = (Finset.univ :
      Finset {z : V // z ∈ (C : Set V)}).filter
        (fun x ↦ Odd (H.degree x)) := by
    ext x
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rw [hx]
      exact odd_one
    · rintro ⟨k, hk⟩
      have := hle x
      omega
  rw [hcard, hPodd]
  exact H.even_card_odd_degree_vertices

/-- Quantitative large-clique constraint across the whole positive-excess
band.  Any deficit below the top excess `e=d-4` must be paid for by vertices
of the defect clique that are incident with an internal original-graph edge. -/
theorem degree_le_four_add_excess_add_internalOverlap_of_large_defectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V)) :
    d ≤ 4 + e +
      (C ∩ C.biUnion (fun x ↦ G.neighborFinset x)).card := by
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  have hpack := hsafe.card_add_sum_degrees_le_card_add_overlap G C
  have hsum : (∑ x ∈ C, G.degree x) = C.card * d := by
    simp_rw [hreg]
    simp
  rw [hsum, hCcard, hcard] at hpack
  have hmul : (d - 1) * d = d * (d - 1) := Nat.mul_comm _ _
  rw [hmul] at hpack
  omega

/-- Parity rounds the overlap bound up by one when the deficit below the top
excess is odd.  In particular, an odd-degree exact-boundary clique must have
at least `d-3` internally incident vertices, not merely `d-4`. -/
theorem degree_add_one_le_four_add_excess_add_internalOverlap_of_odd_deficit
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (hodd : Odd (d - (4 + e)))
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V)) :
    d + 1 ≤ 4 + e +
      (C ∩ C.biUnion (fun x ↦ G.neighborFinset x)).card := by
  have hbound :=
    degree_le_four_add_excess_add_internalOverlap_of_large_defectClique
      G hfree hd hcard hreg C hCcard hclique
  have heven :=
    (commonNeighborIndependent_of_secondOrderDefect_isClique
      G hfree C hclique).even_card_overlap G C
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven
  omega

/-- Equality in the preceding packing bound gives an exact partition: every
vertex is either in the safe independent set or adjacent to one of its
members. -/
theorem CommonNeighborIndependent.mem_or_exists_adj_of_count_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hsafe : CommonNeighborIndependent G C)
    (hind : G.IsIndepSet (C : Set V))
    (hcount : C.card + ∑ x ∈ C, G.degree x = Fintype.card V)
    (v : V) : v ∈ C ∨ ∃ c ∈ C, G.Adj c v := by
  classical
  let U := C.biUnion fun c ↦ G.neighborFinset c
  have hpair : (C : Set V).PairwiseDisjoint fun c ↦ G.neighborFinset c := by
    intro x hx y hy hxy
    change Disjoint (G.neighborFinset x) (G.neighborFinset y)
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hz : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨hzx, hzy⟩
    have hempty := hsafe hx hy hxy
    rw [Finset.card_eq_zero] at hempty
    exact Finset.notMem_empty z (hempty ▸ hz)
  have hUcard : U.card = ∑ x ∈ C, G.degree x := by
    change (C.biUnion fun c ↦ G.neighborFinset c).card = _
    rw [Finset.card_biUnion hpair]
    apply Finset.sum_congr rfl
    intro x _
    exact G.card_neighborFinset_eq_degree x
  rw [SimpleGraph.isIndepSet_iff] at hind
  have hdisj : Disjoint C U := by
    change Disjoint C (C.biUnion fun c ↦ G.neighborFinset c)
    rw [Finset.disjoint_left]
    intro x hx hxU
    rw [Finset.mem_biUnion] at hxU
    obtain ⟨y, hy, hyx⟩ := hxU
    have hadj : G.Adj y x := (G.mem_neighborFinset y x).mp hyx
    by_cases hxy : y = x
    · subst y
      exact G.loopless.irrefl x hadj
    · exact hind hy hx hxy hadj
  have hCUcard : (C ∪ U).card = Fintype.card V := by
    rw [Finset.card_union_of_disjoint hdisj, hUcard, hcount]
  have hCU : C ∪ U = Finset.univ := Finset.eq_univ_of_card _ hCUcard
  have hv : v ∈ C ∪ U := by rw [hCU]; simp
  rcases Finset.mem_union.mp hv with hvC | hvU
  · exact Or.inl hvC
  · right
    change v ∈ C.biUnion (fun c ↦ G.neighborFinset c) at hvU
    rw [Finset.mem_biUnion] at hvU
    obtain ⟨c, hc, hcv⟩ := hvU
    exact ⟨c, hc, (G.mem_neighborFinset c v).mp hcv⟩

/-- A defect clique of size `d-1` can occur in the regular positive-excess
band only at its top endpoint `e=d-4`.  This is forced directly by the
regular defect degree `e+2`; no independence assumption in `G` is needed. -/
theorem excess_eq_sub_four_of_large_secondOrderDefectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V)) :
    e = d - 4 := by
  have hCpos : 0 < C.card := by rw [hCcard]; omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hCpos
  have hsub : C.erase c ⊆
      (secondOrderDefectGraph G).neighborFinset c := by
    intro y hy
    have hy' := Finset.mem_erase.mp hy
    apply ((secondOrderDefectGraph G).mem_neighborFinset c y).mpr
    exact hclique hc hy'.2 hy'.1.symm
  have hcardLe := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hc, hCcard,
    (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcard c] at hcardLe
  omega

/-- Independent-set specialization retained as a compatibility interface. -/
theorem excess_eq_sub_four_of_independent_large_secondOrderDefectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (_hind : G.IsIndepSet (C : Set V)) :
    e = d - 4 := by
  exact excess_eq_sub_four_of_large_secondOrderDefectClique
    G hfree hd he hcard hreg C hCcard hclique

/-- At that forced top endpoint the independent defect clique and its
pairwise-disjoint open neighborhoods exhaust the entire cardinal budget. -/
theorem independent_large_secondOrderDefectClique_count_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V)) :
    C.card + ∑ x ∈ C, G.degree x = Fintype.card V := by
  have heq :=
    excess_eq_sub_four_of_independent_large_secondOrderDefectClique
      G hfree hd he hcard hreg C hCcard hclique hind
  have hsum : (∑ x ∈ C, G.degree x) = C.card * d := by
    simp_rw [hreg]
    simp
  rw [hsum, hCcard, hcard, heq]
  have hmul : (d - 1) * d = d * (d - 1) := Nat.mul_comm _ _
  rw [hmul]
  omega

/-- Consequently, at the forced top excess an independent `D`-clique of
size `d-1` is an exact dominating part: every other vertex has a neighbor
in the clique. -/
theorem mem_or_exists_adj_of_independent_large_secondOrderDefectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V)) (v : V) :
    v ∈ C ∨ ∃ c ∈ C, G.Adj c v := by
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  apply hsafe.mem_or_exists_adj_of_count_eq_card G C hind
  exact independent_large_secondOrderDefectClique_count_eq_card
    G hfree hd he hcard hreg C hCcard hclique hind

/-- At the top excess, the defect neighborhood of a clique vertex consists
exactly of the other clique vertices. -/
theorem secondOrderDefect_neighborFinset_eq_erase_of_large_clique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    {c : V} (hc : c ∈ C) :
    (secondOrderDefectGraph G).neighborFinset c = C.erase c := by
  have heq :=
    excess_eq_sub_four_of_large_secondOrderDefectClique
      G hfree hd he hcard hreg C hCcard hclique
  have hDdegree : (secondOrderDefectGraph G).degree c = d - 2 := by
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcard c
    rw [heq] at h
    omega
  have hsub : C.erase c ⊆
      (secondOrderDefectGraph G).neighborFinset c := by
    intro y hy
    have hy' := Finset.mem_erase.mp hy
    apply ((secondOrderDefectGraph G).mem_neighborFinset c y).mpr
    exact hclique hc hy'.2 hy'.1.symm
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    hDdegree, Finset.card_erase_of_mem hc, hCcard]
  omega

/-- Compatibility wrapper for the earlier independent-clique interface. -/
theorem secondOrderDefect_neighborFinset_eq_erase_of_independent_large_clique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (_hind : G.IsIndepSet (C : Set V)) {c : V} (hc : c ∈ C) :
    (secondOrderDefectGraph G).neighborFinset c = C.erase c :=
  secondOrderDefect_neighborFinset_eq_erase_of_large_clique
    G hfree hd he hcard hreg C hCcard hclique hc

/-- Therefore no clique vertex is incident with a triangle-free defect
edge; all of its defect neighbors are antipodal. -/
theorem triangleFreeNeighbors_card_eq_zero_of_independent_large_defectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V)) {c : V} (hc : c ∈ C) :
    (triangleFreeNeighbors G c).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have hyD : y ∈ (secondOrderDefectGraph G).neighborFinset c := by
    rw [secondOrderDefectGraph_neighborFinset]
    exact Finset.mem_union_right _ hy
  rw [secondOrderDefect_neighborFinset_eq_erase_of_large_clique
    G hfree hd he hcard hreg C hCcard hclique hc] at hyD
  have hyC := (Finset.mem_erase.mp hyD).2
  have hcy : G.Adj c y := (mem_triangleFreeNeighbors G c y).mp hy |>.1
  rw [SimpleGraph.isIndepSet_iff] at hind
  exact hind hc hyC (G.ne_of_adj hcy) hcy

/-- If no edge at `c` is triangle-free, then the graph induced by the open
neighborhood of `c` is 1-regular.  The upper bound is the usual local
matching consequence of `C₄`-freeness; the absence of triangle-free edges
rules out isolated vertices. -/
theorem degree_induce_neighborSet_eq_one_of_triangleFreeNeighbors_card_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (c : V)
    (hzero : (triangleFreeNeighbors G c).card = 0)
    (y : {z : V // z ∈ G.neighborSet c}) :
    (G.induce (G.neighborSet c)).degree y = 1 := by
  have hle : (G.induce (G.neighborSet c)).degree y ≤ 1 := by
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree c y.1
      (G.ne_of_adj y.2)
  have hne : (G.induce (G.neighborSet c)).degree y ≠ 0 := by
    intro hdegzero
    have hcommonzero :
        (G.neighborFinset c ∩ G.neighborFinset y.1).card = 0 := by
      rwa [degree_induce_neighborSet_eq_card_common] at hdegzero
    have hyTF : y.1 ∈ triangleFreeNeighbors G c :=
      (mem_triangleFreeNeighbors G c y.1).mpr ⟨y.2, hcommonzero⟩
    rw [Finset.card_eq_zero] at hzero
    exact Finset.notMem_empty y.1 (hzero ▸ hyTF)
  omega

/-- Every block indexed by a vertex of an extremal independent defect clique
induces a perfect matching (equivalently, is 1-regular). -/
theorem degree_induce_neighborSet_eq_one_of_independent_large_defectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V)) {c : V} (hc : c ∈ C)
    (y : {z : V // z ∈ G.neighborSet c}) :
    (G.induce (G.neighborSet c)).degree y = 1 := by
  apply degree_induce_neighborSet_eq_one_of_triangleFreeNeighbors_card_eq_zero
    G hfree c
  exact triangleFreeNeighbors_card_eq_zero_of_independent_large_defectClique
    G hfree hd he hcard hreg C hCcard hclique hind hc

/-- Every block indexed by an extremal independent defect clique meets every
vertex of any block in exactly one neighbor.  For equal indices this is the
internal perfect matching; for distinct indices it says that the bipartite
graph between the blocks is a perfect matching. -/
theorem card_common_eq_one_between_independent_large_defectClique_blocks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V))
    {c c' : V} (hc : c ∈ C) (hc' : c' ∈ C)
    (y : {z : V // z ∈ G.neighborSet c}) :
    (G.neighborFinset y.1 ∩ G.neighborFinset c').card = 1 := by
  classical
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  have hyNotC : y.1 ∉ C := by
    intro hyC
    rw [SimpleGraph.isIndepSet_iff] at hind
    exact hind hc hyC (G.ne_of_adj y.2) y.2
  have hyc' : y.1 ≠ c' := fun h ↦ hyNotC (h ▸ hc')
  have hle :
      (G.neighborFinset y.1 ∩ G.neighborFinset c').card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree y.1 c' hyc'
  by_contra hone
  have htargetZero :
      (G.neighborFinset y.1 ∩ G.neighborFinset c').card = 0 := by
    omega
  let U := insert c ((C.erase c').biUnion fun a ↦
    G.neighborFinset y.1 ∩ G.neighborFinset a)
  have hsub : G.neighborFinset y.1 ⊆ U := by
    intro z hz
    have hcover :=
      mem_or_exists_adj_of_independent_large_secondOrderDefectClique
        G hfree hd he hcard hreg C hCcard hclique hind z
    rcases hcover with hzC | ⟨a, haC, haz⟩
    · have hzc : z = c := by
        by_contra hzc
        have hempty := hsafe hc hzC (fun hcz ↦ hzc hcz.symm)
        rw [Finset.card_eq_zero] at hempty
        have hyMem : y.1 ∈ G.neighborFinset c ∩ G.neighborFinset z := by
          rw [Finset.mem_inter, G.mem_neighborFinset,
            G.mem_neighborFinset]
          exact ⟨y.2,
            (G.adj_comm z y.1).mpr ((G.mem_neighborFinset y.1 z).mp hz)⟩
        exact Finset.notMem_empty y.1 (hempty ▸ hyMem)
      simp [U, hzc]
    · have hac' : a ≠ c' := by
        intro hac'
        subst a
        have hzTarget : z ∈
            G.neighborFinset y.1 ∩ G.neighborFinset c' := by
          rw [Finset.mem_inter, G.mem_neighborFinset,
            G.mem_neighborFinset]
          exact ⟨(G.mem_neighborFinset y.1 z).mp hz, haz⟩
        rw [Finset.card_eq_zero] at htargetZero
        exact Finset.notMem_empty z (htargetZero ▸ hzTarget)
      simp only [U, Finset.mem_insert, Finset.mem_biUnion,
        Finset.mem_erase, Finset.mem_inter]
      exact Or.inr ⟨a, ⟨hac', haC⟩, hz,
        (G.mem_neighborFinset a z).mpr haz⟩
  have hpiece : ∀ a ∈ C.erase c',
      (G.neighborFinset y.1 ∩ G.neighborFinset a).card ≤ 1 := by
    intro a ha
    exact common_le_one_of_not_containsC4 hfree y.1 a
      (fun hya ↦ hyNotC (hya ▸ (Finset.mem_erase.mp ha).2))
  have hsum : (∑ a ∈ C.erase c',
      (G.neighborFinset y.1 ∩ G.neighborFinset a).card) ≤
      (C.erase c').card := by
    calc
      (∑ a ∈ C.erase c',
          (G.neighborFinset y.1 ∩ G.neighborFinset a).card) ≤
          ∑ _a ∈ C.erase c', 1 :=
        Finset.sum_le_sum fun a ha ↦ hpiece a ha
      _ = (C.erase c').card := by simp
  have hUcard : U.card ≤ 1 + (C.erase c').card := by
    calc
      U.card ≤ 1 + ((C.erase c').biUnion fun a ↦
          G.neighborFinset y.1 ∩ G.neighborFinset a).card := by
        simpa [Nat.add_comm] using Finset.card_insert_le c
          ((C.erase c').biUnion fun a ↦
            G.neighborFinset y.1 ∩ G.neighborFinset a)
      _ ≤ 1 + ∑ a ∈ C.erase c',
          (G.neighborFinset y.1 ∩ G.neighborFinset a).card := by
        exact Nat.add_le_add_left Finset.card_biUnion_le 1
      _ ≤ 1 + (C.erase c').card := Nat.add_le_add_left hsum 1
  have hdegreeLe : G.degree y.1 ≤ 1 + (C.erase c').card := by
    rw [← G.card_neighborFinset_eq_degree y.1]
    exact (Finset.card_le_card hsub).trans hUcard
  rw [hreg y.1, Finset.card_erase_of_mem hc', hCcard] at hdegreeLe
  omega

/-- The extremal block geometry is a sharp obstruction to direct attachment:
every common-neighbor-independent set has size at most `d-1`.  A safe set
meeting the anchor clique cannot contain a block vertex; a safe set avoiding
the anchors injects into the anchors by assigning each vertex its unique
dominating block. -/
theorem commonNeighborIndependent_card_le_pred_of_independent_large_defectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V))
    (S : Finset V) (hS : CommonNeighborIndependent G S) :
    S.card ≤ d - 1 := by
  classical
  by_cases hmeet : ∃ c ∈ C, c ∈ S
  · obtain ⟨c, hcC, hcS⟩ := hmeet
    have hSC : S ⊆ C := by
      intro y hyS
      by_contra hyC
      obtain ⟨a, haC, hay⟩ :=
        (mem_or_exists_adj_of_independent_large_secondOrderDefectClique
          G hfree hd he hcard hreg C hCcard hclique hind y).resolve_left hyC
      let ya : {z : V // z ∈ G.neighborSet a} := ⟨y, hay⟩
      have hone :=
        card_common_eq_one_between_independent_large_defectClique_blocks
          G hfree hd he hcard hreg C hCcard hclique hind haC hcC ya
      by_cases hyc : y = c
      · exact hyC (hyc ▸ hcC)
      · have hzero := hS hyS hcS hyc
        have hcomm : G.neighborFinset y ∩ G.neighborFinset c =
            G.neighborFinset ya.1 ∩ G.neighborFinset c := rfl
        rw [hcomm, hone] at hzero
        omega
    rw [← hCcard]
    exact Finset.card_le_card hSC
  · have hdisj : ∀ y ∈ S, y ∉ C := by
      intro y hyS hyC
      exact hmeet ⟨y, hyC, hyS⟩
    let anchor : ∀ y : {z : V // z ∈ S}, {c : V // c ∈ C} := fun y ↦
      ⟨Classical.choose
          ((mem_or_exists_adj_of_independent_large_secondOrderDefectClique
            G hfree hd he hcard hreg C hCcard hclique hind y.1).resolve_left
              (hdisj y.1 y.2)),
        (Classical.choose_spec
          ((mem_or_exists_adj_of_independent_large_secondOrderDefectClique
            G hfree hd he hcard hreg C hCcard hclique hind y.1).resolve_left
              (hdisj y.1 y.2))).1⟩
    have hanchorAdj : ∀ y : {z : V // z ∈ S},
        G.Adj (anchor y).1 y.1 := by
      intro y
      exact (Classical.choose_spec
        ((mem_or_exists_adj_of_independent_large_secondOrderDefectClique
          G hfree hd he hcard hreg C hCcard hclique hind y.1).resolve_left
            (hdisj y.1 y.2))).2
    have hinj : Function.Injective anchor := by
      intro y z hyz
      apply Subtype.ext
      by_contra hyzVal
      have hzero := hS y.2 z.2 hyzVal
      rw [Finset.card_eq_zero] at hzero
      have haMem : (anchor y).1 ∈
          G.neighborFinset y.1 ∩ G.neighborFinset z.1 := by
        rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
        exact ⟨(hanchorAdj y).symm,
          (hyz ▸ hanchorAdj z).symm⟩
      exact Finset.notMem_empty (anchor y).1 (hzero ▸ haMem)
    have hcardLe := Fintype.card_le_of_injective anchor hinj
    simpa [Fintype.card_coe, hCcard] using hcardLe

/-- The exact block geometry also forces even degree.  Indeed, for any
`c ∈ C`, the other `d-2` clique vertices exhaust the entire degree-`d-2`
defect neighborhood of `c`.  Since `C` is independent in `G`, none of these
defect neighbors is a triangle-free edge.  The local matching parity then
forces `d` even. -/
theorem even_degree_of_independent_large_secondOrderDefectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V)) :
    Even d := by
  classical
  have hCpos : 0 < C.card := by rw [hCcard]; omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hCpos
  have hTFzero :=
    triangleFreeNeighbors_card_eq_zero_of_independent_large_defectClique
      G hfree hd he hcard hreg C hCcard hclique hind hc
  have hparity := triangleFreeNeighbors_card_mod_two_eq_degree
    G hfree hreg c
  rw [hTFzero] at hparity
  exact Nat.even_iff.mpr (by omega)

/-- **Defect-clique plateau rigidity.**  In a graph with no degree-`d`
witness one order higher, every second-order-defect clique of size at least
`d-1` is entangled with every vertex: the vertex lies in the clique, is
adjacent to it, or has a neighbor adjacent to it. -/
theorem secondOrderDefectClique_entangled_of_no_witness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {n d : ℕ} (hcard : Fintype.card V = n + 1) (hd : 1 ≤ d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hnext : ¬ C4FreeMinDegreeWitness (n + 2) d)
    (C : Finset V) (hCcard : d - 1 ≤ C.card)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (u : V) :
    u ∈ C ∨ (∃ c ∈ C, G.Adj u c) ∨
      (∃ a ∈ C, ∃ b : V, G.Adj b u ∧ G.Adj a b) := by
  apply defectClique_entangled_of_no_witness
    G hcard hd hmin hfree hnext C hCcard
  intro a ha b hb hab
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  exact hsafe ha hb hab

end

end Erdos85
