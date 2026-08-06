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

/-- An independent defect clique of size `d-1` can occur in the regular
positive-excess band only at its top endpoint `e=d-4`. -/
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
    (hind : G.IsIndepSet (C : Set V)) :
    e = d - 4 := by
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  have hcount :=
    hsafe.card_add_sum_degrees_le_card_of_isIndepSet G C hind
  have hsum : (∑ x ∈ C, G.degree x) = C.card * d := by
    simp_rw [hreg]
    simp
  rw [hsum, hCcard, hcard] at hcount
  have hmul : (d - 1) * d = d * (d - 1) := Nat.mul_comm _ _
  rw [hmul] at hcount
  omega

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
    (hind : G.IsIndepSet (C : Set V)) {c : V} (hc : c ∈ C) :
    (secondOrderDefectGraph G).neighborFinset c = C.erase c := by
  have heq :=
    excess_eq_sub_four_of_independent_large_secondOrderDefectClique
      G hfree hd he hcard hreg C hCcard hclique hind
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
  rw [secondOrderDefect_neighborFinset_eq_erase_of_independent_large_clique
    G hfree hd he hcard hreg C hCcard hclique hind hc] at hyD
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
