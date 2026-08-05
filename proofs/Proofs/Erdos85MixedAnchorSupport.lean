import Proofs.Erdos85FrequencyPairMixedTransport
import Proofs.Erdos85BoundaryQuotientExcess

/-!
# Mixed-length anchor supports and the excess identity

Foundation layer for the mixed-length diagonal-anchor parity program.  The
key observation is that the boundary-quotient counting machinery is
already length-agnostic:

* the component partition is equitable
  (`secondOrder_componentNeighborFinset_card_eq`), so anchor supports have
  the quotient entries as cardinalities regardless of cycle lengths;
* the local excess identity
  (`secondOrder_componentQuotientMatrix_local_excess`) —
  `∑ e, Q c e * (Q e c - 1) = ℓ c - 3` — carries no equal-length
  hypothesis at all.

This file packages both in the mixed vocabulary: rectangular anchor
supports `mixedAnchorSupport G x v ⊆ ZMod m` for a labeled target cycle
`v : ZMod m → V`, their identification with quotient entries, agreement
with `graphCycleBlockZeroSupport` on diagonal blocks, and the mixed
excess identity in support form.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

section AnchorSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Neighbors of an anchor vertex on a labeled target cycle, recorded by
their cycle coordinate.  This is the rectangular generalization of the
zero-row support: the two cycles may have different lengths. -/
def mixedAnchorSupport (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) {m : ℕ} [NeZero m] (v : ZMod m → V) : Finset (ZMod m) :=
  Finset.univ.filter fun z ↦ G.Adj x (v z)

theorem mem_mixedAnchorSupport_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) {m : ℕ} [NeZero m] (v : ZMod m → V)
    (z : ZMod m) :
    z ∈ mixedAnchorSupport G x v ↔ G.Adj x (v z) := by
  simp [mixedAnchorSupport]

/-- On a square diagonal block the rectangular anchor support agrees with
the zero-row support of the block matrix. -/
theorem mixedAnchorSupport_eq_graphCycleBlockZeroSupport
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (u v : ZMod r → V) :
    mixedAnchorSupport G (u 0) v = graphCycleBlockZeroSupport G u v := by
  ext z
  rw [mem_mixedAnchorSupport_iff, graphCycleBlockZeroSupport,
    mem_zeroRowSupport_iff]
  simp [SimpleGraph.adjMatrix_apply]

/-- The cardinality of an anchor support is the corresponding entry of the
component quotient matrix — for anchors in any component and target
cycles of any length. -/
theorem card_mixedAnchorSupport_eq_componentQuotient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    {x : V} (hx : x ∈ c.supp) {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hv : Function.Injective v) (hvRange : Set.range v = e.supp) :
    (mixedAnchorSupport G x v).card =
      componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
  have hbij : (mixedAnchorSupport G x v).card =
      (componentNeighborFinset G (secondOrderDefectGraph G) e x).card := by
    apply Finset.card_bij (fun z _ ↦ v z)
    · intro z hz
      rw [mem_mixedAnchorSupport_iff] at hz
      rw [componentNeighborFinset, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      constructor
      · exact hz
      · have hmem : v z ∈ e.supp := by
          rw [← hvRange]
          exact ⟨z, rfl⟩
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hmem
        exact hmem
    · intro z₁ h₁ z₂ h₂ hz
      exact hv hz
    · intro y hy
      rw [componentNeighborFinset, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset] at hy
      have hmem : y ∈ e.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact hy.2
      rw [← hvRange] at hmem
      obtain ⟨z, rfl⟩ := hmem
      refine ⟨z, ?_, rfl⟩
      rw [mem_mixedAnchorSupport_iff]
      exact hy.1
  rw [hbij, componentQuotientMatrix]
  exact secondOrder_componentNeighborFinset_card_eq
    G hfree hd heven hmin hcard c e hx
    (componentRepresentative_mem (secondOrderDefectGraph G) c)

/-- **Mixed excess identity in support form.**  For any anchor component
`c` of a mixed cycle system, the anchor supports on all target cycles
satisfy the quadratic excess identity with the reverse quotient entries —
no equal-length hypothesis. -/
theorem mixed_anchorSupport_excess
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {ℓ : (secondOrderDefectGraph G).ConnectedComponent → ℕ}
    [∀ c, NeZero (ℓ c)]
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod (ℓ c) → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ e, ((mixedAnchorSupport G (u c 0) (u e)).card : ℤ) *
        ((componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ)
          - 1)) = (ℓ c : ℤ) - 3 := by
  have hanchor : u c 0 ∈ c.supp := by
    rw [← huRange c]
    exact ⟨0, rfl⟩
  have hlen : c.supp.ncard = ℓ c := by
    rw [← huRange c, Set.ncard_range_of_injective (hu c),
      Nat.card_eq_fintype_card, ZMod.card]
  have hcards : ∀ e, (mixedAnchorSupport G (u c 0) (u e)).card =
      componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
    intro e
    exact card_mixedAnchorSupport_eq_componentQuotient G hfree hd heven
      hmin hcard c e hanchor (hu e) (huRange e)
  have hlocal := secondOrder_componentQuotientMatrix_local_excess
    G hfree hd heven hmin hcard c
  rw [hlen] at hlocal
  rw [← hlocal]
  apply Finset.sum_congr rfl
  intro e _
  rw [hcards e]
  ring

/-- The total anchor mass over all components is the degree: each anchor
vertex has exactly `d` neighbors, distributed over the target cycles. -/
theorem sum_card_mixedAnchorSupport_eq_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {ℓ : (secondOrderDefectGraph G).ConnectedComponent → ℕ}
    [∀ c, NeZero (ℓ c)]
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod (ℓ c) → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ e, (mixedAnchorSupport G (u c 0) (u e)).card) = d := by
  have hanchor : u c 0 ∈ c.supp := by
    rw [← huRange c]
    exact ⟨0, rfl⟩
  have hcards : ∀ e, (mixedAnchorSupport G (u c 0) (u e)).card =
      componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
    intro e
    exact card_mixedAnchorSupport_eq_componentQuotient G hfree hd heven
      hmin hcard c e hanchor (hu e) (huRange e)
  rw [Finset.sum_congr rfl fun e _ ↦ hcards e]
  exact sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard c

/-! ## The mixed leave and the mixed exact cover

Two more length-agnostic consequences of the even second-order matrix
equation.  Together with the excess identity and the total-mass identity
they form the complete counting substrate of the diagonal-anchor parity
engine, now available for cycles of arbitrary lengths.
-/

/-- **Mixed leave.**  No two neighbors of an anchor vertex are consecutive
on a target cycle: a defect-adjacent pair has zero common neighbors, but
the anchor would be one.  Valid for target cycles of any length. -/
theorem mixedAnchorSupport_no_consecutive
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hvinj : Function.Injective v) (hm3 : 3 ≤ m)
    (hvD : ∀ z, (secondOrderDefectGraph G).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (x : V) (s : ZMod m)
    (hs : s ∈ mixedAnchorSupport G x v) :
    s + 1 ∉ mixedAnchorSupport G x v := by
  intro hs1
  rw [mem_mixedAnchorSupport_iff] at hs hs1
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have hne : v s ≠ v (s + 1) := by
    intro h
    have hss : s = s + 1 := hvinj h
    exact hone (by linear_combination -hss)
  have hmem : v (s + 1) ∈
      (secondOrderDefectGraph G).neighborFinset (v s) := by
    rw [hvD s]
    simp
  have hcommon := card_common_eq_if_secondOrderDefect_of_even
    G hfree hd heven hmin hcard (v s) (v (s + 1)) hne
  rw [if_pos hmem] at hcommon
  have hx : x ∈ G.neighborFinset (v s) ∩
      G.neighborFinset (v (s + 1)) := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hs.symm, hs1.symm⟩
  have hpos : 0 < (G.neighborFinset (v s) ∩
      G.neighborFinset (v (s + 1))).card :=
    Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- **Mixed exact cover.**  A same-cycle pair which is neither equal nor
defect-adjacent has exactly one common anchor, over the whole vertex
set. -/
theorem existsUnique_anchor_of_pair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (s t : ZMod m) (hne : v s ≠ v t)
    (hnadj : ¬ (secondOrderDefectGraph G).Adj (v s) (v t)) :
    ∃! x : V, s ∈ mixedAnchorSupport G x v ∧
      t ∈ mixedAnchorSupport G x v := by
  have hcommon := card_common_eq_if_secondOrderDefect_of_even
    G hfree hd heven hmin hcard (v s) (v t) hne
  rw [if_neg (fun h ↦ hnadj
    (((secondOrderDefectGraph G).mem_neighborFinset _ _).mp h))]
    at hcommon
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcommon
  refine ⟨z, ?_, ?_⟩
  · have hzmem : z ∈ G.neighborFinset (v s) ∩ G.neighborFinset (v t) := by
      rw [hz]
      exact Finset.mem_singleton_self z
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hzmem
    exact ⟨(mem_mixedAnchorSupport_iff G z v s).mpr hzmem.1.symm,
      (mem_mixedAnchorSupport_iff G z v t).mpr hzmem.2.symm⟩
  · intro y hy
    rw [mem_mixedAnchorSupport_iff, mem_mixedAnchorSupport_iff] at hy
    have hymem : y ∈ G.neighborFinset (v s) ∩ G.neighborFinset (v t) := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hy.1.symm, hy.2.symm⟩
    rw [hz, Finset.mem_singleton] at hymem
    exact hymem

/-- Position form of the mixed exact cover: distinct, non-consecutive
cycle positions have exactly one common anchor. -/
theorem existsUnique_anchor_of_position
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hvinj : Function.Injective v)
    (hvD : ∀ z, (secondOrderDefectGraph G).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s t : ZMod m) (h0 : t ≠ s) (h1 : t ≠ s + 1) (h2 : t ≠ s - 1) :
    ∃! x : V, s ∈ mixedAnchorSupport G x v ∧
      t ∈ mixedAnchorSupport G x v := by
  apply existsUnique_anchor_of_pair G hfree hd heven hmin hcard
  · intro h
    exact h0 (hvinj h).symm
  · intro hadj
    rw [← SimpleGraph.mem_neighborFinset, hvD s] at hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hadj
    rcases hadj with h | h
    · exact h2 (hvinj h)
    · exact h1 (hvinj h)

end AnchorSupport

end

end Erdos85
