import Proofs.Erdos85BinarySquareMuThreeExteriorGrid
import Proofs.Erdos85CrossEdgeTriangleDichotomy
import Proofs.Erdos85BinarySquareSizeTwoJointEigenvectorMuOneExclusion

/-! # Row-pair balance at a normalized size-two component

Summing the row-hit law over one exterior row and double-counting the exterior
edges between two rows gives a symmetric internal-obstruction count.  In grid
coordinates this is the graph-facing form of
`|N_H(x') ∩ K(x)| = |N_H(x) ∩ K(x')|`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- Component vertices which form an exterior-selected pair with `x`.
Equivalently, these are the neighbours of `x` in `exteriorPairGraph G c.supp`,
kept as ambient vertices for convenient finite-set counting. -/
noncomputable def sizeTwoExteriorPartnerFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (x : c.supp) : Finset V :=
  Finset.univ.filter fun y =>
    y ∈ c.supp ∧ y ≠ x.1 ∧
      ∃ u : V, u ∉ c.supp ∧ G.Adj x.1 u ∧ G.Adj y u

/-- **Row-pair balance.**  For two vertices `x,x'` of a normalized size-two
defect component, sum over the exterior neighbours of `x` the number of
internal neighbours of `x'` also adjacent to that exterior vertex.  This is
symmetric in `x,x'`. -/
theorem binarySquare_regular_sizeTwoComponent_rowPair_internalHit_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q)
    (hcardV : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x x' : c.supp) :
    let R : c.supp → Finset V := fun z =>
      (G.neighborFinset z.1).filter
        (fun u => (secondOrderDefectGraph G).connectedComponentMk u ≠ c)
    (∑ u ∈ R x,
      ((G.neighborFinset x'.1).filter
        (fun y => y ∈ c.supp ∧ G.Adj u y)).card) =
    ∑ u ∈ R x',
      ((G.neighborFinset x.1).filter
        (fun y => y ∈ c.supp ∧ G.Adj u y)).card := by
  classical
  let R : c.supp → Finset V := fun z =>
    (G.neighborFinset z.1).filter
      (fun u => (secondOrderDefectGraph G).connectedComponentMk u ≠ c)
  let I : c.supp → V → ℕ := fun z u =>
    ((G.neighborFinset z.1).filter
      (fun y => y ∈ c.supp ∧ G.Adj u y)).card
  let E : c.supp → V → ℕ := fun z u =>
    ((G.neighborFinset u).filter
      (fun y => y ∉ c.supp ∧ G.Adj z.1 y)).card
  have hRcard : ∀ z : c.supp, (R z).card = q - 2 := by
    intro z
    exact binarySquare_regular_sizeTwoComponent_exteriorNeighborCard
      G hfree hq hreg hcardV c hc z
  have hrow : ∀ z : c.supp, ∀ u ∈ R x,
      I z u + E z u = 1 := by
    intro z u hu
    have huout : u ∉ c.supp := by
      intro huc
      have heq := (ConnectedComponent.mem_supp_iff c u).mp huc
      exact (Finset.mem_filter.mp hu).2 heq
    exact card_internal_common_add_card_exterior_common_eq_one
      G hfree c z.2 huout
  have hrow' : ∀ z : c.supp, ∀ u ∈ R x',
      I z u + E z u = 1 := by
    intro z u hu
    have huout : u ∉ c.supp := by
      intro huc
      have heq := (ConnectedComponent.mem_supp_iff c u).mp huc
      exact (Finset.mem_filter.mp hu).2 heq
    exact card_internal_common_add_card_exterior_common_eq_one
      G hfree c z.2 huout
  have hE_as_row : ∀ z : c.supp, ∀ u : V,
      E z u = ((G.neighborFinset u).filter (fun y => y ∈ R z)).card := by
    intro z u
    apply congrArg Finset.card
    ext y
    simp only [R, Finset.mem_filter, mem_neighborFinset]
    rw [ConnectedComponent.mem_supp_iff]
    tauto
  have hedgeZ := sum_sum_filter_neighborFinset_comm
    G (R x) (R x') (fun _ _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hedgeZ
  have hedge : (∑ u ∈ R x, E x' u) = ∑ u ∈ R x', E x u := by
    simp_rw [hE_as_row]
    exact_mod_cast hedgeZ
  have hsumRow : (∑ u ∈ R x, I x' u) + (∑ u ∈ R x, E x' u) = (R x).card := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ u ∈ R x, (I x' u + E x' u) = ∑ _u ∈ R x, 1 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hrow x' u hu
      _ = (R x).card := by simp
  have hsumRow' : (∑ u ∈ R x', I x u) + (∑ u ∈ R x', E x u) = (R x').card := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ u ∈ R x', (I x u + E x u) = ∑ _u ∈ R x', 1 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hrow' x u hu
      _ = (R x').card := by simp
  change (∑ u ∈ R x, I x' u) = ∑ u ∈ R x', I x u
  rw [hRcard x] at hsumRow
  rw [hRcard x'] at hsumRow'
  omega

/-- For nonadjacent component vertices, the internal-hit sum along the
exterior row of `x` is exactly the number of exterior partners of `x` which
are internal neighbours of `x'`. -/
theorem binarySquare_regular_sizeTwoComponent_internalHit_sum_eq_partner_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (x x' : c.supp) (hxx' : ¬(G.induce c.supp).Adj x x') :
    let R := (G.neighborFinset x.1).filter
      (fun u => (secondOrderDefectGraph G).connectedComponentMk u ≠ c)
    (∑ u ∈ R,
      ((G.neighborFinset x'.1).filter
        (fun y => y ∈ c.supp ∧ G.Adj u y)).card) =
      ((sizeTwoExteriorPartnerFinset G c x).filter
        fun y => G.Adj x'.1 y).card := by
  classical
  let R := (G.neighborFinset x.1).filter
    (fun u => (secondOrderDefectGraph G).connectedComponentMk u ≠ c)
  let B := (G.neighborFinset x'.1).filter fun y => y ∈ c.supp
  let K := sizeTwoExteriorPartnerFinset G c x
  change (∑ u ∈ R,
      ((G.neighborFinset x'.1).filter
        (fun y => y ∈ c.supp ∧ G.Adj u y)).card) =
    (K.filter fun y => G.Adj x'.1 y).card
  have hdcZ := sum_sum_filter_neighborFinset_comm
    G R B (fun _ _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hdcZ
  have hdc :
      (∑ u ∈ R, ((G.neighborFinset u).filter fun y => y ∈ B).card) =
        ∑ y ∈ B, ((G.neighborFinset y).filter fun u => u ∈ R).card := by
    exact_mod_cast hdcZ
  have hleft :
      (∑ u ∈ R,
        ((G.neighborFinset x'.1).filter
          (fun y => y ∈ c.supp ∧ G.Adj u y)).card) =
      ∑ u ∈ R, ((G.neighborFinset u).filter fun y => y ∈ B).card := by
    apply Finset.sum_congr rfl
    intro u _hu
    congr 1
    ext y
    simp only [B, Finset.mem_filter, mem_neighborFinset]
    tauto
  have hterm : ∀ y ∈ B,
      ((G.neighborFinset y).filter fun u => u ∈ R).card =
        if y ∈ K then 1 else 0 := by
    intro y hyB
    have hyc : y ∈ c.supp := (Finset.mem_filter.mp hyB).2
    have hxy : x.1 ≠ y := by
      intro h
      subst y
      apply hxx'
      exact ((G.mem_neighborFinset x'.1 x.1).mp
        (Finset.mem_filter.mp hyB).1).symm
    let U := (G.neighborFinset y).filter fun u => u ∈ R
    have hUle : U.card ≤ 1 := by
      apply le_trans (Finset.card_le_card ?_)
        (common_le_one_of_not_containsC4 hfree x.1 y hxy)
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have huR := Finset.mem_filter.mp hu'.2
      simp only [Finset.mem_inter, mem_neighborFinset]
      exact ⟨(G.mem_neighborFinset x.1 u).mp huR.1,
        (G.mem_neighborFinset y u).mp hu'.1⟩
    by_cases hyK : y ∈ K
    · have hpos : 0 < U.card := by
        rw [Finset.card_pos]
        have hyData : y ∈ c.supp ∧ y ≠ x.1 ∧
            ∃ u : V, u ∉ c.supp ∧ G.Adj x.1 u ∧ G.Adj y u := by
          simpa [K, sizeTwoExteriorPartnerFinset] using hyK
        obtain ⟨u, huout, hxu, hyu⟩ := hyData.2.2
        refine ⟨u, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset y u).mpr hyu, ?_⟩⟩
        apply Finset.mem_filter.mpr
        refine ⟨(G.mem_neighborFinset x.1 u).mpr hxu, ?_⟩
        intro heq
        exact huout ((ConnectedComponent.mem_supp_iff c u).mpr heq)
      have hUeq : U.card = 1 := by omega
      simp only [if_pos hyK]
      change U.card = 1
      exact hUeq
    · have hzero : U.card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        apply hyK
        have hu' := Finset.mem_filter.mp hu
        have huR := Finset.mem_filter.mp hu'.2
        have huout : u ∉ c.supp := by
          intro huc
          exact huR.2 ((ConnectedComponent.mem_supp_iff c u).mp huc)
        have hxu : G.Adj x.1 u := (G.mem_neighborFinset x.1 u).mp huR.1
        have hyu : G.Adj y u := (G.mem_neighborFinset y u).mp hu'.1
        simpa [K, sizeTwoExteriorPartnerFinset] using
          (show y ∈ c.supp ∧ y ≠ x.1 ∧
              ∃ u : V, u ∉ c.supp ∧ G.Adj x.1 u ∧ G.Adj y u from
            ⟨hyc, hxy.symm, u, huout, hxu, hyu⟩)
      simp only [if_neg hyK]
      change U.card = 0
      exact hzero
  rw [hleft, hdc]
  calc
    (∑ y ∈ B, ((G.neighborFinset y).filter fun u => u ∈ R).card) =
        ∑ y ∈ B, if y ∈ K then 1 else 0 := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (B ∩ K).card := by simp
    _ = (K.filter fun y => G.Adj x'.1 y).card := by
      congr 1
      ext y
      simp [B, K, sizeTwoExteriorPartnerFinset, and_comm, and_left_comm,
        and_assoc]

/-- Explicit exterior-pair-factor form of the row-pair balance.  This is the
uniform identity `|N_H(x') ∩ K(x)| = |N_H(x) ∩ K(x')|`. -/
theorem binarySquare_regular_sizeTwoComponent_exteriorPartner_inter_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q)
    (hcardV : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x x' : c.supp)
    (hxx' : ¬(G.induce c.supp).Adj x x') :
    ((sizeTwoExteriorPartnerFinset G c x).filter
      fun y => G.Adj x'.1 y).card =
    ((sizeTwoExteriorPartnerFinset G c x').filter
      fun y => G.Adj x.1 y).card := by
  rw [← binarySquare_regular_sizeTwoComponent_internalHit_sum_eq_partner_inter
      G hfree c x x' hxx',
    ← binarySquare_regular_sizeTwoComponent_internalHit_sum_eq_partner_inter
      G hfree c x' x (fun h => hxx' h.symm)]
  exact binarySquare_regular_sizeTwoComponent_rowPair_internalHit_balance
    G hfree hq hreg hcardV c hc x x'

end


end Erdos85

#print axioms
  Erdos85.binarySquare_regular_sizeTwoComponent_rowPair_internalHit_balance
#print axioms Erdos85.sizeTwoExteriorPartnerFinset
#print axioms
  Erdos85.binarySquare_regular_sizeTwoComponent_internalHit_sum_eq_partner_inter
#print axioms
  Erdos85.binarySquare_regular_sizeTwoComponent_exteriorPartner_inter_balance
