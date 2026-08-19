import Proofs.Erdos85SizeTwoMuNegThreeSixTenCrossColumnTypes
import Proofs.Erdos85BipartiteRegularSignedEigenvector

/-! # Exclusion of the `mu=-3` six-plus-ten stratum -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- For a `±1`-valued family, twice the base-sign fiber size is its total
cardinality plus the base sign times its signed sum. -/
theorem signed_same_card_equation
    {X : Type*} [DecidableEq X] (T : Finset X) (s : X → ℤ)
    (base : ℤ)
    (hsign : ∀ x ∈ T, s x = -1 ∨ s x = 1)
    (hbase : base = -1 ∨ base = 1) :
    (2 : ℤ) * ((T.filter fun x ↦ s x = base).card : ℤ) =
      (T.card : ℤ) + base * ∑ x ∈ T, s x := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert x T hx ih =>
      have hsx := hsign x (by simp)
      have hsT : ∀ y ∈ T, s y = -1 ∨ s y = 1 := by
        intro y hy
        exact hsign y (by simp [hy])
      have hi := ih hsT
      rcases hbase with hbase | hbase <;> subst base <;>
        rcases hsx with hsx | hsx <;>
        simp only [Finset.filter_insert, Finset.sum_insert hx] <;>
        simp [hx, hsx] at hi ⊢ <;> omega

/-- On four signed points, an eigenvalue equation determines the number of
entries having the base sign. -/
theorem signedFour_same_card_equation
    {X : Type*} [DecidableEq X] (T : Finset X) (s : X → ℤ)
    (base mu : ℤ) (hcard : T.card = 4)
    (hsign : ∀ x ∈ T, s x = -1 ∨ s x = 1)
    (hbase : base = -1 ∨ base = 1)
    (hsum : ∑ x ∈ T, s x = mu * base) :
    (2 : ℤ) * ((T.filter fun x ↦ s x = base).card : ℤ) = 4 + mu := by
  have h := signed_same_card_equation T s base hsign hbase
  calc
    _ = (T.card : ℤ) + base * ∑ x ∈ T, s x := h
    _ = 4 + mu := by
      rw [hcard, hsum]
      rcases hbase with hbase | hbase <;> rw [hbase] <;> ring

set_option maxHeartbeats 1200000 in
/-- The `mu=-3` signed eigenline cannot have two internal cycles of lengths
six and ten. The commuting long diagonal block preserves the alternating line,
forcing a constant signed column type, while the cross census totals twelve
same-sign incidences over ten columns. -/
theorem orderSixtyFour_sizeTwo_muNegThree_sixTen_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) : False := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let Hb := H.induce b.supp
  let Kb := K.induce b.supp
  let v : b.supp → ℤ := fun x ↦ s x.1.1
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hHbdegree : ∀ z : b.supp, Hb.degree z = 2 := by
    intro z
    rw [degree_induce_connectedComponent_supp]
    exact hHdegree z.1
  have hvsign : ∀ z, v z = -1 ∨ v z = 1 := by
    intro z
    exact hs_in z.1.1 z.1.2
  have hvH : ∀ z, ∑ w ∈ Hb.neighborFinset z, v w = -2 * v z := by
    intro z
    calc
      ∑ w ∈ Hb.neighborFinset z, v w =
          ∑ _w ∈ Hb.neighborFinset z, -v z := by
        apply Finset.sum_congr rfl
        intro w hw
        have hHw : H.Adj z.1 w.1 :=
          (Hb.mem_neighborFinset z w).mp hw
        have hwmem : w.1.1 ∈ componentNeighborFinset G
            (secondOrderDefectGraph G) c z.1.1 := by
          rw [componentNeighborFinset, Finset.mem_filter]
          exact ⟨(G.mem_neighborFinset _ _).mpr hHw, w.1.2⟩
        exact internal_alternation G hfree (by omega) hreg hcard c hc s
          hs_in hs_out hAfull z.1.2 |>.2 w.1.1 hwmem
      _ = -2 * v z := by
        rw [Finset.sum_const, nsmul_eq_mul, Hb.card_neighborFinset_eq_degree,
          hHbdegree]
        ring
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    exact (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  have hcommb : Kb.adjMatrix ℤ * Hb.adjMatrix ℤ =
      Hb.adjMatrix ℤ * Kb.adjMatrix ℤ := by
    exact induce_component_adjMatrix_comm_of_comm K H hcomm b
  obtain ⟨mu, hmu⟩ := commutingGraph_exists_eigenvalue_on_signed_negativeDegree_line
    Hb Kb b.connected_toSimpleGraph 2 hHbdegree v hvsign hvH hcommb
  have hquot := binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
    G hfree hreg hcard c hc s hs_in hs_out hAfull a b ha hb
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  let g : b.supp → ℕ := fun y ↦
    ((Kb.neighborFinset y).filter fun x ↦ v x = v y).card
  have hKbcard : ∀ y : b.supp, (Kb.neighborFinset y).card = 4 := by
    intro y
    let I := componentNeighborFinset K H b y.1
    have hIcard : I.card = 4 := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal b b y.2]
      exact hquot.2.2.2
    have heq : (Kb.neighborFinset y).image (fun z ↦ z.1) = I := by
      ext x
      simp [I, Kb, H, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        eq_comm]
    rw [← hIcard, ← heq, Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hgeq : ∀ y, (2 : ℤ) * (g y : ℤ) = 4 + mu := by
    intro y
    apply signedFour_same_card_equation (Kb.neighborFinset y) v (v y) mu
    · exact hKbcard y
    · intro x hx
      exact hvsign x
    · exact hvsign y
    · have hmuy := congrFun hmu y
      rw [SimpleGraph.adjMatrix_mulVec_apply] at hmuy
      simpa [v, Pi.smul_apply, smul_eq_mul] using hmuy
  have gconst : ∀ y z, g y = g z := by
    intro y z
    have hy := hgeq y
    have hz := hgeq z
    omega
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let L := (Finset.univ : Finset c.supp).filter fun y ↦ y ∉ a.supp
  let f := fun y : c.supp ↦ (A.filter fun x ↦
    K.Adj y x ∧ s y.1 = s x.1).card
  have hcomp := sixTen_internalComponent_complement G c
    (by simpa using hc) a b ha hb
  have hprofile := orderSixtyFour_sizeTwo_muNegThree_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hKsame : ∀ y : c.supp,
      ((K.neighborFinset y).filter fun x ↦ s x.1 = s y.1).card = 2 := by
    intro y
    let D := secondOrderDefectGraph G
    have himage (t : ℤ) : Finset.image Subtype.val
        ((K.neighborFinset y).filter fun x ↦ s x.1 = t) =
        (D.neighborFinset y.1).filter fun x ↦ s x = t := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨z, ⟨hK, hsz⟩, rfl⟩
        exact ⟨hK, hsz⟩
      · rintro ⟨hDx, hsx⟩
        have hxc : x ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c x]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hDx).symm.trans
            ((ConnectedComponent.mem_supp_iff c y.1).mp y.2)
        exact ⟨⟨x, hxc⟩, ⟨hDx, hsx⟩, rfl⟩
    rcases hs_in y.1 y.2 with hsy | hsy
    · have hp := (hprofile.2.2 y.1 y.2).2 hsy
      calc
        _ = ((D.neighborFinset y.1).filter fun x ↦ s x = -1).card := by
          rw [← congrArg Finset.card (himage (-1)),
            Finset.card_image_of_injective _ Subtype.val_injective]
          simp [hsy]
        _ = 2 := hp.2.2.1
    · have hp := (hprofile.2.2 y.1 y.2).1 hsy
      calc
        _ = ((D.neighborFinset y.1).filter fun x ↦ s x = 1).card := by
          rw [← congrArg Finset.card (himage 1),
            Finset.card_image_of_injective _ Subtype.val_injective]
          simp [hsy]
        _ = 2 := hp.2.2.1
  have hfg : ∀ (y : c.supp) (hy : y ∈ L),
      f y + g ⟨y, (hcomp y).mp (Finset.mem_filter.mp hy).2⟩ = 2 := by
    intro y hy
    let yb : b.supp := ⟨y, (hcomp y).mp (Finset.mem_filter.mp hy).2⟩
    let CA := A.filter fun x ↦ K.Adj y x ∧ s y.1 = s x.1
    let IB := ((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp).filter
      fun x ↦ K.Adj y x ∧ s y.1 = s x.1
    have hgIB : IB.card = g yb := by
      change IB.card = ((Kb.neighborFinset yb).filter fun z ↦ v z = v yb).card
      apply Finset.card_bij (fun x hx ↦
        ⟨x, (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2⟩)
      · intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hK := hx'.2.1
        have hs := hx'.2.2
        rw [Finset.mem_filter]
        constructor
        · rw [Kb.mem_neighborFinset]
          change K.Adj y x
          exact hK
        · exact hs.symm
      · intro x₁ hx₁ x₂ hx₂ heq
        exact Subtype.ext_iff.mp heq
      · intro z hz
        refine ⟨z.1, ?_, Subtype.ext rfl⟩
        have hz' := Finset.mem_filter.mp hz
        have hKz := (Kb.mem_neighborFinset _ _).mp hz'.1
        change K.Adj y z.1 at hKz
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩,
          hKz, hz'.2.symm⟩
    have hunion : CA ∪ IB =
        (K.neighborFinset y).filter fun x ↦ s x.1 = s y.1 := by
      ext x
      simp only [CA, IB, A, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro (⟨hxa, hK, hs⟩ | ⟨hxb, hK, hs⟩) <;>
          exact ⟨hK, hs.symm⟩
      · intro hx
        rcases hx with ⟨hK, hs⟩
        by_cases hxa : x ∈ a.supp
        · left
          exact ⟨hxa, hK, hs.symm⟩
        · right
          have hxb := (hcomp x).mp hxa
          exact ⟨hxb, hK, hs.symm⟩
    have hdisj : Disjoint CA IB := by
      dsimp only [CA, IB, A]
      rw [Finset.disjoint_left]
      intro x hxA hxB
      have hxa := (Finset.mem_filter.mp (Finset.mem_filter.mp hxA).1).2
      have hxb := (Finset.mem_filter.mp (Finset.mem_filter.mp hxB).1).2
      exact ((hcomp x).mpr hxb) hxa
    have hcards : CA.card + IB.card = 2 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, hKsame]
    change CA.card + g yb = 2
    rw [← hgIB]
    exact hcards
  have fconst : ∀ y ∈ L, ∀ z ∈ L, f y = f z := by
    intro y hy z hz
    have hyfg := hfg y hy
    have hzfg := hfg z hz
    have hg := gconst
      ⟨y, (hcomp y).mp (Finset.mem_filter.mp hy).2⟩
      ⟨z, (hcomp z).mp (Finset.mem_filter.mp hz).2⟩
    omega
  have hcensus := orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_census
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b ha hb
  have hsum : (∑ y ∈ L, f y) = 12 := by
    rw [← hcensus.1]
    simp only [Finset.card_sigma]
    rfl
  have hLcard : L.card = 10 := by
    let B := (Finset.univ : Finset c.supp).filter fun y ↦ y ∈ b.supp
    have hLB : L = B := by
      ext y
      simp only [L, B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcomp y
    rw [hLB]
    have heq : B = b.supp.toFinite.toFinset := by
      ext y
      simp [B]
    rw [heq, ← Set.ncard_eq_toFinset_card, hb]
  have hLnonempty : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y₀, hy₀⟩ := hLnonempty
  have hsumConst : (∑ y ∈ L, f y) = L.card * f y₀ := by
    calc
      _ = ∑ _y ∈ L, f y₀ := by
        apply Finset.sum_congr rfl
        intro y hy
        exact fconst y hy y₀ hy₀
      _ = L.card * f y₀ := by simp
  rw [hsum, hLcard] at hsumConst
  omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sixTen_false
