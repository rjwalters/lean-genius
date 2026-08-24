import Proofs.Erdos85FinalDyadicEmptySecondLayerSupportBound

/-!
# Endpoint partition by exceptional support and empty second-layer branches

When the support bound is saturated, the punctured second-layer branches of
any empty center are exactly the nonexceptional vertices.  C4-freeness makes
the resulting branch coordinate unique.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The union of the punctured neighbor branches rooted at `e`. -/
def emptyCenterPuncturedSecondLayer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : V) : Finset V :=
  (G.neighborFinset e).biUnion fun x => (G.neighborFinset x).erase e

/-- At support size `q`, the punctured second layer of any empty center is
exactly the complement of the exceptional support. -/
theorem finalDyadic_endpoint_emptyCenterPuncturedSecondLayer_eq_support_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e : V} (he : e ∈ emptyLineCenters G S) :
    emptyCenterPuncturedSecondLayer G e =
      (Finset.univ : Finset V) \ exceptionalSignedSupport G S q := by
  let B := G.neighborFinset e
  let U := emptyCenterPuncturedSecondLayer G e
  let C := exceptionalSignedSupport G S q
  have hpair : (↑B : Set V).PairwiseDisjoint
      (fun x => (G.neighborFinset x).erase e) := by
    intro x hx y hy hxy
    change Disjoint ((G.neighborFinset x).erase e)
      ((G.neighborFinset y).erase e)
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hzxData := Finset.mem_erase.mp hzx
    have hzyData := Finset.mem_erase.mp hzy
    have hex : G.Adj e x := (G.mem_neighborFinset e x).mp hx
    have hey : G.Adj e y := (G.mem_neighborFinset e y).mp hy
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzxData.2
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp hzyData.2
    exact hfree (containsC4_of_two_common hxy hzxData.1.symm
      hex hey hxz.symm hyz.symm)
  have hUcard : U.card = q * (q - 1) := by
    change ((G.neighborFinset e).biUnion
      (fun x => (G.neighborFinset x).erase e)).card = _
    rw [Finset.card_biUnion hpair]
    calc
      (∑ x ∈ B, ((G.neighborFinset x).erase e).card) =
          ∑ _x ∈ B, (q - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hex : e ∈ G.neighborFinset x :=
              (G.mem_neighborFinset x e).mpr
                ((G.mem_neighborFinset e x).mp hx).symm
            rw [Finset.card_erase_of_mem hex,
              G.card_neighborFinset_eq_degree, hreg]
      _ = B.card * (q - 1) := by simp
      _ = q * (q - 1) := by
        dsimp only [B]
        rw [G.card_neighborFinset_eq_degree, hreg]
  have hUsub : U ⊆ (Finset.univ : Finset V) \ C := by
    intro z hzU
    change z ∈ (Finset.univ : Finset V) \ C
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ z, ?_⟩
    intro hzC
    change z ∈ emptyCenterPuncturedSecondLayer G e at hzU
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hzU
    have hzxData := Finset.mem_erase.mp hzx
    have hzHalf :=
      finalDyadic_emptyCenter_puncturedSecondLayer_occupancy_eq_half
        G hfree hqa hreg S hdiv hemptyClique he hx hzxData.2 hzxData.1
    have hzSupport : z ∈ fullLineCenters G S q ∪ emptyLineCenters G S := by
      rw [← exceptionalSignedSupport_eq_full_union_empty G S q]
      exact hzC
    rcases Finset.mem_union.mp hzSupport with hzFull | hzEmpty
    · have hzq := (mem_fullLineCenters G S q z).mp hzFull
      rw [hqa] at hzq
      have hpowPos : 0 < 2 ^ j := by positivity
      have hne : 2 ^ j ≠ 2 * 2 ^ j := by omega
      exact hne (hzHalf.symm.trans hzq)
    · have hzzero := (mem_emptyLineCenters G S z).mp hzEmpty
      have hpowPos : 0 < 2 ^ j := by positivity
      exact (Nat.ne_of_gt hpowPos) (hzHalf.symm.trans hzzero)
  have hqpos : 0 < q := by rw [hqa]; positivity
  have hsplit : q * (q - 1) + q = q * q := by
    calc
      q * (q - 1) + q = q * ((q - 1) + 1) := by ring
      _ = q * q := by rw [Nat.sub_add_cancel hqpos]
  have hCcard : C.card = q := hsupport
  have hcomplCard : ((Finset.univ : Finset V) \ C).card = q * (q - 1) := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      hcard, hCcard]
    omega
  change U = (Finset.univ : Finset V) \ C
  exact Finset.eq_of_subset_of_card_le hUsub (by rw [hUcard, hcomplCard])

/-- Equivalently, every nonexceptional vertex has a unique punctured branch
coordinate under an empty center. -/
theorem finalDyadic_endpoint_nonexceptional_existsUnique_emptyBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e z : V} (he : e ∈ emptyLineCenters G S) :
    z ∉ exceptionalSignedSupport G S q ↔
      ∃! x, x ∈ G.neighborFinset e ∧
        z ∈ (G.neighborFinset x).erase e := by
  have hpart :=
    finalDyadic_endpoint_emptyCenterPuncturedSecondLayer_eq_support_compl
      G hfree hqa hreg hcard S hdiv hsupport hemptyClique he
  constructor
  · intro hz
    have hzU : z ∈ emptyCenterPuncturedSecondLayer G e := by
      rw [hpart]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hzU
    refine ⟨x, ⟨hx, hzx⟩, ?_⟩
    intro y hy
    by_contra hxy
    have hxy' : x ≠ y := fun h => hxy h.symm
    have hzxData := Finset.mem_erase.mp hzx
    have hzyData := Finset.mem_erase.mp hy.2
    have hex : G.Adj e x := (G.mem_neighborFinset e x).mp hx
    have hey : G.Adj e y := (G.mem_neighborFinset e y).mp hy.1
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzxData.2
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp hzyData.2
    exact hfree (containsC4_of_two_common hxy' hzxData.1.symm
      hex hey hxz.symm hyz.symm)
  · rintro ⟨x, hx, _⟩ hzSupport
    have hzU : z ∈ emptyCenterPuncturedSecondLayer G e :=
      Finset.mem_biUnion.mpr ⟨x, hx.1, hx.2⟩
    rw [hpart] at hzU
    exact (Finset.mem_sdiff.mp hzU).2 hzSupport

end


end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_emptyCenterPuncturedSecondLayer_eq_support_compl
#print axioms
  Erdos85.finalDyadic_endpoint_nonexceptional_existsUnique_emptyBranch
