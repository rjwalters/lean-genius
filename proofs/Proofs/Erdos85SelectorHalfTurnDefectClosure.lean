import Proofs.Erdos85C4FreeCommonNeighborUnique

/-!
# A free involution and selector budgets force a defect split

This is the generic checked core of the fixed-carrier half-turn audit at
A.5.3. The involution symmetry, selector disjointness, parity-row budgets,
and defect/common-neighbor dictionary are explicit hypotheses. No theorem
here asserts those hypotheses for arbitrary size-two carriers.
-/

open SimpleGraph

namespace Erdos85

theorem c4Free_fixedFree_involution_no_commonNeighbor
    {V : Type*} (T : SimpleGraph V) (hfree : ¬ containsC4 V T)
    (mate : V → V) (hinvol : Function.Involutive mate)
    (hfixed : ∀ v, mate v ≠ v)
    (hmap : ∀ {v w}, T.Adj v w → T.Adj (mate v) (mate w)) (e : V) :
    ¬ ∃ w, T.Adj e w ∧ T.Adj (mate e) w := by
  rintro ⟨w, hew, hmew⟩
  have he_mw : T.Adj e (mate w) := by
    simpa only [hinvol e] using hmap hmew
  have hm_mw : T.Adj (mate e) (mate w) := hmap hew
  have hw := commonNeighbor_unique_of_c4Free hfree (hfixed e).symm
    hew hmew he_mw hm_mw
  exact hfixed w hw.symm

/-- Exact selector-row budgets rule out every defect edge crossing Z when
the exterior graph has a free involutive symmetry. -/
theorem selector_budget_halfTurn_no_defect_boundary
    {C F : Type*} [DecidableEq C] [Fintype F] [DecidableEq F]
    (T D : SimpleGraph F) [DecidableRel D.Adj]
    (B : C → Finset F) (P : F → Finset C) (Z : Set F)
    (mate : F → F) (hinvol : Function.Involutive mate)
    (hfixed : ∀ e, mate e ≠ e)
    (hmap : ∀ {e f}, T.Adj e f → T.Adj (mate e) (mate f))
    (hfree : ¬ containsC4 F T)
    (hdisjoint : ∀ e x, ¬ (e ∈ B x ∧ mate e ∈ B x))
    (hdefect : ∀ e f, D.Adj e f ↔ e ≠ f ∧
      (∀ x, ¬ (e ∈ B x ∧ f ∈ B x)) ∧
      ¬ ∃ w, T.Adj e w ∧ T.Adj f w)
    (hpreserve : ∀ e, e ∉ Z → mate e ∉ Z)
    (hbudget : ∀ e, e ∉ Z → ∀ x ∈ P e,
      (D.neighborFinset e ∩ B x).card = if mate e ∈ B x then 1 else 0)
    (hcross : ∀ e, e ∉ Z → ∀ z, z ∈ Z → ∃ x ∈ P e, z ∈ B x) :
    ∀ e, e ∉ Z → ∀ z, z ∈ Z → ¬ D.Adj e z := by
  intro e he z hz hez
  have hmate : D.Adj e (mate e) := (hdefect e (mate e)).mpr
    ⟨(hfixed e).symm, hdisjoint e,
      c4Free_fixedFree_involution_no_commonNeighbor T hfree mate hinvol hfixed hmap e⟩
  obtain ⟨x, hx, hzx⟩ := hcross e he z hz
  have hzmem : z ∈ D.neighborFinset e ∩ B x := by
    exact Finset.mem_inter.mpr ⟨by simpa using hez, hzx⟩
  have hmatex : mate e ∈ B x := by
    by_contra hnot
    have hzero : (D.neighborFinset e ∩ B x).card = 0 := by
      simpa only [if_neg hnot] using hbudget e he x hx
    have hpos := Finset.card_pos.mpr ⟨z, hzmem⟩
    omega
  have hm_mem : mate e ∈ D.neighborFinset e ∩ B x := by
    exact Finset.mem_inter.mpr ⟨by simpa using hmate, hmatex⟩
  have hcard : (D.neighborFinset e ∩ B x).card ≤ 1 := by
    rw [hbudget e he x hx, if_pos hmatex]
  have heq : z = mate e := Finset.card_le_one_iff.mp hcard hzmem hm_mem
  exact hpreserve e he (heq ▸ hz)

/-- A nonempty proper Z with the same explicit selector budgets contradicts
connectedness of the defect graph. -/
theorem selector_budget_halfTurn_defect_not_connected
    {C F : Type*} [DecidableEq C] [Fintype F] [DecidableEq F]
    (T D : SimpleGraph F) [DecidableRel D.Adj]
    (B : C → Finset F) (P : F → Finset C) (Z : Set F)
    (mate : F → F) (hinvol : Function.Involutive mate)
    (hfixed : ∀ e, mate e ≠ e)
    (hmap : ∀ {e f}, T.Adj e f → T.Adj (mate e) (mate f))
    (hfree : ¬ containsC4 F T)
    (hdisjoint : ∀ e x, ¬ (e ∈ B x ∧ mate e ∈ B x))
    (hdefect : ∀ e f, D.Adj e f ↔ e ≠ f ∧
      (∀ x, ¬ (e ∈ B x ∧ f ∈ B x)) ∧
      ¬ ∃ w, T.Adj e w ∧ T.Adj f w)
    (hpreserve : ∀ e, e ∉ Z → mate e ∉ Z)
    (hbudget : ∀ e, e ∉ Z → ∀ x ∈ P e,
      (D.neighborFinset e ∩ B x).card = if mate e ∈ B x then 1 else 0)
    (hcross : ∀ e, e ∉ Z → ∀ z, z ∈ Z → ∃ x ∈ P e, z ∈ B x)
    (hZ : Z.Nonempty) (houtside : ∃ e, e ∉ Z) : ¬ D.Connected := by
  have hboundary := selector_budget_halfTurn_no_defect_boundary T D B P Z
    mate hinvol hfixed hmap hfree hdisjoint hdefect hpreserve hbudget hcross
  have hwalk : ∀ {a b}, Relation.ReflTransGen D.Adj a b → a ∉ Z → b ∉ Z := by
    intro a b hab
    induction hab with
    | refl => exact id
    | tail _ hbc ih =>
      intro ha hb
      exact hboundary _ (ih ha) _ hb hbc
  intro hconn
  obtain ⟨e, he⟩ := houtside
  obtain ⟨z, hz⟩ := hZ
  exact hwalk ((D.reachable_iff_reflTransGen e z).mp (hconn.preconnected e z)) he hz

#print axioms c4Free_fixedFree_involution_no_commonNeighbor
#print axioms selector_budget_halfTurn_no_defect_boundary
#print axioms selector_budget_halfTurn_defect_not_connected

end Erdos85
