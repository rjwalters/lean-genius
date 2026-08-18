import Proofs.Erdos85BinarySquareSignedEigenvectorSupport

/-!
# The `μ = 3` signed size-two line collapses to a global adjacency eigenvector

At order `64`, the outside-support energy identity has right-hand side zero
when the defect eigenvalue is `3`.  Consequently the adjacency image has no
outside support at all: a signed internal `-2` vector is already a global
ambient `-2` eigenvector.  This is the structural entrance to the exterior
routing problem for the remaining `μ = 3` branch.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A two-element signed fibre with zero signed sum contains one sign of each
kind.  Kept separate from the graph wrapper so later routing arguments can
reuse the exact finite-set conclusion. -/
theorem signedPair_zeroSum_filter_cards
    {V : Type*} [DecidableEq V] (T : Finset V) (s : V → ℤ)
    (hcard : T.card = 2) (hsign : ∀ x ∈ T, s x = -1 ∨ s x = 1)
    (hsum : ∑ x ∈ T, s x = 0) :
    (T.filter fun x => s x = 1).card = 1 ∧
      (T.filter fun x => s x = -1).card = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha := hsign a (by simp)
  have hb := hsign b (by simp)
  have hanot : a ∉ ({b} : Finset V) := by simp [hab]
  rw [Finset.sum_insert hanot, Finset.sum_singleton] at hsum
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · rw [ha, hb] at hsum
      omega
    · have hp : (({a, b} : Finset V).filter fun x => s x = 1) = {b} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxab, hsx⟩
          rcases hxab with rfl | rfl
          · omega
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, hb⟩
      have hn : (({a, b} : Finset V).filter fun x => s x = -1) = {a} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxab, hsx⟩
          rcases hxab with rfl | rfl
          · rfl
          · omega
        · rintro rfl
          exact ⟨Or.inl rfl, ha⟩
      rw [hp, hn]
      simp
  · rcases hb with hb | hb
    · have hp : (({a, b} : Finset V).filter fun x => s x = 1) = {a} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxab, hsx⟩
          rcases hxab with rfl | rfl
          · rfl
          · omega
        · rintro rfl
          exact ⟨Or.inl rfl, ha⟩
      have hn : (({a, b} : Finset V).filter fun x => s x = -1) = {b} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxab, hsx⟩
          rcases hxab with rfl | rfl
          · omega
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, hb⟩
      rw [hp, hn]
      simp
    · rw [ha, hb] at hsum
      omega

/-- At `q = 8` and `μ = 3`, the adjacency image of a signed size-two defect
eigenvector vanishes outside its component and hence equals `-2s` globally. -/
theorem orderSixtyFour_signedSizeTwo_muThree_adjEigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2) :
    (G.adjMatrix ℤ).mulVec s = (-2 : ℤ) • s := by
  have hsupp := binarySquare_regular_signedEigenvector_outsideSupport
    G hfree hreg c hc s 3 hs_in hs_out hsum hDs hA_in hA_out
  have hcard : (Finset.univ.filter fun x =>
      x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x ≠ 0).card = 0 := by
    have hsupp' : 2 * ((Finset.univ.filter fun x =>
        x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x ≠ 0).card : ℤ) = 0 := by
      convert hsupp using 1
      all_goals norm_num
    have hcast : ((Finset.univ.filter fun x =>
        x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x ≠ 0).card : ℤ) = 0 := by
      omega
    exact_mod_cast hcast
  have hempty : (Finset.univ.filter fun x =>
      x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x ≠ 0) = ∅ :=
    Finset.card_eq_zero.mp hcard
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ c.supp
  · exact hA_in x hx
  · rw [hs_out x hx, mul_zero]
    by_contra hne
    have hmem : x ∈ (Finset.univ.filter fun x =>
        x ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s x ≠ 0) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hne⟩
    rw [hempty] at hmem
    simp at hmem

/-- In the `μ = 3` branch, every exterior vertex sees exactly one positive and
one negative vertex of the size-two component.  Thus the exterior vertices
are canonically labelled by balanced sign pairs, the incidence structure used
by the exterior-routing obstruction. -/
theorem orderSixtyFour_signedSizeTwo_muThree_exterior_balancedPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (x : V) (hx : x ∉ c.supp) :
    let T := (G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
    (T.filter fun y => s y = 1).card = 1 ∧
      (T.filter fun y => s y = -1).card = 1 := by
  let T := (G.neighborFinset x).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
  have hTcard : T.card = 2 := by
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg hcardV
      ((secondOrderDefectGraph G).connectedComponentMk x) c
      (x := x) ((ConnectedComponent.mem_supp_iff _ x).mpr rfl)
    rw [hc] at h
    change 8 * T.card = 8 * 2 at h
    omega
  have hTsign : ∀ y ∈ T, s y = -1 ∨ s y = 1 := by
    intro y hy
    have hyc : (secondOrderDefectGraph G).connectedComponentMk y = c :=
      (Finset.mem_filter.mp hy).2
    exact hs_in y ((ConnectedComponent.mem_supp_iff c y).mpr hyc)
  have hglobal := orderSixtyFour_signedSizeTwo_muThree_adjEigenvector
    G hfree hreg c hc s hs_in hs_out hsum hDs hA_in hA_out
  have hxsum : ∑ y ∈ G.neighborFinset x, s y = 0 := by
    have heq := congrFun hglobal x
    rw [SimpleGraph.adjMatrix_mulVec_apply] at heq
    simp [Pi.smul_apply, hs_out x hx] at heq
    exact heq
  have hTsum : ∑ y ∈ T, s y = 0 := by
    calc
      ∑ y ∈ T, s y = ∑ y ∈ G.neighborFinset x, s y := by
        change (∑ y ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hyc : (secondOrderDefectGraph G).connectedComponentMk y = c
        · simp [hyc]
        · have hyn : y ∉ c.supp := by
            rw [ConnectedComponent.mem_supp_iff]
            exact hyc
          simp [hyc, hs_out y hyn]
      _ = 0 := hxsum
  exact signedPair_zeroSum_filter_cards T s hTcard hTsign hTsum

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_signedSizeTwo_muThree_adjEigenvector
#print axioms Erdos85.signedPair_zeroSum_filter_cards
#print axioms Erdos85.orderSixtyFour_signedSizeTwo_muThree_exterior_balancedPair
