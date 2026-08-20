import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCenters

/-! # A paired antipodal center inside every selected triple -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem three_of_four_contains_opposite_pair
    {α : Type*} [DecidableEq α]
    (a0 a1 a2 a3 : α)
    (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h03 : a0 ≠ a3)
    (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3)
    (S : Finset α) (hsub : S ⊆ {a0, a1, a2, a3})
    (hcard : S.card = 3) :
    (a0 ∈ S ∧ a2 ∈ S) ∨ (a1 ∈ S ∧ a3 ∈ S) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h02, h13'⟩
  by_cases h0 : a0 ∈ S <;> by_cases h1 : a1 ∈ S
  · have h2 := h02 h0
    have h3 := h13' h1
    have hs : S ⊆ {a0, a1} := by
      intro x hx
      have hxall := hsub hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxall
      rcases hxall with rfl | rfl | rfl | rfl <;> simp_all
    have hc := Finset.card_le_card hs
    simp [h01, hcard] at hc
  · have h2 := h02 h0
    have hs : S ⊆ {a0, a3} := by
      intro x hx
      have hxall := hsub hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxall
      rcases hxall with rfl | rfl | rfl | rfl <;> simp_all
    have hc := Finset.card_le_card hs
    simp [h03, hcard] at hc
  · have h3 := h13' h1
    have hs : S ⊆ {a1, a2} := by
      intro x hx
      have hxall := hsub hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxall
      rcases hxall with rfl | rfl | rfl | rfl <;> simp_all
    have hc := Finset.card_le_card hs
    simp [h12, hcard] at hc
  · have hs : S ⊆ {a2, a3} := by
      intro x hx
      have hxall := hsub hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxall
      rcases hxall with rfl | rfl | rfl | rfl <;> simp_all
    have hc := Finset.card_le_card hs
    simp [h23, hcard] at hc

/-- The centers whose starting indices differ by two already share a service
neighbor: the second center belongs to the first center's forced two-star
target set. -/
theorem h305_antipodalCenter_oppositePair_has_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (i : Fin 2) :
    let a := h305AntipodalCenter R u hmode ⟨i.1, by omega⟩
    let d := h305AntipodalCenter R u hmode ⟨i.1 + 2, by omega⟩
    ∃ c : R.edgeFinset, Cedge.Adj a c ∧ Cedge.Adj d c := by
  classical
  dsimp only
  let p : Fin 4 := ⟨i.1, by omega⟩
  let q : Fin 4 := ⟨i.1 + 2, by omega⟩
  let a := h305AntipodalCenter R u hmode p
  let d := h305AntipodalCenter R u hmode q
  let z : ZMod 8 := i.1
  have hdmem : d.1 ∈ h305AntipodalSaturatedStarUnion R u z := by
    rw [h305AntipodalSaturatedStarUnion, Finset.mem_union]
    apply Or.inl
    rw [R.incidenceFinset_eq_filter]
    refine Finset.mem_filter.mpr ⟨d.2, ?_⟩
    apply Sym2.mem_toFinset.mp
    have hdset := h305AntipodalCenter_toFinset R u hmode q
    rw [hdset]
    simpa [q, z]
  have hforced := h305_antipodalSaturatedStarUnion_forced_common
    H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu
      a z (z + 4) (by ring)
      (by simpa [a, p, z] using
        h305AntipodalCenter_toFinset R u hmode p)
      d.1 hdmem
  obtain ⟨c, hcval, hccommon⟩ := hforced
  have hdval : c = d := by
    apply Subtype.ext
    exact hcval
  subst c
  obtain ⟨c, hc⟩ := hccommon
  have hcmem := Finset.mem_inter.mp hc
  exact ⟨c,
    (Cedge.mem_neighborFinset a c).mp hcmem.2,
    (Cedge.mem_neighborFinset d c).mp hcmem.1⟩

/-- Every three-element subset of the four coordinate centers contains one
of the two opposite-index pairs, and that pair has a common service
neighbor. -/
theorem h305_three_antipodalCenters_contain_paired_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (S : Finset R.edgeFinset)
    (hsub : S ⊆ h305AntipodalCenterFinset R u hmode)
    (hcard : S.card = 3) :
    ∃ i : Fin 2,
      h305AntipodalCenter R u hmode ⟨i.1, by omega⟩ ∈ S ∧
      h305AntipodalCenter R u hmode ⟨i.1 + 2, by omega⟩ ∈ S ∧
      ∃ c : R.edgeFinset,
        Cedge.Adj (h305AntipodalCenter R u hmode ⟨i.1, by omega⟩) c ∧
        Cedge.Adj
          (h305AntipodalCenter R u hmode ⟨i.1 + 2, by omega⟩) c := by
  classical
  let f := h305AntipodalCenter R u hmode
  have hfinj : Function.Injective f :=
    h305AntipodalCenter_injective R u huinj hmode
  have hcenters : h305AntipodalCenterFinset R u hmode =
      {f 0, f 1, f 2, f 3} := by
    ext a
    simp only [h305AntipodalCenterFinset, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [f]
    · intro ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  have hpairs := three_of_four_contains_opposite_pair
    (f 0) (f 1) (f 2) (f 3)
    (hfinj.ne (by decide)) (hfinj.ne (by decide))
    (hfinj.ne (by decide)) (hfinj.ne (by decide))
    (hfinj.ne (by decide)) (hfinj.ne (by decide)) S
    (hcenters ▸ hsub) hcard
  rcases hpairs with h02 | h13
  · refine ⟨0, h02.1, h02.2, ?_⟩
    simpa [f] using
      h305_antipodalCenter_oppositePair_has_commonNeighbor
        H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu hmode 0
  · refine ⟨1, h13.1, h13.2, ?_⟩
    simpa [f] using
      h305_antipodalCenter_oppositePair_has_commonNeighbor
        H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu hmode 1

/-- The triple-target package may be chosen so that two of its selected
centers form an opposite-index pair with their own (forced) common service
neighbor.  This is the input for the equal-witness versus length-six-walk
terminal split. -/
theorem h305_exists_tripleTarget_packed_with_pairedCenterWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hzero : (shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 0).card = 12) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    let A := h305AntipodalCenterFinset R u hmode
    ∃ b ∈ shoreTypeEdgeFinset R U 0,
      ∃ S : Finset R.edgeFinset, S ⊆ A ∧ S.card = 3 ∧
        (∃ w : ↥(S : Set R.edgeFinset) → R.edgeFinset,
          (∀ a, Cedge.Adj b (w a) ∧ Cedge.Adj a.1 (w a)) ∧
          ∀ a d, w a ≠ w d →
            Disjoint (w a).1.toFinset (w d).1.toFinset) ∧
        ∃ i : Fin 2,
          h305AntipodalCenter R u hmode ⟨i.1, by omega⟩ ∈ S ∧
          h305AntipodalCenter R u hmode ⟨i.1 + 2, by omega⟩ ∈ S ∧
          ∃ y : R.edgeFinset,
            Cedge.Adj
              (h305AntipodalCenter R u hmode ⟨i.1, by omega⟩) y ∧
            Cedge.Adj
              (h305AntipodalCenter R u hmode ⟨i.1 + 2, by omega⟩) y := by
  classical
  dsimp only
  obtain ⟨b, hb, S, hSA, hScard, w, hw, hdisj⟩ :=
    h305_antipodalCenters_exists_tripleTarget_with_witnessPacking
      H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu hmode hzero
  refine ⟨b, hb, S, hSA, hScard, ⟨w, hw, hdisj⟩, ?_⟩
  exact h305_three_antipodalCenters_contain_paired_commonNeighbor
    H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu hmode
      S hSA hScard

end

end Erdos85

#print axioms Erdos85.three_of_four_contains_opposite_pair
#print axioms
  Erdos85.h305_antipodalCenter_oppositePair_has_commonNeighbor
#print axioms
  Erdos85.h305_three_antipodalCenters_contain_paired_commonNeighbor
#print axioms
  Erdos85.h305_exists_tripleTarget_packed_with_pairedCenterWitness
