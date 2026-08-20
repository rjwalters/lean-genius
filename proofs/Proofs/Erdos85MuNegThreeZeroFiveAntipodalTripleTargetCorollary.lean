import Proofs.Erdos85MuNegThreeZeroFiveAntipodalTripleTarget
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalTypeZeroLower

/-! # Native four-center antipodal triple-target consequence -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the full two-shore h305 geometry, some opposite-shore exterior edge
shares a service neighbor with at least three of the four antipodal edges
of the selected shore. -/
theorem h305_exists_typeZero_target_common_to_three_antipodal_centers
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    let center : Fin 4 → R.edgeFinset := fun p ↦
      ⟨s(u (p.val : ZMod 8), u ((p.val : ZMod 8) + 4)),
        R.mem_edgeFinset.mpr (by
          rcases humode with htri | htf
          · exact (htri _ _).2 (Or.inr (Or.inl (by ring)))
          · exact (htf _ _).2 (Or.inr (Or.inl (by ring))))⟩
    let A := (Finset.univ : Finset (Fin 4)).image center
    ∃ b ∈ shoreTypeEdgeFinset R U 0,
      3 ≤ (A.filter fun a ↦
        b ∈ offDiagonalCommonNeighborSupport Cedge a).card := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  have hadj : ∀ z : ZMod 8, R.Adj (u z) (u (z + 4)) := by
    intro z
    rcases humode with htri | htf
    · exact (htri z (z + 4)).2 (Or.inr (Or.inl (by ring)))
    · exact (htf z (z + 4)).2 (Or.inr (Or.inl (by ring)))
  let center : Fin 4 → R.edgeFinset := fun p ↦
    ⟨s(u (p.val : ZMod 8), u ((p.val : ZMod 8) + 4)),
      R.mem_edgeFinset.mpr (hadj (p.val : ZMod 8))⟩
  let A := (Finset.univ : Finset (Fin 4)).image center
  have hcenterinj : Function.Injective center := by
    intro p q hpq
    let eu : ZMod 8 ↪ V := ⟨u, huinj⟩
    have hpairs := congrArg (fun a : R.edgeFinset ↦ a.1.toFinset) hpq
    have hmaps : ({(p.val : ZMod 8), (p.val : ZMod 8) + 4} :
          Finset (ZMod 8)).map eu =
        ({(q.val : ZMod 8), (q.val : ZMod 8) + 4} :
          Finset (ZMod 8)).map eu := by
      simpa [center, eu, Sym2.toFinset_mk_eq] using hpairs
    have hcoords : ({(p.val : ZMod 8), (p.val : ZMod 8) + 4} :
          Finset (ZMod 8)) =
        ({(q.val : ZMod 8), (q.val : ZMod 8) + 4} :
          Finset (ZMod 8)) := Finset.map_injective eu hmaps
    have hnative : ∀ p q : Fin 4,
        ({(p.val : ZMod 8), (p.val : ZMod 8) + 4} : Finset (ZMod 8)) =
          ({(q.val : ZMod 8), (q.val : ZMod 8) + 4} : Finset (ZMod 8)) →
            p = q := by native_decide
    exact hnative p q hcoords
  have hA : A.card = 4 := by
    change ((Finset.univ : Finset (Fin 4)).image center).card = 4
    rw [Finset.card_image_of_injective _ hcenterinj]
    decide
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover humode hvmode hRreg
  have hzero : (shoreTypeEdgeFinset R U 0).card = 12 := by
    simpa [U] using hpop.2.2
  apply h305_four_antipodal_centers_have_triple_typeZero_target
    R Cedge U A hA hzero
  intro a haA
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp haA
  apply h305_antipodal_offDiagonalCommon_typeZero_seven_le
    H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu humode
      (center p) (p.val : ZMod 8) ((p.val : ZMod 8) + 4)
  · ring
  · exact Sym2.toFinset_mk_eq

end

end Erdos85

#print axioms
  Erdos85.h305_exists_typeZero_target_common_to_three_antipodal_centers
