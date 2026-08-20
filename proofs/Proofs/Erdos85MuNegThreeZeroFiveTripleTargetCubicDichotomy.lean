import Proofs.Erdos85AdjacencyCubeTwoWalkLower

/-! # Cubic consequence of the packed antipodal triple target -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- In the h305 antipodal configuration there is a type-zero target `b` and
a paired-center witness `y` such that either `b,y` are adjacent or the cubic
service entry from `b` to `y` is at least two. -/
theorem h305_exists_typeZeroTarget_fan_or_cube_ge_two
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
    ∃ b ∈ shoreTypeEdgeFinset R U 0, ∃ y : R.edgeFinset,
      Cedge.Adj b y ∨
        (2 : ℤ) ≤ (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ *
          Cedge.adjMatrix ℤ) b y := by
  classical
  dsimp only
  obtain ⟨b, hb, S, _hSA, _hScard, ⟨w, hw, _hdisj⟩,
      i, haS, hdS, y, hay, hdy⟩ :=
    h305_exists_tripleTarget_packed_with_pairedCenterWitness
      H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu hmode hzero
  let ia : Fin 4 := ⟨i.1, by omega⟩
  let id : Fin 4 := ⟨i.1 + 2, by omega⟩
  let a := h305AntipodalCenter R u hmode ia
  let d := h305AntipodalCenter R u hmode id
  have hadIndex : ia ≠ id := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ia, id] at hv
    omega
  have had : a ≠ d :=
    (h305AntipodalCenter_injective R u huinj hmode).ne hadIndex
  let aS : ↥(S : Set R.edgeFinset) := ⟨a, by simpa [a, ia] using haS⟩
  let dS : ↥(S : Set R.edgeFinset) := ⟨d, by simpa [d, id] using hdS⟩
  have hwa := hw aS
  have hwd := hw dS
  refine ⟨b, hb, y, ?_⟩
  exact c4Free_pairedCommonTarget_fan_or_cube_ge_two Cedge hfree
    a d b y (w aS) (w dS) had hwa.2 hwa.1 hwd.2 hwd.1
      (by simpa [a, ia] using hay) (by simpa [d, id] using hdy)

end

end Erdos85

#print axioms Erdos85.h305_exists_typeZeroTarget_fan_or_cube_ge_two
