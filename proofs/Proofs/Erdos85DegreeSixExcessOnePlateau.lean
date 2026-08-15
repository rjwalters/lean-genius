import Proofs.Erdos85DegreeSixBoundaryPackage
import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# The degree-six excess-one plateau kernel

The order-34 residue of the degree-six plateau band feeds directly into the
mod-two defect-kernel theorem.  This file exports that consequence without
requiring later assembly code to unpack `PositiveExcessPlateauData`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Every hypothetical degree-six plateau core at order 34 carries a proper,
nonempty defect set satisfying the exact mod-two neighborhood law. -/
theorem C4PlateauCore.degreeSix_thirtyFour_exists_odd_defect_set
    (hcore : C4PlateauCore 34 6) :
    ∃ (G : SimpleGraph (Fin 34)) (_ : DecidableRel G.Adj)
        (W : Finset (Fin 34)),
      ¬ containsC4 (Fin 34) G ∧
      (∀ x, G.degree x = 6) ∧
      W ≠ ∅ ∧ W ≠ Finset.univ ∧ ∀ v : Fin 34,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) = 0 := by
  rcases hcore.degreeSix_thirtyFour_positiveExcessOne with
    ⟨_hm, _he, G, hdec, hfree, hreg, _hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨W, hWempty, hWuniv, hWparity⟩ :=
    excessOne_even_exists_odd_defect_set G hfree (by decide) hreg (by norm_num)
  exact ⟨G, hdec, W, hfree, hreg, hWempty, hWuniv, hWparity⟩

end

end Erdos85
