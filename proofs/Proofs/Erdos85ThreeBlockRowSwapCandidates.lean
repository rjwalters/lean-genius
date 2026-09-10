import Proofs.Erdos85ThreeBlockRowSwap
import Proofs.Erdos85EncodedRelabeling

namespace Erdos85

def threeBlockFullRowSwap (p : ThreeBlockFullParameters) : ThreeBlockFullParameters :=
  (fun k => p.1 (threeBlockSwapRows k),p.2.symm)

def threeBlockDeficientRowSwap (p : ThreeBlockDeficientParameters) : ThreeBlockDeficientParameters :=
  (threeBlockFullRowSwap p.1,p.1.2 p.2)

def threeBlockSwapLabels : Equiv.Perm (Fin 3 × Fin 5) :=
  Equiv.prodCongr threeBlockSwapRows (Equiv.refl (Fin 5))

theorem threeBlockFullRowSwap_c4 (p : ThreeBlockFullParameters) :
    encodedC4Free (threeBlockFullParameterAdj p) =
      encodedC4Free (threeBlockFullParameterAdj (threeBlockFullRowSwap p)) := by
  have he : threeBlockFullParameterAdj p = fun a b =>
      threeBlockFullParameterAdj (threeBlockFullRowSwap p)
        (threeBlockSwapLabels a) (threeBlockSwapLabels b) := by
    funext a b
    exact threeBlockMatchingAdj_swap_rows (fun k => (p.1 k).val) p.2 a b
  calc
    _ = encodedC4Free (fun a b => threeBlockFullParameterAdj (threeBlockFullRowSwap p)
        (threeBlockSwapLabels a) (threeBlockSwapLabels b)) := congrArg encodedC4Free he
    _ = _ := encodedC4Free_relabel _ threeBlockSwapLabels

theorem threeBlockDeficientRowSwap_c4 (p : ThreeBlockDeficientParameters) :
    encodedC4Free (threeBlockDeficientParameterAdj p) =
      encodedC4Free (threeBlockDeficientParameterAdj (threeBlockDeficientRowSwap p)) := by
  have he : threeBlockDeficientParameterAdj p = fun a b =>
      threeBlockDeficientParameterAdj (threeBlockDeficientRowSwap p)
        (threeBlockSwapLabels a) (threeBlockSwapLabels b) := by
    funext a b
    exact threeBlockDeficientMatchingAdj_swap_rows (fun k => (p.1.1 k).val) p.1.2 p.2 a b
  calc
    _ = encodedC4Free (fun a b => threeBlockDeficientParameterAdj (threeBlockDeficientRowSwap p)
        (threeBlockSwapLabels a) (threeBlockSwapLabels b)) := congrArg encodedC4Free he
    _ = _ := encodedC4Free_relabel _ threeBlockSwapLabels

theorem threeBlockFullRowSwap_mem_iff (p : ThreeBlockFullParameters) :
    threeBlockFullRowSwap p ∈ threeBlockFullCandidates ↔ p ∈ threeBlockFullCandidates := by
  rw [threeBlockFullCandidates_mem_iff,threeBlockFullCandidates_mem_iff,
    ← threeBlockFullRowSwap_c4]

theorem threeBlockDeficientRowSwap_mem_iff (p : ThreeBlockDeficientParameters) :
    threeBlockDeficientRowSwap p ∈ threeBlockDeficientCandidates ↔ p ∈ threeBlockDeficientCandidates := by
  rw [threeBlockDeficientCandidates_mem_iff,threeBlockDeficientCandidates_mem_iff,
    ← threeBlockDeficientRowSwap_c4]

/-- Swapping the other two rows preserves the normalized first matching exactly. -/
theorem threeBlockFullRowSwap_first (p : ThreeBlockFullParameters) :
    (threeBlockFullRowSwap p).1 0 = p.1 0 := by
  simp [threeBlockFullRowSwap,threeBlockSwapRows,Equiv.swap_apply_def]

end Erdos85
#print axioms Erdos85.threeBlockFullRowSwap_c4
#print axioms Erdos85.threeBlockDeficientRowSwap_c4
#print axioms Erdos85.threeBlockFullRowSwap_mem_iff
#print axioms Erdos85.threeBlockDeficientRowSwap_mem_iff
#print axioms Erdos85.threeBlockFullRowSwap_first
