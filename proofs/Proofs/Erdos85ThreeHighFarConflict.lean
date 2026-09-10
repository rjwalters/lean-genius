import Proofs.Erdos85ThreeHighRootRowPruning

namespace Erdos85

/-- Two distinct U vertices sharing a U neighbor cannot also share an R neighbor. -/
theorem threeHighEmptyAdj_common_U_not_cross
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross)
    (hc : encodedC4Free (threeHighEmptyAdj UAdj RAdj cross) = true)
    (x y s : Fin 15) (hxy : x ≠ y) (hxs : UAdj x s = true) (hys : UAdj y s = true)
    (j : Fin 8) (hxj : cross x j = true) (hyj : cross y j = true) : False := by
  unfold encodedC4Free at hc
  simp only [decide_eq_true_eq] at hc
  have hne : threeHighEmptyUIndex x ≠ threeHighEmptyUIndex y := by
    intro he
    apply hxy
    apply Fin.ext
    simpa only [threeHighEmptyUIndex, Fin.val_castAdd] using
      congrArg (fun a : Fin 24 => a.val) he
  have h := hc (threeHighEmptyUIndex x) (threeHighEmptyUIndex y) hne
  have hs : threeHighEmptyUIndex s ∈ Finset.univ.filter (fun q =>
      threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyUIndex x) q &&
      threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyUIndex y) q) := by
    simp [threeHighEmptyAdj,hxs,hys]
  have hj : threeHighEmptyRIndex j ∈ Finset.univ.filter (fun q =>
      threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyUIndex x) q &&
      threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyUIndex y) q) := by
    simp [threeHighEmptyAdj,hxj,hyj]
  have he := Finset.card_le_one.mp h _ hs _ hj
  have hv := congrArg Fin.val he
  change s.val = 15 + j.val at hv
  have := s.isLt
  omega

end Erdos85
#print axioms Erdos85.threeHighEmptyAdj_common_U_not_cross
