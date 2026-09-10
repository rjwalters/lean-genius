import Proofs.Erdos85EncodedRelabeling

namespace Erdos85

/-- Extend a U permutation, fixing the eight R labels and the root. -/
def threeHighEmptyURelabel (e : Equiv.Perm (Fin 15)) : Equiv.Perm (Fin 24) :=
  let split := (@finSumFinEquiv 23 1).symm.trans
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1)))
  split.trans ((Equiv.sumCongr (Equiv.sumCongr e (Equiv.refl (Fin 8)))
    (Equiv.refl (Fin 1))).trans split.symm)

theorem threeHighEmptySplit_relabel (e : Equiv.Perm (Fin 15)) (p : Fin 24) :
    threeHighEmptySplit (threeHighEmptyURelabel e p) =
      Sum.map (Sum.map e id) id (threeHighEmptySplit p) := by
  let split := (@finSumFinEquiv 23 1).symm.trans
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1)))
  change split (split.symm ((Equiv.sumCongr (Equiv.sumCongr e (Equiv.refl (Fin 8)))
    (Equiv.refl (Fin 1))) (split p))) = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] theorem threeHighEmptyURelabel_root (e : Equiv.Perm (Fin 15)) :
    threeHighEmptyURelabel e 23 = 23 := by
  have h := threeHighEmptySplit_relabel e 23
  simp only [threeHighEmptySplit_root,Sum.map_inr,id_eq] at h
  have hinj : Function.Injective threeHighEmptySplit :=
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1))).injective.comp
      (@finSumFinEquiv 23 1).symm.injective
  apply hinj
  simpa using h

theorem threeHighEmptyAdj_relabel_U
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (e : Equiv.Perm (Fin 15)) (p q : Fin 24) :
    threeHighEmptyAdj (fun x y => U (e x) (e y)) R (fun x j => cross (e x) j) p q =
      threeHighEmptyAdj U R cross (threeHighEmptyURelabel e p) (threeHighEmptyURelabel e q) := by
  simp only [threeHighEmptyAdj,threeHighEmptySplit_relabel]
  rcases threeHighEmptySplit p with (x | x) | x <;>
    rcases threeHighEmptySplit q with (y | y) | y <;> rfl

attribute [local irreducible] threeHighCrossDomain

/-- Reindexing U preserves the full cross-domain conditions. -/
theorem threeHighCrossDomain_relabel_U
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (e : Equiv.Perm (Fin 15))
    (hc : cross ∈ threeHighCrossDomain U R) :
    (fun x j => cross (e x) j) ∈ threeHighCrossDomain (fun x y => U (e x) (e y)) R := by
  obtain ⟨hfree,hdeg⟩ := (mem_threeHighCrossDomain_iff U R cross).mp hc
  apply (mem_threeHighCrossDomain_iff _ _ _).mpr
  have hB : threeHighEmptyAdj (fun x y => U (e x) (e y)) R (fun x j => cross (e x) j) =
      fun p q => threeHighEmptyAdj U R cross (threeHighEmptyURelabel e p) (threeHighEmptyURelabel e q) :=
    funext fun p => funext fun q => threeHighEmptyAdj_relabel_U U R cross e p q
  rw [hB]
  refine ⟨?_,?_⟩
  · simpa only [encodedC4Free_relabel] using hfree
  · have hd := encodedDegreeProfile_relabel (threeHighEmptyAdj U R cross)
      (fun i => if i = 23 then 6 else 4) (threeHighEmptyURelabel e)
    have hr (p : Fin 24) : threeHighEmptyURelabel e p = 23 ↔ p = 23 := by
      rw [← threeHighEmptyURelabel_root e]
      exact (threeHighEmptyURelabel e).injective.eq_iff
    simp only [hr] at hd
    exact hd.trans hdeg

/-- A universal completion exclusion transfers along an exact U isomorphism. -/
theorem threeHighCrossDomain_no_cross_of_relabel
    (U V : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (e : Equiv.Perm (Fin 15)) (hUV : ∀ x y, U x y = V (e x) (e y))
    (hV : ∀ cross : ThreeHighCross, cross ∉ threeHighCrossDomain V R)
    (cross : ThreeHighCross) : cross ∉ threeHighCrossDomain U R := by
  intro hc
  have ht := threeHighCrossDomain_relabel_U U R cross e.symm hc
  have heq : (fun x y => U (e.symm x) (e.symm y)) = V := by
    funext x y
    simp only [hUV,Equiv.apply_symm_apply]
  rw [heq] at ht
  exact hV _ ht

end Erdos85
#print axioms Erdos85.threeHighEmptyAdj_relabel_U
#print axioms Erdos85.threeHighCrossDomain_relabel_U
#print axioms Erdos85.threeHighCrossDomain_no_cross_of_relabel
