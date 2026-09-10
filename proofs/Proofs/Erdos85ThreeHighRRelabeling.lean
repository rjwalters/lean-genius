import Proofs.Erdos85ThreeHighOrbitJointTransport

namespace Erdos85

/-- Extend an R permutation, fixing U and the root. -/
def threeHighEmptyRRelabel (e : Equiv.Perm (Fin 8)) : Equiv.Perm (Fin 24) :=
  let split := (@finSumFinEquiv 23 1).symm.trans
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1)))
  split.trans ((Equiv.sumCongr (Equiv.sumCongr (Equiv.refl (Fin 15)) e)
    (Equiv.refl (Fin 1))).trans split.symm)

theorem threeHighEmptySplit_Rrelabel (e : Equiv.Perm (Fin 8)) (p : Fin 24) :
    threeHighEmptySplit (threeHighEmptyRRelabel e p) =
      Sum.map (Sum.map id e) id (threeHighEmptySplit p) := by
  let split := (@finSumFinEquiv 23 1).symm.trans
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1)))
  change split (split.symm ((Equiv.sumCongr (Equiv.sumCongr (Equiv.refl (Fin 15)) e)
    (Equiv.refl (Fin 1))) (split p))) = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] theorem threeHighEmptyRRelabel_root (e : Equiv.Perm (Fin 8)) :
    threeHighEmptyRRelabel e 23 = 23 := by
  have h := threeHighEmptySplit_Rrelabel e 23
  simp only [threeHighEmptySplit_root,Sum.map_inr,id_eq] at h
  have hinj : Function.Injective threeHighEmptySplit :=
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1))).injective.comp
      (@finSumFinEquiv 23 1).symm.injective
  apply hinj
  simpa using h

theorem threeHighEmptyAdj_relabel_R
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (e : Equiv.Perm (Fin 8))
    (hnear : ∀ j, (e j).val < 6 ↔ j.val < 6) (p q : Fin 24) :
    threeHighEmptyAdj U (fun x y => R (e x) (e y)) (fun x j => cross x (e j)) p q =
      threeHighEmptyAdj U R cross (threeHighEmptyRRelabel e p) (threeHighEmptyRRelabel e q) := by
  simp only [threeHighEmptyAdj,threeHighEmptySplit_Rrelabel]
  rcases threeHighEmptySplit p with (x | x) | x <;>
    rcases threeHighEmptySplit q with (y | y) | y <;> simp [hnear]

attribute [local irreducible] threeHighCrossDomain

/-- Reindexing R within the near/far partition preserves the full cross-domain conditions. -/
theorem threeHighCrossDomain_relabel_R
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (e : Equiv.Perm (Fin 8))
    (hnear : ∀ j, (e j).val < 6 ↔ j.val < 6)
    (hc : cross ∈ threeHighCrossDomain U R) :
    (fun x j => cross x (e j)) ∈ threeHighCrossDomain U (fun x y => R (e x) (e y)) := by
  obtain ⟨hfree,hdeg⟩ := (mem_threeHighCrossDomain_iff U R cross).mp hc
  apply (mem_threeHighCrossDomain_iff _ _ _).mpr
  have hB : threeHighEmptyAdj U (fun x y => R (e x) (e y)) (fun x j => cross x (e j)) =
      fun p q => threeHighEmptyAdj U R cross (threeHighEmptyRRelabel e p) (threeHighEmptyRRelabel e q) :=
    funext fun p => funext fun q => threeHighEmptyAdj_relabel_R U R cross e hnear p q
  rw [hB]
  refine ⟨?_,?_⟩
  · simpa only [encodedC4Free_relabel] using hfree
  · have hd := encodedDegreeProfile_relabel (threeHighEmptyAdj U R cross)
      (fun i => if i = 23 then 6 else 4) (threeHighEmptyRRelabel e)
    have hr (p : Fin 24) : threeHighEmptyRRelabel e p = 23 ↔ p = 23 := by
      rw [← threeHighEmptyRRelabel_root e]
      exact (threeHighEmptyRRelabel e).injective.eq_iff
    simp only [hr] at hd
    exact hd.trans hdeg


@[simp] theorem threeHighEmptyRRelabel_u (e : Equiv.Perm (Fin 8)) (i : Fin 15) :
    threeHighEmptyRRelabel e (threeHighEmptyUIndex i) = threeHighEmptyUIndex i := by
  have hinj : Function.Injective threeHighEmptySplit :=
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1))).injective.comp
      (@finSumFinEquiv 23 1).symm.injective
  apply hinj
  simp only [threeHighEmptySplit_Rrelabel,threeHighEmptySplit_u,Sum.map_inl,id_eq]

theorem threeHighEmptyRRelabel_rows (e : Equiv.Perm (Fin 8)) (k : Fin 3) :
    (threeHighCanonicalRow k).image (threeHighEmptyRRelabel e) = threeHighCanonicalRow k := by
  simp [threeHighCanonicalRow,Finset.image_image,Function.comp_def]

/-- An R automorphism preserving the root's near/far partition transports
an admissible completion and the same joint families. -/
theorem threeHighRAutomorphism_joint_transport
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (e : Equiv.Perm (Fin 8)) (hnear : ∀ j, (e j).val < 6 ↔ j.val < 6)
    (hR : ∀ i j, R (e i) (e j) = R i j)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    (fun i j => cross i (e j)) ∈ threeHighCrossDomain U R ∧
      encodedExternalBlockCap (threeHighEmptyAdj U R (fun i j => cross i (e j)))
        threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj U R (fun i j => cross i (e j))) := by
  have hRe : (fun i j => R (e i) (e j)) = R := funext fun i => funext fun j => hR i j
  let E := threeHighEmptyRRelabel e.symm
  have hAdj : threeHighEmptyAdj U R (fun i j => cross i (e j)) =
      fun x y => threeHighEmptyAdj U R cross (E.symm x) (E.symm y) := by
    funext x y
    have h := threeHighEmptyAdj_relabel_R U R cross e hnear x y
    rw [hRe] at h
    exact h
  have hrows (k : Fin 3) : (threeHighCanonicalRow k).image E = threeHighCanonicalRow k :=
    threeHighEmptyRRelabel_rows e.symm k
  refine ⟨?_,?_,?_⟩
  · simpa only [hRe] using threeHighCrossDomain_relabel_R U R cross e hnear hc
  · have h := (encodedExternalBlockCap_relabel (threeHighEmptyAdj U R cross)
        threeHighCanonicalRow E).trans hExt
    have hr : (fun k => (threeHighCanonicalRow k).image E) = threeHighCanonicalRow := funext hrows
    rw [hr,← hAdj] at h
    exact h
  · have h := hJoint.relabel (threeHighEmptyAdj U R cross) E (Equiv.refl (Fin 3))
      (threeHighEmptyRRelabel_root e.symm) hrows
    rw [← hAdj] at h
    exact h

end Erdos85
#print axioms Erdos85.threeHighEmptyAdj_relabel_R
#print axioms Erdos85.threeHighCrossDomain_relabel_R
#print axioms Erdos85.threeHighEmptyRRelabel_rows
#print axioms Erdos85.threeHighRAutomorphism_joint_transport
