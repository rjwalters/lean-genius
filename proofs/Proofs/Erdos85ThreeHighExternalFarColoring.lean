import Proofs.Erdos85ThreeHighFarWitness
import Proofs.Erdos85ThreeHighFarConflict
import Proofs.Erdos85ThreeHighExternalBlockFactorization

namespace Erdos85

theorem threeHighCrossBlockCap_same_block
    (cross : ThreeHighCross) (hc : threeHighCrossBlockCap cross = true)
    (x y : Fin 15) (hxy : x ≠ y)
    (hb : ((@finProdFinEquiv 3 5).symm x).1 = ((@finProdFinEquiv 3 5).symm y).1)
    (j : Fin 8) (hx : cross x j = true) (hy : cross y j = true) : False := by
  obtain ⟨⟨k,i⟩,rfl⟩ := (@finProdFinEquiv 3 5).surjective x
  obtain ⟨⟨l,t⟩,rfl⟩ := (@finProdFinEquiv 3 5).surjective y
  simp only [Equiv.symm_apply_apply] at hb
  change k = l at hb
  subst l
  unfold threeHighCrossBlockCap at hc
  have hh := of_decide_eq_true hc j k
  have hi : i ∈ Finset.univ.filter (fun a => cross ((@finProdFinEquiv 3 5) (k,a)) j) := by
    simp [hx]
  have ht : t ∈ Finset.univ.filter (fun a => cross ((@finProdFinEquiv 3 5) (k,a)) j) := by
    simp [hy]
  have he := Finset.card_le_one.mp hh _ hi _ ht
  exact hxy (by rw [he])

attribute [local irreducible] threeHighCrossDomain

/-- Low U vertices choose far labels; common U neighbors and common blocks forbid equal choices. -/
theorem threeHighCrossDomain_external_far_coloring
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hcap : threeHighCrossBlockCap cross = true) :
    ∃ c : Fin 15 → Fin 2,
      ∀ x y, encodedRowDegree (U x) ≤ 2 → encodedRowDegree (U y) ≤ 2 →
        x ≠ y → ((∃ s, U x s = true ∧ U y s = true) ∨
          ((@finProdFinEquiv 3 5).symm x).1 = ((@finProdFinEquiv 3 5).symm y).1) →
        c x ≠ c y := by
  classical
  have hw : ∀ x, ∃ a : Fin 8, 6 ≤ a.val ∧
      (encodedRowDegree (U x) ≤ 2 → cross x a = true) := by
    intro x
    by_cases hx : encodedRowDegree (U x) ≤ 2
    · obtain ⟨a,ha,hxa⟩ := threeHighCrossDomain_low_degree_far U R cross hc x hx
      exact ⟨a,ha,fun _ => hxa⟩
    · exact ⟨6,by decide,fun h => False.elim (hx h)⟩
  choose f hfar hcross using hw
  let c : Fin 15 → Fin 2 := fun x => ⟨(f x).val - 6,by
    have := (f x).isLt
    have := hfar x
    omega⟩
  have hinj {x y : Fin 15} (he : c x = c y) : f x = f y := by
    apply Fin.ext
    have hv := congrArg Fin.val he
    change (f x).val - 6 = (f y).val - 6 at hv
    have := hfar x
    have := hfar y
    omega

  have hC4 := ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  refine ⟨c,?_⟩
  intro x y hx hy hxy hconf he
  have hf := hinj he
  have hyf : cross y (f x) = true := by rw [hf]; exact hcross y hy
  rcases hconf with ⟨s,hxs,hys⟩ | hb
  · exact threeHighEmptyAdj_common_U_not_cross U R cross hC4 x y s hxy hxs hys
      (f x) (hcross x hx) hyf
  · exact threeHighCrossBlockCap_same_block cross hcap x y hxy hb
      (f x) (hcross x hx) hyf

end Erdos85
#print axioms Erdos85.threeHighCrossBlockCap_same_block
#print axioms Erdos85.threeHighCrossDomain_external_far_coloring
