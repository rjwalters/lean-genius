import Proofs.InverseGaloisD4OQ01

/-
# Inverse Galois D₄ — OQ-01 (external packaging): `D₄ ≅ ℤ/4 ⋊ ℤ/2`

`InverseGaloisD4OQ01` exhibits the *internal* semidirect-product decomposition
of `DihedralGroup 4` (a normal rotation subgroup `≅ ℤ/4`, an order-2 reflection
complement `≅ ℤ/2`, acting by inversion). This file packages that data as an
honest *external* `MulEquiv`

    SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) φ
      ≃* DihedralGroup 4,

with `φ` the ℤ/2-action sending the nontrivial generator to inversion of ℤ/4.
Mathlib has `SemidirectProduct` but no `DihedralGroup n` as an explicit
semidirect product, so this is a genuine addition rather than a re-export.

The compatibility hypothesis of `SemidirectProduct.lift` collapses, on the
nontrivial ℤ/2 generator, to exactly `reflection_conj_rotation'` (already
proven); bijectivity is established directly (no `Fintype`/cardinality input).
-/

namespace InverseGaloisD4OQ01External

open DihedralGroup InverseGaloisD4OQ01

/-! ## The inversion action `φ : ℤ/2 → Aut(ℤ/4)` -/

/-- Inversion automorphism of the commutative group `ℤ/4`. -/
def invAut : MulAut (Multiplicative (ZMod 4)) where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := mul_inv a b

@[simp] theorem invAut_apply (x : Multiplicative (ZMod 4)) : invAut x = x⁻¹ := rfl

theorem invAut_mul_self : invAut * invAut = 1 := by
  ext x; simp [MulAut.mul_apply, MulAut.one_apply]

/-- In `ℤ/2`, every nonzero element is `1`. -/
theorem zmod2_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

/-- The ℤ/2-action by inversion: the nontrivial generator acts as `invAut`. -/
def φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 4)) where
  toFun g := if g.toAdd = 0 then 1 else invAut
  map_one' := by simp
  map_mul' a b := by
    have hab : (a * b).toAdd = a.toAdd + b.toAdd := toAdd_mul a b
    rw [hab]
    by_cases ha : a.toAdd = 0 <;> by_cases hb : b.toAdd = 0
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
    · have c1 : (1 + 1 : ZMod 2) = 0 := by decide
      have c2 : ¬ (1 : ZMod 2) = 0 := by decide
      rw [zmod2_eq_one ha, zmod2_eq_one hb, if_pos c1, if_neg c2]
      simp [invAut_mul_self]

/-- The reflection complement homomorphism `ℤ/2 → D₄`. -/
def sHom : Multiplicative (ZMod 2) →* DihedralGroup 4 where
  toFun g := if g.toAdd = 0 then 1 else sr 0
  map_one' := by simp
  map_mul' a b := by
    have hab : (a * b).toAdd = a.toAdd + b.toAdd := toAdd_mul a b
    rw [hab]
    by_cases ha : a.toAdd = 0 <;> by_cases hb : b.toAdd = 0
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
    · have c1 : (1 + 1 : ZMod 2) = 0 := by decide
      have c2 : ¬ (1 : ZMod 2) = 0 := by decide
      rw [zmod2_eq_one ha, zmod2_eq_one hb, if_pos c1, if_neg c2]
      simp [sr_mul_self]

theorem sHom_ofAdd_one : sHom (Multiplicative.ofAdd (1 : ZMod 2)) = sr 0 := by
  simp only [sHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [if_neg (by decide)]

/-! ## Compatibility of the lift (the inversion twist) -/

/-- The `SemidirectProduct.lift` compatibility condition: conjugation by the
reflection inverts the rotations, exactly `reflection_conj_rotation'`. -/
theorem lift_compat (g : Multiplicative (ZMod 2)) :
    rHom.comp (φ g).toMonoidHom
      = (MulAut.conj (sHom g)).toMonoidHom.comp rHom := by
  ext n
  have hrn : rHom n = r (Multiplicative.toAdd n) := rfl
  by_cases hg : Multiplicative.toAdd g = 0
  · have hφ1 : φ g = 1 := by
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]; rw [if_pos hg]
    have hs1 : sHom g = 1 := by
      simp only [sHom, MonoidHom.coe_mk, OneHom.coe_mk]; rw [if_pos hg]
    simp only [MonoidHom.comp_apply, hφ1, hs1]
    simp [MulAut.conj_apply]
  · have hφ : φ g = invAut := by
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]; rw [if_neg hg]
    have hs : sHom g = sr 0 := by
      simp only [sHom, MonoidHom.coe_mk, OneHom.coe_mk]; rw [if_neg hg]
    simp only [MonoidHom.comp_apply, hφ, hs]
    show rHom n⁻¹ = sr 0 * rHom n * (sr 0)⁻¹
    rw [map_inv, hrn, reflection_conj_rotation']

/-! ## The external semidirect-product isomorphism -/

/-- The lift `ℤ/4 ⋊ ℤ/2 → D₄`. -/
noncomputable def d4Hom :
    SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) φ
      →* DihedralGroup 4 :=
  SemidirectProduct.lift rHom sHom lift_compat

theorem d4Hom_apply
    (x : SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) φ) :
    d4Hom x = rHom x.left * sHom x.right := by
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul]
  simp [d4Hom, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]

theorem d4Hom_surjective : Function.Surjective d4Hom := by
  intro y
  cases y with
  | r i =>
    exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd i), by
      simp [d4Hom, SemidirectProduct.lift_inl]⟩
  | sr i =>
    refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd (-i)) *
      SemidirectProduct.inr (Multiplicative.ofAdd 1), ?_⟩
    rw [map_mul]
    simp only [d4Hom, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr,
      rHom_ofAdd, sHom_ofAdd_one]
    rw [r_mul_sr]; congr 1; ring

theorem d4Hom_injective : Function.Injective d4Hom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [d4Hom_apply] at hx
  by_cases hr : x.right.toAdd = 0
  · have hs1 : sHom x.right = 1 := by
      simp only [sHom, MonoidHom.coe_mk, OneHom.coe_mk]; rw [if_pos hr]
    rw [hs1, mul_one] at hx
    have hl0 : x.left.toAdd = 0 := by
      have h1 : (r x.left.toAdd : DihedralGroup 4) = r 0 := by
        rw [← DihedralGroup.one_def]; exact hx
      exact DihedralGroup.r.inj h1
    have hxl : x.left = 1 :=
      Multiplicative.toAdd.injective (by rw [hl0, toAdd_one])
    have hxr : x.right = 1 :=
      Multiplicative.toAdd.injective (by rw [hr, toAdd_one])
    exact SemidirectProduct.ext hxl hxr
  · exfalso
    have hs : sHom x.right = sr 0 := by
      simp only [sHom, MonoidHom.coe_mk, OneHom.coe_mk]; rw [if_neg hr]
    rw [hs, show rHom x.left = r x.left.toAdd from rfl, r_mul_sr,
      DihedralGroup.one_def] at hx
    exact DihedralGroup.noConfusion hx

theorem d4Hom_bijective : Function.Bijective d4Hom :=
  ⟨d4Hom_injective, d4Hom_surjective⟩

/-- **External semidirect product**: `D₄ ≅ ℤ/4 ⋊ ℤ/2` with the inversion
action. The Galois group `Gal(ℚ(⁴√2, i)/ℚ)` (order 8, `d4_realizable`) is thus
identified, as an abstract group, with the explicit semidirect product. -/
noncomputable def d4Equiv :
    SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) φ
      ≃* DihedralGroup 4 :=
  MulEquiv.ofBijective d4Hom d4Hom_bijective

end InverseGaloisD4OQ01External
