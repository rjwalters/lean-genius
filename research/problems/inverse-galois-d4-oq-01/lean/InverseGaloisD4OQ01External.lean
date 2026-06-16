import Proofs.InverseGaloisD4OQ01

/-
# Inverse Galois D₄ — OQ-01 (external packaging): `DihedralGroup 4 ≃* ℤ/4 ⋊ ℤ/2`

⚠️ STATUS: **UNVERIFIED / build-pending.** This file was authored in a session
where neither a Docker build nor Aristotle was available (Docker VM saturated,
Aristotle backend 404). It is staged OUTSIDE `proofs/Proofs/` on purpose: every
file under `proofs/Proofs/` is auto-aggregated into `Proofs.lean`, so a broken
file would fail the whole deploy build. Do not move it into `proofs/Proofs/`
until it builds green under `./proofs/scripts/docker-build.sh`.

## What it adds over the internal decomposition

`InverseGaloisD4OQ01.lean` (registered, 0 sorry/0 axiom) already proves the
*internal* semidirect decomposition of `DihedralGroup 4` (normal rotation
subgroup ≅ ℤ/4, reflection complement ≅ ℤ/2, inversion action). This file
packages that as an honest *external* `MulEquiv`

    SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) φ
      ≃* DihedralGroup 4

with `φ` the ℤ/2-action sending the generator to inversion of ℤ/4. Mathlib
v4.26.0 has `SemidirectProduct` but no `DihedralGroup`-as-semidirect-product
result, so this is a genuine addition.

## API confirmed against pinned Mathlib (rev 2df2f01, v4.26.0)

* `SemidirectProduct.lift (fn fg) (h : ∀ g, fn.comp (φ g).toMonoidHom
    = (MulAut.conj (fg g)).toMonoidHom.comp fn)` with `toFun a := fn a.1 * fg a.2`
  (Mathlib/GroupTheory/SemidirectProduct.lean:194-206).
* `lift_inl : lift fn fg h (inl n) = fn n`, `lift_inr : … (inr g) = fg g`.
* `MulAut.conj_apply : MulAut.conj g h = g * h * g⁻¹` (used inside `lift`'s own
  proof, line 202).
* `Multiplicative.toAdd_mul`/`toAdd_inv`/`toAdd_one`/`toAdd_ofAdd` (all `rfl`,
  TypeTags/Basic.lean:166/390/251/119).
* DihedralGroup: `r_mul_sr i j : r i * sr j = sr (j - i)`, `sr_mul_self`,
  `inv_r`, `inv_sr`, `one_def`, constructor `r.injEq`/`sr.injEq`.

## Residual build risk (the only unverified parts)

1. `if · = 0`-condition discharge on `ZMod 2` inside `phi`/`sHom`/`lift_compat`
   (the `decide`-backed `zmod2_cases` + `simp` may need `decide` to close
   `(1 : ZMod 2) + 1 = 0` and `(1 : ZMod 2) ≠ 0`).
2. `MulAut.mul_apply`/`MulAut.one_apply` simp-lemma names in `invAut_mul_self`.
3. defeq unfolding of `SemidirectProduct.lift _ _ _ ⟨n, g⟩` to `rHom n * sHom g`
   in the bijectivity proofs.
-/

namespace InverseGaloisD4OQ01

open DihedralGroup SemidirectProduct

/-! ## The inversion automorphism of ℤ/4 -/

/-- Inversion is an automorphism of the commutative group `Multiplicative (ZMod 4)`. -/
def invAut : MulAut (Multiplicative (ZMod 4)) where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := mul_inv a b

@[simp] theorem invAut_apply (x : Multiplicative (ZMod 4)) : invAut x = x⁻¹ := rfl

theorem invAut_mul_self : invAut * invAut = 1 := by
  ext x; simp

/-! ## The ℤ/2 action by inversion and the reflection complement hom -/

/-- Every element of `ZMod 2` is `0` or `1` (decidable enumeration). -/
theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by decide

/-- The ℤ/2-action on ℤ/4 by inversion: the generator acts as `invAut`. -/
def φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 4)) where
  toFun g := if g.toAdd = 0 then 1 else invAut
  map_one' := by simp
  map_mul' a b := by
    rcases zmod2_cases a.toAdd with ha | ha <;>
      rcases zmod2_cases b.toAdd with hb | hb <;>
        simp [toAdd_mul, ha, hb, invAut_mul_self]

/-- The reflection complement hom `ℤ/2 → D₄`, generator ↦ `sr 0`. -/
def sHom : Multiplicative (ZMod 2) →* DihedralGroup 4 where
  toFun g := if g.toAdd = 0 then 1 else sr 0
  map_one' := by simp
  map_mul' a b := by
    rcases zmod2_cases a.toAdd with ha | ha <;>
      rcases zmod2_cases b.toAdd with hb | hb <;>
        simp [toAdd_mul, ha, hb, sr_mul_self] <;> decide

@[simp] theorem φ_zero {g : Multiplicative (ZMod 2)} (hg : g.toAdd = 0) : φ g = 1 := by
  show (if g.toAdd = 0 then (1 : MulAut _) else invAut) = 1
  rw [hg, if_pos rfl]

@[simp] theorem φ_one {g : Multiplicative (ZMod 2)} (hg : g.toAdd = 1) : φ g = invAut := by
  show (if g.toAdd = 0 then (1 : MulAut _) else invAut) = invAut
  rw [hg, if_neg (by decide)]

@[simp] theorem sHom_zero {g : Multiplicative (ZMod 2)} (hg : g.toAdd = 0) : sHom g = 1 := by
  show (if g.toAdd = 0 then (1 : DihedralGroup 4) else sr 0) = 1
  rw [hg, if_pos rfl]

@[simp] theorem sHom_one {g : Multiplicative (ZMod 2)} (hg : g.toAdd = 1) : sHom g = sr 0 := by
  show (if g.toAdd = 0 then (1 : DihedralGroup 4) else sr 0) = sr 0
  rw [hg, if_neg (by decide)]

/-! ## Compatibility — reduces to `reflection_conj_rotation'` -/

/-- The `SemidirectProduct.lift` compatibility hypothesis. On the identity it is
trivial; on the ℤ/2 generator it is exactly the already-proven inversion law
`reflection_conj_rotation'`. -/
theorem lift_compat (g : Multiplicative (ZMod 2)) :
    rHom.comp (φ g).toMonoidHom
      = (MulAut.conj (sHom g)).toMonoidHom.comp rHom := by
  ext n
  rcases zmod2_cases g.toAdd with hg | hg
  · -- generator trivial: φ g = 1, sHom g = 1
    simp [φ_zero hg, sHom_zero hg, MulAut.conj_apply]
  · -- generator nontrivial: φ g = invAut, sHom g = sr 0
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, φ_one hg, sHom_one hg,
      MulAut.conj_apply, invAut_apply]
    -- LHS rHom n⁻¹ = r ((n⁻¹).toAdd) = r (-(n.toAdd)) = (r n.toAdd)⁻¹
    -- RHS sr 0 * rHom n * (sr 0)⁻¹ = (r n.toAdd)⁻¹
    show r ((n⁻¹).toAdd) = sr 0 * r n.toAdd * (sr 0)⁻¹
    rw [toAdd_inv, ← inv_r, reflection_conj_rotation']

/-! ## Bijectivity of the lift -/

/-- `lift rHom sHom lift_compat ⟨n, g⟩ = rHom n * sHom g` (element form). -/
theorem lift_apply (x : SemidirectProduct (Multiplicative (ZMod 4))
    (Multiplicative (ZMod 2)) φ) :
    SemidirectProduct.lift rHom sHom lift_compat x = rHom x.left * sHom x.right := rfl

theorem lift_surjective :
    Function.Surjective (SemidirectProduct.lift rHom sHom lift_compat) := by
  intro y
  cases y with
  | r i =>
    refine ⟨inl (Multiplicative.ofAdd i), ?_⟩
    rw [lift_inl, rHom_ofAdd]
  | sr i =>
    refine ⟨⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd 1⟩, ?_⟩
    rw [lift_apply]
    show rHom (Multiplicative.ofAdd (-i)) * sHom (Multiplicative.ofAdd 1) = sr i
    rw [rHom_ofAdd, sHom_one (by simp), r_mul_sr]
    congr 1; ring

theorem lift_injective :
    Function.Injective (SemidirectProduct.lift rHom sHom lift_compat) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨n, g⟩ hx
  simp only [lift_apply] at hx
  rcases zmod2_cases g.toAdd with hg | hg
  · -- g.toAdd = 0: sHom g = 1, so r n.toAdd = 1 ⇒ n.toAdd = 0 ⇒ n = 1, g = 1.
    rw [sHom_zero hg, mul_one] at hx
    have h0 : r n.toAdd = r (0 : ZMod 4) := by rw [← one_def]; exact hx
    have hn1 : n = 1 := Multiplicative.toAdd.injective (by simpa using r.inj h0)
    have hg1 : g = 1 := Multiplicative.toAdd.injective (by simpa using hg)
    exact SemidirectProduct.ext hn1 hg1
  · -- g.toAdd = 1: sHom g = sr 0, so r n.toAdd * sr 0 = sr (0 - n.toAdd) = 1 — impossible.
    exfalso
    rw [sHom_one hg, r_mul_sr] at hx
    -- hx : sr (0 - n.toAdd) = 1; but sr _ = 1 = r 0 is false (distinct constructors).
    rw [one_def] at hx
    exact absurd hx (by simp)

/-! ## The external semidirect-product isomorphism -/

/-- **External semidirect-product packaging of `D₄`.**

`DihedralGroup 4` is isomorphic to `ℤ/4 ⋊ ℤ/2` with the ℤ/2 generator acting by
inversion of ℤ/4. -/
noncomputable def d4Equiv :
    SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) φ
      ≃* DihedralGroup 4 :=
  MulEquiv.ofBijective (SemidirectProduct.lift rHom sHom lift_compat)
    ⟨lift_injective, lift_surjective⟩

end InverseGaloisD4OQ01
