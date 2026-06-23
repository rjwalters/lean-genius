import Proofs.InverseGaloisD4

/-
# Inverse Galois D₄ — OQ-01: The Semidirect-Product Structure ℤ/4 ⋊ ℤ/2

## Parent open question

The gallery entry `inverse-galois-d4` (file `InverseGaloisD4.lean`) proves

> `InverseGaloisExtensions.d4_realizable` : the splitting field of `X⁴ − 2`
> over `ℚ` is Galois with `|Gal| = 8`,

and remarks that this group "is the dihedral group `D₄`". The order alone
does **not** pin down the isomorphism type — there are two non-abelian
groups of order 8 (`D₄` and the quaternion group `Q₈`) and three abelian
ones. OQ-01 asks to make the *structure* `ℤ/4 ⋊ ℤ/2` explicit:

> a normal order-4 rotation subgroup and an order-2 reflection acting on
> it by inversion.

## What this file does

It establishes the explicit internal semidirect-product decomposition of
the abstract group `DihedralGroup 4` (Mathlib's `D₄`):

1. **Rotation subgroup `rotations ≅ ℤ/4`** — the image of the monoid
   homomorphism `rHom : Multiplicative (ZMod 4) →* DihedralGroup 4`,
   `i ↦ rᵢ`; injective, hence `rotations ≃* Multiplicative (ZMod 4)`
   (`rotationsEquiv`) and `Nat.card rotations = 4`.
2. **Normality** — `rotations.Normal`: conjugation by either a rotation
   or a reflection sends a rotation to a rotation.
3. **The inversion action** — `reflection_conj_rotation`:
   `sr j * rᵢ * (sr j)⁻¹ = r₍₋ᵢ₎`, and in particular
   `sr 0 * rᵢ * (sr 0)⁻¹ = rᵢ⁻¹`. This is the defining `ℤ/2`-twist.
4. **Order-2 reflection** — `orderOf (sr 0) = 2`.
5. **Complement `reflections ≅ ℤ/2`** — the order-2 subgroup `{1, sr 0}`,
   with `rotations ⊔ reflections = ⊤` and `rotations ⊓ reflections = ⊥`.
   Together with (2)–(3) this exhibits `D₄` as the internal semidirect
   product `rotations ⋊ reflections ≅ ℤ/4 ⋊ ℤ/2`.

### Scope honesty

This file works entirely inside the abstract group `DihedralGroup 4`. The
remaining (harder) step — an explicit `MulEquiv` between the concrete
Galois group `Gal(X⁴ − 2 / ℚ)` and `DihedralGroup 4`, i.e. identifying the
order-8 Galois group of `InverseGaloisD4.lean` *as* `D₄` — is the bridge
tracked in OQ-03 (it needs that `D₄` is the unique transitive subgroup of
`S₄` of order 8). The external `SemidirectProduct (Multiplicative (ZMod 4))
(Multiplicative (ZMod 2)) φ ≃* DihedralGroup 4` packaging is a natural next
iteration built on the data proved here.
-/

namespace InverseGaloisD4OQ01

open DihedralGroup

/-! ## The rotation subgroup `≅ ℤ/4` -/

/-- The rotation map `ℤ/4 → D₄`, `i ↦ rᵢ`, as a monoid homomorphism out of
the multiplicative form of `ℤ/4`. -/
def rHom : Multiplicative (ZMod 4) →* DihedralGroup 4 where
  toFun a := r a.toAdd
  map_one' := by simp
  map_mul' a b := by
    show r (a * b).toAdd = r a.toAdd * r b.toAdd
    rw [r_mul_r, toAdd_mul]

@[simp] theorem rHom_ofAdd (i : ZMod 4) : rHom (Multiplicative.ofAdd i) = r i := rfl

theorem rHom_injective : Function.Injective rHom := by
  intro a b h
  have h' : r a.toAdd = r b.toAdd := h
  exact Multiplicative.toAdd.injective (DihedralGroup.r.inj h')

/-- The subgroup of rotations of `D₄` — the image of `rHom`. -/
def rotations : Subgroup (DihedralGroup 4) := rHom.range

theorem mem_rotations {x : DihedralGroup 4} :
    x ∈ rotations ↔ ∃ i : ZMod 4, r i = x := by
  unfold rotations
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.toAdd, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd i, rfl⟩

/-- The rotation subgroup is cyclic of order 4: `rotations ≃* ℤ/4`. -/
noncomputable def rotationsEquiv : rotations ≃* Multiplicative (ZMod 4) :=
  (MonoidHom.ofInjective rHom_injective).symm

theorem card_rotations : Nat.card rotations = 4 := by
  rw [Nat.card_congr rotationsEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, ZMod.card]

/-! ## The inversion action (the `ℤ/2`-twist) -/

/-- Conjugation of a rotation by any reflection inverts the rotation:
`sr j * rᵢ * (sr j)⁻¹ = r₍₋ᵢ₎`. -/
theorem reflection_conj_rotation (i j : ZMod 4) :
    sr j * r i * (sr j)⁻¹ = r (-i) := by
  rw [inv_sr, sr_mul_r, sr_mul_sr]; congr 1; ring

/-- The reflection `sr 0` conjugates each rotation to its inverse — the
defining relation `s r s⁻¹ = r⁻¹` of the dihedral / semidirect structure. -/
theorem reflection_conj_rotation' (i : ZMod 4) :
    sr 0 * r i * (sr 0)⁻¹ = (r i)⁻¹ := by
  rw [inv_r]; exact reflection_conj_rotation i 0

/-! ## Element orders: rotation generator (4) and reflection (2) -/

theorem orderOf_rotation_gen : orderOf (r (1 : ZMod 4) : DihedralGroup 4) = 4 :=
  orderOf_r_one

theorem orderOf_reflection : orderOf (sr (0 : ZMod 4) : DihedralGroup 4) = 2 :=
  orderOf_sr 0

/-! ## Normality of the rotation subgroup -/

/-- The rotation subgroup is normal in `D₄`: conjugation by a rotation or a
reflection again yields a rotation. -/
theorem rotations_normal : rotations.Normal := by
  constructor
  intro n hn g
  obtain ⟨i, rfl⟩ := mem_rotations.mp hn
  cases g with
  | r j =>
    refine mem_rotations.mpr ⟨i, ?_⟩
    rw [inv_r, r_mul_r, r_mul_r]; congr 1; ring
  | sr j =>
    refine mem_rotations.mpr ⟨-i, ?_⟩
    rw [reflection_conj_rotation]

/-! ## The reflection complement `≅ ℤ/2` and the internal decomposition -/

/-- The order-2 subgroup generated by the reflection `sr 0`, namely
`{1, sr 0} ≅ ℤ/2`. -/
def reflections : Subgroup (DihedralGroup 4) where
  carrier := {1, sr 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [sr_mul_self]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl <;> simp

theorem mem_reflections {x : DihedralGroup 4} :
    x ∈ reflections ↔ x = 1 ∨ x = sr (0 : ZMod 4) := by
  show x ∈ ({1, sr 0} : Set (DihedralGroup 4)) ↔ _
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- `D₄` is generated by its rotations and the reflection: every element is
a rotation or a rotation times `sr 0`. -/
theorem rotations_sup_reflections : rotations ⊔ reflections = ⊤ := by
  rw [eq_top_iff]
  intro x _
  cases x with
  | r i => exact Subgroup.mem_sup_left (mem_rotations.mpr ⟨i, rfl⟩)
  | sr i =>
    have hx : sr i = r (-i) * sr (0 : ZMod 4) := by
      rw [r_mul_sr]; congr 1; ring
    rw [hx]
    exact Subgroup.mul_mem_sup (mem_rotations.mpr ⟨-i, rfl⟩)
      (mem_reflections.mpr (Or.inr rfl))

/-- The rotations and the reflection complement intersect trivially: the
only rotation that is also `1` or `sr 0` is `1`. -/
theorem rotations_inf_reflections : rotations ⊓ reflections = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx_rot, hx_ref⟩ := hx
  rw [mem_reflections] at hx_ref
  rcases hx_ref with rfl | rfl
  · rfl
  · obtain ⟨i, hi⟩ := mem_rotations.mp hx_rot
    simp at hi

/-- **Internal semidirect-product decomposition of `D₄`.**

The rotation subgroup `≅ ℤ/4` is normal, the reflection complement
`≅ ℤ/2` meets it trivially and together they generate `D₄`, and the
complement acts on the rotations by inversion. This is exactly the
statement that `D₄ ≅ ℤ/4 ⋊ ℤ/2` (with the inversion action). -/
theorem d4_internal_semidirect :
    rotations.Normal ∧ rotations ⊔ reflections = ⊤ ∧
      rotations ⊓ reflections = ⊥ ∧
      (∀ i : ZMod 4, sr 0 * r i * (sr 0)⁻¹ = (r i)⁻¹) :=
  ⟨rotations_normal, rotations_sup_reflections, rotations_inf_reflections,
    reflection_conj_rotation'⟩

/-
The abstract group `DihedralGroup 4` decomposed here is the group realized
as `Gal(ℚ(⁴√2, i)/ℚ)` by `InverseGaloisExtensions.d4_realizable` (order 8).
Identifying that concrete Galois group *with* `DihedralGroup 4` is the
harder bridge tracked by OQ-03.
-/

end InverseGaloisD4OQ01
