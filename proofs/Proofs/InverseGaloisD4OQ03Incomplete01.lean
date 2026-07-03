import Mathlib

/-
# OQ-03 (incomplete-01): A general dihedral **recognition** engine

## Parent open question

This file is a child iteration of `inverse-galois-d4-oq-03`
(parent gallery entry: `inverse-galois-d4`, which proves the specific case
`Gal(X⁴ − 2 / ℚ) ≅ D₄`):

> Is there a general criterion for when `Gal(X^n − a / ℚ)` is dihedral?

The parent's S4 iteration discharged the `(4, 2)` case by a **Sylow**
argument (`InverseGaloisD4OQ03.order_eight_iso_dihedralFour`: an order-`8`
subgroup of `S₄` is `D₄`, because `8 = 2³` is the full `2`-part of `|S₄|`).
That route is special to `n = 4`. The *general* Schinzel–Velez criterion
for arbitrary `(n, a)` is blocked upstream on **Capelli's irreducibility
theorem**, which is not in Mathlib `v4.26.0`.

## What this file contributes (a reusable, Capelli-free building block)

A prior S4 PREP Mathlib audit (recorded in the `inverse-galois-d4-oq-03`
tracker) found a concrete gap:

> `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` provides `DihedralGroup n`,
> its multiplication table, cardinality, and order witnesses — but **no**
> `DihedralGroup.lift` presentation-by-generators-and-relations constructor.
> For ANY Lean formalisation that needs `G ≃* DihedralGroup n` from a
> generator pair `(σ, τ)` with relations `σⁿ = 1`, `τ² = 1`, `τστ⁻¹ = σ⁻¹`,
> the `MulEquiv` must be hand-constructed. This is a recurring need in
> classical Galois formalisations.

This file fills exactly that gap, independently of any field theory:

1. **`liftHom`** — the canonical homomorphism `DihedralGroup n →* G`
   induced by generators `σ, τ : G` satisfying the dihedral relations
   `σⁿ = 1`, `τ² = 1`, `τσ = σ⁻¹τ`. It sends the abstract rotation `r 1`
   to `σ` and the abstract reflection `sr 0` to `τ`. The homomorphism
   property is proved from the relations (no `decide`, so it works for an
   arbitrary carrier `G`, not just `S₄`).

2. **`nonempty_mulEquiv_dihedralGroup`** — the **recognition theorem**:
   if in addition `σ, τ` generate `G` and `|G| = 2n` (`n ≥ 2`), then
   `G ≃* DihedralGroup n`. This is the general, `n`-uniform replacement for
   the parent's Sylow argument: instead of embedding into `Sₖ` and invoking
   Sylow, one exhibits two generators with the dihedral relations and matches
   orders. It is the group-theoretic core every dihedral-binomial case needs.

No `sorry`, no `axiom`, no `native_decide`. Only Mathlib group theory.

## References

* `Mathlib.GroupTheory.SpecificGroups.Dihedral` — `DihedralGroup n`, its
  multiplication simp lemmas (`r_mul_r`, `r_mul_sr`, `sr_mul_r`, `sr_mul_sr`),
  `DihedralGroup.card`, `nat_card`.
* Coxeter/Dyck presentation `⟨s, t ∣ sⁿ = t² = (st)² = 1⟩` of `Dₙ`.
* Parent: `Proofs.InverseGaloisD4OQ03` (the `n = 4` Sylow route).

Tags: galois-theory, inverse-galois-problem, dihedral-groups,
group-presentation, generators-and-relations
-/

namespace InverseGaloisD4OQ03Incomplete01

open DihedralGroup

variable {G : Type*} [Group G] {n : ℕ} {σ τ : G}

/-! ## Well-definedness of `σ`-powers modulo `n`

Because `σⁿ = 1`, the power `σ^k` depends only on `k mod n`. Packaging this as
an additive map `ZMod n → G`, `i ↦ σ^i.val`, is the rotation half of the
dihedral lift. -/

/-- `σ`-powers are periodic with period `n` once `σ ^ n = 1`. -/
theorem pow_mod (hσ : σ ^ n = 1) (k : ℕ) : σ ^ (k % n) = σ ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hσ, one_pow, one_mul]

/-- The rotation map `i ↦ σ^i.val` is additive: `σ^(i+j).val = σ^i.val * σ^j.val`. -/
theorem spow_add [NeZero n] (hσ : σ ^ n = 1) (i j : ZMod n) :
    σ ^ (i + j).val = σ ^ i.val * σ ^ j.val := by
  rw [ZMod.val_add, pow_mod hσ, pow_add]

/-- The rotation map sends negation to inversion:
`(σ^i.val)⁻¹ = σ^(-i).val`. -/
theorem spow_neg [NeZero n] (hσ : σ ^ n = 1) (i : ZMod n) :
    (σ ^ i.val)⁻¹ = σ ^ (-i).val :=
  inv_eq_of_mul_eq_one_right (by
    rw [← spow_add hσ i (-i), add_neg_cancel, ZMod.val_zero, pow_zero])

/-- The dihedral relation, iterated: `σ^m * τ = τ * (σ^m)⁻¹`.
This is the reflection–rotation commutation law used to prove `liftHom`
respects multiplication. -/
theorem sigma_pow_mul_tau (_hτ : τ ^ 2 = 1) (hrel : τ * σ = σ⁻¹ * τ) (m : ℕ) :
    σ ^ m * τ = τ * (σ ^ m)⁻¹ := by
  have hcomm : τ * σ ^ m = (σ ^ m)⁻¹ * τ := by
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hrel, ← mul_assoc, ← mul_inv_rev, ← pow_succ',
        pow_succ]
  have key : σ ^ m * τ * σ ^ m = τ := by
    rw [mul_assoc, hcomm, ← mul_assoc, mul_inv_cancel, one_mul]
  calc σ ^ m * τ = σ ^ m * τ * σ ^ m * (σ ^ m)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = τ * (σ ^ m)⁻¹ := by rw [key]

/-! ## The combination laws for reflections and rotations -/

/-- Rotation times reflection: `σ^i.val * (τ * σ^j.val) = τ * σ^(j - i).val`. -/
theorem rot_mul_refl [NeZero n] (hσ : σ ^ n = 1) (hτ : τ ^ 2 = 1)
    (hrel : τ * σ = σ⁻¹ * τ) (i j : ZMod n) :
    σ ^ i.val * (τ * σ ^ j.val) = τ * σ ^ (j - i).val := by
  rw [← mul_assoc, sigma_pow_mul_tau hτ hrel, mul_assoc, spow_neg hσ, ← spow_add hσ,
    neg_add_eq_sub]

/-- Reflection times reflection: `(τ * σ^i.val) * (τ * σ^j.val) = σ^(j - i).val`. -/
theorem refl_mul_refl [NeZero n] (hσ : σ ^ n = 1) (hτ : τ ^ 2 = 1)
    (hrel : τ * σ = σ⁻¹ * τ) (i j : ZMod n) :
    (τ * σ ^ i.val) * (τ * σ ^ j.val) = σ ^ (j - i).val := by
  rw [mul_assoc, rot_mul_refl hσ hτ hrel, ← mul_assoc, ← pow_two, hτ, one_mul]

/-! ## The dihedral lift -/

/-- The underlying map `DihedralGroup n → G`: rotation `r i ↦ σ^i.val`,
reflection `sr i ↦ τ * σ^i.val`. -/
def liftFun (σ τ : G) : DihedralGroup n → G
  | .r i => σ ^ i.val
  | .sr i => τ * σ ^ i.val

/-- **Dihedral lift** (the missing `DihedralGroup.lift`).
A group `G` with elements `σ, τ` satisfying the dihedral relations
`σⁿ = 1`, `τ² = 1`, `τσ = σ⁻¹τ` receives a canonical group homomorphism
`DihedralGroup n →* G` sending the abstract rotation `r 1` to `σ` and the
abstract reflection `sr 0` to `τ`.

The homomorphism law is proved purely from the relations, so it applies to
*any* carrier `G` — it is not a finite `decide`. -/
def liftHom [NeZero n] (hσ : σ ^ n = 1) (hτ : τ ^ 2 = 1)
    (hrel : τ * σ = σ⁻¹ * τ) : DihedralGroup n →* G where
  toFun := liftFun σ τ
  map_one' := by
    rw [DihedralGroup.one_def]
    show σ ^ (0 : ZMod n).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · show liftFun σ τ (r i * r j) = σ ^ i.val * σ ^ j.val
      rw [r_mul_r]; exact spow_add hσ i j
    · show liftFun σ τ (r i * sr j) = σ ^ i.val * (τ * σ ^ j.val)
      rw [r_mul_sr]; exact (rot_mul_refl hσ hτ hrel i j).symm
    · show liftFun σ τ (sr i * r j) = (τ * σ ^ i.val) * σ ^ j.val
      rw [sr_mul_r]
      show τ * σ ^ (i + j).val = τ * σ ^ i.val * σ ^ j.val
      rw [mul_assoc, ← spow_add hσ]
    · show liftFun σ τ (sr i * sr j) = (τ * σ ^ i.val) * (τ * σ ^ j.val)
      rw [sr_mul_sr]; exact (refl_mul_refl hσ hτ hrel i j).symm

@[simp] theorem liftHom_r_one [NeZero n] [Fact (1 < n)] (hσ : σ ^ n = 1)
    (hτ : τ ^ 2 = 1) (hrel : τ * σ = σ⁻¹ * τ) :
    liftHom hσ hτ hrel (r 1) = σ := by
  show σ ^ (1 : ZMod n).val = σ
  rw [ZMod.val_one, pow_one]

@[simp] theorem liftHom_sr_zero [NeZero n] (hσ : σ ^ n = 1)
    (hτ : τ ^ 2 = 1) (hrel : τ * σ = σ⁻¹ * τ) :
    liftHom hσ hτ hrel (sr 0) = τ := by
  show τ * σ ^ (0 : ZMod n).val = τ
  rw [ZMod.val_zero, pow_zero, mul_one]

/-- **Dihedral recognition theorem.**
If a finite group `G` is generated by two elements `σ, τ` satisfying the
dihedral relations `σⁿ = 1`, `τ² = 1`, `τσ = σ⁻¹τ`, and `|G| = 2n` with
`n ≥ 2`, then `G ≃* DihedralGroup n`.

This is the general (`n`-uniform) group-theoretic core of the dihedral
binomial problem: it replaces the parent's `n = 4`-specific Sylow argument
(`order_eight_iso_dihedralFour`) with a generators-and-relations criterion
valid for every `n`. Once a Galois group `Gal(X^n − a / ℚ)` is exhibited
with such generators and the right order, this theorem identifies it as
`Dₙ` with no further work. -/
theorem nonempty_mulEquiv_dihedralGroup [Finite G] (hn : 2 ≤ n)
    (hσ : σ ^ n = 1) (hτ : τ ^ 2 = 1) (hrel : τ * σ = σ⁻¹ * τ)
    (hgen : Subgroup.closure ({σ, τ} : Set G) = ⊤)
    (hcard : Nat.card G = 2 * n) :
    Nonempty (G ≃* DihedralGroup n) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  set f : DihedralGroup n →* G := liftHom hσ hτ hrel with hf
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact MonoidHom.mem_range.mpr ⟨r 1, by rw [hf, liftHom_r_one]⟩
    · exact MonoidHom.mem_range.mpr ⟨sr 0, by rw [hf, liftHom_sr_zero]⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hcardeq : Fintype.card (DihedralGroup n) = Fintype.card G := by
    rw [DihedralGroup.card, ← Nat.card_eq_fintype_card, hcard]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcardeq⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end InverseGaloisD4OQ03Incomplete01
