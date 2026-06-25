/-
Copyright (c) 2026 Lean Genius. All rights reserved.
Released under Apache 2.0 license.
Authors: Lean Genius Researcher

# Brouwer Degree via Mathlib Homology

This file develops the algebraic and functorial core of **Brouwer degree theory** and
instantiates it on Mathlib's genuine singular-homology functor
(`AlgebraicTopology.singularHomologyFunctor`, Andrew Yang, 2025).

## Mathematical background

For a continuous self-map `f : Sⁿ → Sⁿ` of the `n`-sphere, the *Brouwer degree* `deg f` is
the integer by which the induced endomorphism `f∗ : Hₙ(Sⁿ) → Hₙ(Sⁿ)` acts, after the canonical
identification `Hₙ(Sⁿ) ≅ ℤ`.  Its defining properties are

* `deg id = 1`,
* `deg (g ∘ f) = (deg g) · (deg f)` (functoriality / multiplicativity),
* a homeomorphism has degree `±1`,
* the degree does **not** depend on the chosen identification `Hₙ(Sⁿ) ≅ ℤ`.

These four facts are *purely formal* consequences of homology being a functor into abelian
groups together with `Hₙ(Sⁿ) ≅ ℤ`.  This file isolates that formal content and proves it in
full generality, with **0 sorries and 0 axioms** (only the standard `propext / Classical.choice
/ Quot.sound`).

## What is and is not assumed

Mathlib's singular homology (the only such theory currently in Mathlib) computes the homology of
totally disconnected spaces but does **not** yet provide the computation `Hₙ(Sⁿ) ≅ ℤ`, nor the
homotopy invariance and Eilenberg–Steenrod machinery needed to derive it.  Accordingly the
identification `Hₙ(X) ≃+ ℤ` enters here as an explicit **hypothesis** `e`, never as an axiom: the
theorems have the honest shape *"given the standard identification `Hₙ(X) ≃+ ℤ`, the degree is
well defined and functorial"*.  Supplying that identification for `X = Sⁿ` is the remaining
Mathlib-development gap (significance of this OQ), recorded in the gallery entry.

## Main definitions and results

* `degreeOfEnd e f` — the integer degree of an endomorphism `f : G →+ G` of an abelian group
  `G`, read through `e : G ≃+ ℤ`.
* `degreeOfEnd_conj` — the conjugate of `f` to `ℤ` is multiplication by `degreeOfEnd e f`.
* `degreeOfEnd_id`, `degreeOfEnd_comp` — identity and multiplicativity (functoriality).
* `degreeOfEnd_indep` — independence of the chosen identification `e`.
* `degreeOfEnd_equiv_isUnit`, `degreeOfEnd_equiv_eq` — an automorphism has degree a unit, i.e. `±1`.
* `functorDegree` — degree transported through an arbitrary functor `F : C ⥤ AddCommGrpCat`,
  with `functorDegree_id`, `functorDegree_comp`.
* `brouwerDegree` — `functorDegree` for the genuine Mathlib singular-homology functor, with
  `brouwerDegree_id`, `brouwerDegree_comp`, and `brouwerDegree_iso_eq` (homeomorphisms have
  degree `±1`).
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Tactic

open CategoryTheory AlgebraicTopology

namespace BrouwerDegree

/-! ## Section I — Algebraic core: degree of an endomorphism of a group `≅ ℤ` -/

variable {G : Type*} [AddCommGroup G]

/-- The **degree** of an endomorphism `f : G →+ G` of an abelian group `G`, read through a chosen
identification `e : G ≃+ ℤ`.  It is the integer `d` such that the conjugate `e ∘ f ∘ e⁻¹` of `f`
to `ℤ` is multiplication by `d`; concretely the image of the generator. -/
def degreeOfEnd (e : G ≃+ ℤ) (f : G →+ G) : ℤ := e (f (e.symm 1))

/-- The conjugate of `f` to `ℤ` is multiplication by `degreeOfEnd e f`:
`e (f (e⁻¹ n)) = (degreeOfEnd e f) · n`.  This is the characterising property of the degree. -/
theorem degreeOfEnd_conj (e : G ≃+ ℤ) (f : G →+ G) (n : ℤ) :
    e (f (e.symm n)) = degreeOfEnd e f * n := by
  -- The map `n ↦ e (f (e⁻¹ n))` is an additive hom `ℤ →+ ℤ`, hence multiplication by its value at 1.
  set c : ℤ →+ ℤ := (e.toAddMonoidHom.comp (f.comp e.symm.toAddMonoidHom)) with hc
  have hcn : c n = e (f (e.symm n)) := rfl
  have hc1 : c 1 = degreeOfEnd e f := rfl
  have key : c n = c 1 * n := by
    have := c.map_zsmul 1 n
    simpa [mul_comm] using this
  rw [hcn, hc1] at key
  simpa using key

@[simp] theorem degreeOfEnd_id (e : G ≃+ ℤ) : degreeOfEnd e (AddMonoidHom.id G) = 1 := by
  simp [degreeOfEnd]

/-- **Functoriality / multiplicativity** of the degree:
`deg (g ∘ f) = (deg g) · (deg f)`. -/
theorem degreeOfEnd_comp (e : G ≃+ ℤ) (g f : G →+ G) :
    degreeOfEnd e (g.comp f) = degreeOfEnd e g * degreeOfEnd e f := by
  have hf : f (e.symm 1) = e.symm (degreeOfEnd e f) := (e.symm_apply_apply _).symm
  unfold degreeOfEnd
  simp only [AddMonoidHom.comp_apply]
  rw [hf]
  -- now `e (g (e⁻¹ (deg f))) = deg g * deg f` is exactly the conjugation identity at `n = deg f`
  have := degreeOfEnd_conj e g (degreeOfEnd e f)
  simpa using this

/-- The degree does **not** depend on the chosen identification `e : G ≃+ ℤ`.  This is the
well-definedness of the Brouwer degree: any two identifications of `Hₙ` with `ℤ` give the same
integer. -/
theorem degreeOfEnd_indep (e₁ e₂ : G ≃+ ℤ) (f : G →+ G) :
    degreeOfEnd e₁ f = degreeOfEnd e₂ f := by
  -- Let `d := degreeOfEnd e₁ f` and `a := e₁ (e₂⁻¹ 1)`.
  set d : ℤ := degreeOfEnd e₁ f with hd
  set a : ℤ := e₁ (e₂.symm 1) with ha
  -- `e₂⁻¹ 1 = e₁⁻¹ a`, so `f (e₂⁻¹ 1) = f (e₁⁻¹ a)`.
  have h1 : e₂.symm 1 = e₁.symm a := by rw [ha, e₁.symm_apply_apply]
  -- Conjugation identity for `e₁` at `n = a`: `e₁ (f (e₁⁻¹ a)) = d * a`.
  have h2 : e₁ (f (e₁.symm a)) = d * a := by rw [hd]; exact degreeOfEnd_conj e₁ f a
  -- Hence `f (e₂⁻¹ 1) = e₁⁻¹ (d * a)`.
  have h3 : f (e₂.symm 1) = e₁.symm (d * a) := by
    have hrw : e₁.symm (d * a) = e₁.symm (e₁ (f (e₁.symm a))) := by rw [h2]
    rw [hrw, e₁.symm_apply_apply, h1]
  -- The additive hom `ψ := e₂ ∘ e₁⁻¹ : ℤ →+ ℤ` is `ℤ`-linear and sends `a ↦ 1`.
  set ψ : ℤ →+ ℤ := e₂.toAddMonoidHom.comp e₁.symm.toAddMonoidHom with hψ
  have hψa : ψ a = 1 := by
    simp only [hψ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, ha,
      e₁.symm_apply_apply, e₂.apply_symm_apply]
  have hlin : ψ (d * a) = d * ψ a := by
    have := ψ.map_zsmul a d
    simpa [smul_eq_mul] using this
  -- Conclude `degreeOfEnd e₂ f = d`.
  have : degreeOfEnd e₂ f = ψ (d * a) := by
    simp only [degreeOfEnd, h3, hψ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [this, hlin, hψa, mul_one]

/-- The degree of an **automorphism** `σ : G ≃+ G` is a unit of `ℤ` (it has a multiplicative
inverse, namely the degree of `σ⁻¹`). -/
theorem degreeOfEnd_equiv_isUnit (e : G ≃+ ℤ) (σ : G ≃+ G) :
    IsUnit (degreeOfEnd e σ.toAddMonoidHom) := by
  have h : degreeOfEnd e σ.toAddMonoidHom * degreeOfEnd e σ.symm.toAddMonoidHom = 1 := by
    rw [← degreeOfEnd_comp]
    have hcomp : σ.toAddMonoidHom.comp σ.symm.toAddMonoidHom = AddMonoidHom.id G := by
      ext x; simp
    rw [hcomp, degreeOfEnd_id]
  exact IsUnit.of_mul_eq_one _ h

/-- An automorphism has degree exactly `+1` or `-1`. -/
theorem degreeOfEnd_equiv_eq (e : G ≃+ ℤ) (σ : G ≃+ G) :
    degreeOfEnd e σ.toAddMonoidHom = 1 ∨ degreeOfEnd e σ.toAddMonoidHom = -1 :=
  Int.isUnit_iff.mp (degreeOfEnd_equiv_isUnit e σ)

/-! ## Section II — Functorial degree through a functor into abelian groups

The homology functor is, abstractly, a functor `F : C ⥤ AddCommGrpCat`.  The identity and
multiplicativity of the Brouwer degree are exactly the functor laws `F.map id = id` and
`F.map (f ≫ g) = F.map f ≫ F.map g` fed through Section I. -/

variable {C : Type*} [Category C]

/-- The degree of a self-morphism `f : X ⟶ X` transported through a functor `F` to abelian
groups, with respect to a chosen identification `e : F.obj X ≃+ ℤ`. -/
noncomputable def functorDegree (F : C ⥤ AddCommGrpCat) {X : C}
    (e : (F.obj X : Type) ≃+ ℤ) (f : X ⟶ X) : ℤ :=
  degreeOfEnd e (F.map f).hom

@[simp] theorem functorDegree_id (F : C ⥤ AddCommGrpCat) {X : C}
    (e : (F.obj X : Type) ≃+ ℤ) : functorDegree F e (𝟙 X) = 1 := by
  unfold functorDegree
  have : (F.map (𝟙 X)).hom = AddMonoidHom.id (F.obj X) := by
    rw [F.map_id]; ext x; simp
  rw [this, degreeOfEnd_id]

/-- **Functoriality of the Brouwer degree.**  Note the order: `f ≫ g` is "first `f`, then `g`",
matching the reversed composition of the induced abelian-group maps. -/
theorem functorDegree_comp (F : C ⥤ AddCommGrpCat) {X : C}
    (e : (F.obj X : Type) ≃+ ℤ) (f g : X ⟶ X) :
    functorDegree F e (f ≫ g) = functorDegree F e g * functorDegree F e f := by
  unfold functorDegree
  have : (F.map (f ≫ g)).hom = (F.map g).hom.comp (F.map f).hom := by
    rw [F.map_comp]; ext x; simp
  rw [this, degreeOfEnd_comp]

/-- An isomorphism (e.g. a homeomorphism after `F`) has degree `±1`. -/
theorem functorDegree_iso_eq (F : C ⥤ AddCommGrpCat) {X : C}
    (e : (F.obj X : Type) ≃+ ℤ) (σ : X ≅ X) :
    functorDegree F e σ.hom = 1 ∨ functorDegree F e σ.hom = -1 := by
  -- `F.mapIso σ` is an iso in `AddCommGrpCat`; turn it into an additive automorphism.
  have hσ : functorDegree F e σ.hom =
      degreeOfEnd e (F.mapIso σ).addCommGroupIsoToAddEquiv.toAddMonoidHom := by
    rfl
  rw [hσ]
  exact degreeOfEnd_equiv_eq e _

/-! ## Section III — Instantiation on Mathlib's singular homology functor

`singularHomologyFunctor AddCommGrpCat n` applied to the coefficient object `ℤ` is the genuine
`n`-th singular homology functor `Hₙ(-;ℤ) : TopCat ⥤ AddCommGrpCat`.  Feeding it to Section II
yields a Brouwer degree for continuous self-maps of any space whose `n`-th homology is identified
with `ℤ`. -/

/-- The `n`-th singular homology functor with integer coefficients,
`Hₙ(-;ℤ) : TopCat ⥤ AddCommGrpCat`. -/
noncomputable def Hn (n : ℕ) : TopCat ⥤ AddCommGrpCat :=
  (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)

/-- The **Brouwer degree** of a continuous self-map `f : X ⟶ X`, defined via Mathlib's singular
homology `Hₙ(X;ℤ)` and a chosen identification `e : Hₙ(X;ℤ) ≃+ ℤ` (the content of `Hₙ(Sⁿ) ≅ ℤ`
for `X = Sⁿ`). -/
noncomputable def brouwerDegree (n : ℕ) {X : TopCat}
    (e : ((Hn n).obj X : Type) ≃+ ℤ) (f : X ⟶ X) : ℤ :=
  functorDegree (Hn n) e f

/-- The identity map has Brouwer degree `1`. -/
@[simp] theorem brouwerDegree_id (n : ℕ) {X : TopCat} (e : ((Hn n).obj X : Type) ≃+ ℤ) :
    brouwerDegree n e (𝟙 X) = 1 :=
  functorDegree_id (Hn n) e

/-- **Multiplicativity of the Brouwer degree:** `deg (f ≫ g) = (deg g)·(deg f)`. -/
theorem brouwerDegree_comp (n : ℕ) {X : TopCat} (e : ((Hn n).obj X : Type) ≃+ ℤ)
    (f g : X ⟶ X) :
    brouwerDegree n e (f ≫ g) = brouwerDegree n e g * brouwerDegree n e f :=
  functorDegree_comp (Hn n) e f g

/-- A self-homeomorphism (iso in `TopCat`) has Brouwer degree `±1`. -/
theorem brouwerDegree_iso_eq (n : ℕ) {X : TopCat} (e : ((Hn n).obj X : Type) ≃+ ℤ)
    (σ : X ≅ X) :
    brouwerDegree n e σ.hom = 1 ∨ brouwerDegree n e σ.hom = -1 :=
  functorDegree_iso_eq (Hn n) e σ

/-- Convenience: the Brouwer degree of a continuous self-map `g : C(α, α)` of a topological
space `α`, packaged through `TopCat`. -/
noncomputable def brouwerDegreeCM (n : ℕ) {α : Type} [TopologicalSpace α]
    (e : ((Hn n).obj (TopCat.of α) : Type) ≃+ ℤ) (g : C(α, α)) : ℤ :=
  brouwerDegree n e (TopCat.ofHom g)

@[simp] theorem brouwerDegreeCM_id (n : ℕ) {α : Type} [TopologicalSpace α]
    (e : ((Hn n).obj (TopCat.of α) : Type) ≃+ ℤ) :
    brouwerDegreeCM n e (ContinuousMap.id α) = 1 := by
  unfold brouwerDegreeCM
  have : TopCat.ofHom (ContinuousMap.id α) = 𝟙 (TopCat.of α) := rfl
  rw [this, brouwerDegree_id]

end BrouwerDegree
