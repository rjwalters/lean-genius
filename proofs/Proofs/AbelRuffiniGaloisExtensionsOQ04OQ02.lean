import Mathlib

/-
# The Jordan–Hölder Theorem for Modules

The Abel–Ruffini family in this gallery repeatedly invokes the Jordan–Hölder
theorem for the *Galois group*: any two composition series of a finite group
have the same length and isomorphic composition factors, which is what makes
"solvability" a well-defined property independent of the chosen subnormal
series.  Exactly the same statement holds for **modules**, and that is what we
formalize here.

Mathlib proves the Jordan–Hölder theorem abstractly for any `JordanHolderLattice`
(`CompositionSeries.jordan_holder`, in `Mathlib/Order/JordanHolder.lean`) and
supplies the instance `JordanHolderLattice (Submodule R M)`
(`JordanHolderModule.instJordanHolderLattice`, in
`Mathlib/RingTheory/SimpleModule/Basic.lean`).  In that instance:

* the maximality relation `IsMaximal N N'` is the covering relation `N ⋖ N'`,
  equivalently "`N'/N` is a simple module";
* the isomorphism relation `Iso (A,B) (C,D)` is a linear equivalence of the
  successive quotients `B/A ≃ₗ[R] D/C` — i.e. equality of *composition factors*.

This file pulls those two pieces together to state the module-theoretic
Jordan–Hölder theorem, derives the well-definedness of composition length, and
specializes to simple modules (whose composition length is `1`).

The mathematical content is Mathlib's (Tier B): the deep induction is
`CompositionSeries.jordan_holder`.  Our contribution is the explicit
module-theoretic specialization and its consequences, which were not previously
present in the gallery.
-/

open CompositionSeries

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

namespace JordanHolderModuleGallery

/-- **Jordan–Hölder for modules.**  Two composition series of submodules of an
`R`-module `M` that share the same bottom term (`head`) and top term (`last`)
are *equivalent*: there is a bijection between their composition factors under
which corresponding factors are `R`-linearly isomorphic.

This is `CompositionSeries.jordan_holder` instantiated at the lattice
`Submodule R M`. -/
theorem jordanHolder_module (s₁ s₂ : CompositionSeries (Submodule R M))
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    s₁.Equivalent s₂ :=
  CompositionSeries.jordan_holder s₁ s₂ hb ht

/-- The **composition length** of a module is well defined: any two composition
series of `M` with the same endpoints have the same length.  This is the
invariance that lets one speak of *the* length of a module of finite length. -/
theorem compositionSeries_length_eq (s₁ s₂ : CompositionSeries (Submodule R M))
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    s₁.length = s₂.length :=
  (jordanHolder_module s₁ s₂ hb ht).length_eq

/-- Unpacking the conclusion: there is an explicit bijection `f` between the
factor indices of the two series such that, for every `i`, the `i`-th
composition factor of `s₁` is `JordanHolderLattice`-isomorphic to the `f i`-th
composition factor of `s₂`.  For `Submodule R M` this isomorphism is a linear
equivalence of the successive quotients. -/
theorem exists_factor_bijection (s₁ s₂ : CompositionSeries (Submodule R M))
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    ∃ f : Fin s₁.length ≃ Fin s₂.length, ∀ i : Fin s₁.length,
      JordanHolderLattice.Iso
        (s₁ (Fin.castSucc i), s₁ i.succ)
        (s₂ (Fin.castSucc (f i)), s₂ (Fin.succ (f i))) :=
  jordanHolder_module s₁ s₂ hb ht

/-- Equivalence of composition series is symmetric (inherited from the abstract
theory), so the roles of the two series may be exchanged. -/
theorem jordanHolder_module_symm (s₁ s₂ : CompositionSeries (Submodule R M))
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    s₂.Equivalent s₁ :=
  (jordanHolder_module s₁ s₂ hb ht).symm

/-! ### Specialization to simple modules

A nonzero module `M` is *simple* (`IsSimpleModule R M`) exactly when its only
submodules are `⊥` and `⊤`, i.e. `⊥ ⋖ ⊤`.  Then `[⊥, ⊤]` is a composition
series of length `1`, and Jordan–Hölder forces *every* composition series of `M`
to have length `1`. -/

/-- The canonical length-`1` composition series `⊥ ⋖ ⊤` of a simple module. -/
def simpleSeries (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : CompositionSeries (Submodule R M) where
  length := 1
  toFun := ![⊥, ⊤]
  step := by
    intro i
    fin_cases i
    show (⊥ : Submodule R M) ⋖ ⊤
    exact bot_covBy_top

@[simp] theorem simpleSeries_head [IsSimpleModule R M] :
    (simpleSeries R M).head = ⊥ := rfl

@[simp] theorem simpleSeries_last [IsSimpleModule R M] :
    (simpleSeries R M).last = ⊤ := rfl

@[simp] theorem simpleSeries_length [IsSimpleModule R M] :
    (simpleSeries R M).length = 1 := rfl

/-- **A simple module has composition length `1`.**  Every composition series of
a simple module `M` (running from `⊥` to `⊤`) has length exactly `1`. -/
theorem simpleModule_compositionSeries_length_eq_one [IsSimpleModule R M]
    (s : CompositionSeries (Submodule R M)) (hb : s.head = ⊥) (ht : s.last = ⊤) :
    s.length = 1 := by
  have h := compositionSeries_length_eq s (simpleSeries R M)
    (by rw [hb, simpleSeries_head]) (by rw [ht, simpleSeries_last])
  simpa using h

end JordanHolderModuleGallery
