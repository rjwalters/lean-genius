import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.Tactic

/-
# Lawvere's Fixed-Point Theorem in a Cartesian Closed Category

## Open Question (cantor-diagonalization-oq-04-oq-01-oq-01)
"Can the setoid version be lifted to a proof using Mathlib's `CartesianClosed`
typeclass, working in any CCC with a terminal object?"

## Answer: YES.

This file proves **Lawvere's fixed-point theorem** at full categorical generality,
using Mathlib's `CartesianClosed` (= `MonoidalClosed` for a cartesian monoidal
category).  No `Type`-level surjections, no `Setoid` quotients: the argument lives
entirely in the category, with the terminal object `𝟙_ C` supplying "global
points" `𝟙_ C ⟶ X`.

### Statement

Let `C` be a cartesian closed category and `A B : C`.  A morphism
`φ : A ⟶ (A ⟹ B)` is **point-surjective** when every `f : A ⟶ B` is the *name* of
some global point of `A`: there is `a : 𝟙_ C ⟶ A` with `a ≫ φ = name f`, where
`name f := curry ((ρ_ A).hom ≫ f)` is the exponential transpose of `f`.

**Theorem (Lawvere).** If some `φ : A ⟶ (A ⟹ B)` is point-surjective, then every
endomorphism `t : B ⟶ B` has a fixed point: a global point `s : 𝟙_ C ⟶ B` with
`s ≫ t = s`.

### The diagonal argument (point-free)

Build the diagonal `f := Δ ≫ uncurry φ ≫ t : A ⟶ B`, where `Δ = lift (𝟙 A) (𝟙 A)`
is the categorical diagonal.  Point-surjectivity yields `a : 𝟙_ C ⟶ A` with
`a ≫ φ = name f`.  The fixed point is `s := a ≫ f`.  Two computations close it:

* **β-reduction** `lift a a ≫ uncurry φ = a ≫ f` — "evaluating `φ(a)` at `a` equals
  evaluating `f` at `a`", obtained from `a ≫ φ = name f` and the unit coherence
  `(ρ_ A).hom = fst _ _`.
* **diagonal unfolding** `a ≫ f = (lift a a ≫ uncurry φ) ≫ t` — pushing the point
  `a` through `Δ` via `comp_lift`.

Substituting one into the other gives `a ≫ f = (a ≫ f) ≫ t`, i.e. `s ≫ t = s`.

### Corollaries
* `lawvere_cantor` — contrapositive: if `t` has no fixed point, no `φ` is
  point-surjective (the abstract Cantor diagonal).
* In `Type u` this specializes to: no `f : A → (A → B)` is surjective when `B`
  carries a fixed-point-free endomorphism (e.g. `B = Bool`, `t = not`).

This strictly generalizes the parent `Setoid` proof (`CantorDiagonalizationOQ04OQ01`)
and the original `Type` diagonal (`CantorDiagonalization`).
-/

universe v u

namespace LawvereCCC

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.CartesianClosed

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [CartesianClosed C]
variable {A B : C}

/-- The *name* (exponential transpose) of a morphism `f : A ⟶ B`: the global point
`𝟙_ C ⟶ (A ⟹ B)` that internalizes `f`. -/
def name (f : A ⟶ B) : 𝟙_ C ⟶ (A ⟹ B) := curry ((ρ_ A).hom ≫ f)

@[simp] lemma name_def (f : A ⟶ B) : name f = curry ((ρ_ A).hom ≫ f) := rfl

/-- `φ : A ⟶ (A ⟹ B)` is *point-surjective* if every `f : A ⟶ B` is the name of a
global point of `A` factored through `φ`. -/
def PointSurjective (φ : A ⟶ (A ⟹ B)) : Prop :=
  ∀ f : A ⟶ B, ∃ a : 𝟙_ C ⟶ A, a ≫ φ = name f

/-- A global point `s : 𝟙_ C ⟶ B` is a fixed point of `t : B ⟶ B` if `s ≫ t = s`. -/
def IsFixedPoint (t : B ⟶ B) (s : 𝟙_ C ⟶ B) : Prop := s ≫ t = s

/-- **Lawvere's fixed-point theorem.**  If some `φ : A ⟶ (A ⟹ B)` is
point-surjective, then every endomorphism `t : B ⟶ B` admits a fixed point. -/
theorem lawvere_fixedPoint {φ : A ⟶ (A ⟹ B)} (hφ : PointSurjective φ)
    (t : B ⟶ B) : ∃ s : 𝟙_ C ⟶ B, IsFixedPoint t s := by
  -- The diagonal morphism `f a = t (φ(a)(a))`.
  set f : A ⟶ B := lift (𝟙 A) (𝟙 A) ≫ uncurry φ ≫ t with hf
  -- Point-surjectivity names the diagonal: `a ≫ φ = name f`.
  obtain ⟨a, ha⟩ := hφ f
  refine ⟨a ≫ f, ?_⟩
  -- (★) the uncurried form of the naming equation.
  have star : (A ◁ a) ≫ uncurry φ = (ρ_ A).hom ≫ f := by
    have h1 : uncurry (a ≫ φ) = (A ◁ a) ≫ uncurry φ := uncurry_natural_left a φ
    rw [ha, name_def, uncurry_curry] at h1
    exact h1.symm
  -- β-reduction: evaluating `φ(a)` at `a` is `a ≫ f`.
  have beta : lift a a ≫ uncurry φ = a ≫ f := by
    have e : lift a (𝟙 (𝟙_ C)) ≫ (A ◁ a) = lift a a := by
      rw [lift_whiskerLeft, Category.id_comp]
    calc lift a a ≫ uncurry φ
        = (lift a (𝟙 (𝟙_ C)) ≫ (A ◁ a)) ≫ uncurry φ := by rw [e]
      _ = lift a (𝟙 (𝟙_ C)) ≫ ((A ◁ a) ≫ uncurry φ) := by rw [Category.assoc]
      _ = lift a (𝟙 (𝟙_ C)) ≫ ((ρ_ A).hom ≫ f) := by rw [star]
      _ = (lift a (𝟙 (𝟙_ C)) ≫ (ρ_ A).hom) ≫ f := by rw [Category.assoc]
      _ = a ≫ f := by rw [rightUnitor_hom, lift_fst]
  -- Diagonal unfolding: push the point `a` through `Δ = lift (𝟙 A) (𝟙 A)`.
  have factI : a ≫ f = (lift a a ≫ uncurry φ) ≫ t := by
    rw [hf, ← Category.assoc a, comp_lift, Category.comp_id, Category.assoc]
  -- Combine: `a ≫ f = (a ≫ f) ≫ t`.
  rw [beta] at factI
  exact factI.symm

/-- **Abstract Cantor / Lawvere contrapositive.**  If `t : B ⟶ B` is fixed-point
free (no global point `s` with `s ≫ t = s`), then no `φ : A ⟶ (A ⟹ B)` can be
point-surjective. -/
theorem lawvere_cantor {t : B ⟶ B}
    (ht : ∀ s : 𝟙_ C ⟶ B, ¬ IsFixedPoint t s)
    (φ : A ⟶ (A ⟹ B)) : ¬ PointSurjective φ := by
  intro hφ
  obtain ⟨s, hs⟩ := lawvere_fixedPoint hφ t
  exact ht s hs

end LawvereCCC
