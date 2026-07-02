/-
  Reflexive Objects and the Fixed-Point Property
  Open Question: cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01
  (an OQ extension of the completed categorical Lawvere theorem)

  ## Background

  The parent file CantorDiagonalizationOQ03OQ01Incomplete01.lean completes the
  categorical Lawvere fixed-point theorem: if `e : Pt A → Pt(B^A)` is point-
  surjective, then every endomorphism `f : Pt B → Pt B` has a fixed point.

  This file pursues a specialization the parent did not explore: **the diagonal
  case `B = A`**. An object `A` equipped with a point-surjection `e : A → (A → A)`
  is exactly a *reflexive object* — the categorical structure underlying every
  model of the untyped λ-calculus (a term `M` acts both as a function `e M` and
  as an argument, so `A` is "isomorphic to its own function space" at the level
  of points).

  ## Main results

  1. `reflexive_hasFixedPointProperty` — every reflexive object has the fixed-
     point property: *every* self-map `f : A → A` has a fixed point. (This is
     Lawvere with `B = A`, and it is precisely why an untyped λ-model interprets
     the `Y`-combinator: `Y f` is a fixed point of `f`.)

  2. `reflexive_subsingleton` — in **Set**, a reflexive object must be a
     subsingleton: no self-map can be fixed-point-free, but a two-element type
     always admits one (the "swap-to-`a`" map). Hence the only reflexive objects
     in Set are singletons.

  3. `reflexive_iff_subsingleton_nonempty` — the sharp characterization:
     `A` is reflexive ⟺ `A` is a nonempty subsingleton (a one-point type).

  This is the categorical reason the untyped λ-calculus has **no** set-theoretic
  model: one must pass to a category (Scott domains, complete lattices, ...) where
  "point-surjection" is weakened to a *retraction* `A ⟶ (A ⇒ A)` and the fixed-
  point argument no longer forces triviality.

  We also record the general Lawvere–Cantor obstruction (`B` with a fixed-point-
  free endo ⟹ no point-surjection `A → (A → B)`) and recover Cantor's theorem
  (`B = Prop`, `f = Not`) and Mathlib's `Function.cantor_surjective`.

  ## Axioms and Sorries

  0 sorries, 0 axioms (uses only `Classical` for a decidability instance inside a
  `by_cases`; no `axiom` declarations and no assumption-carrying structure fields).
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

namespace CantorDiagonalizationOQ03OQ01Incomplete01OQ01

-- ============================================================
-- SECTION I: The abstract Lawvere theorem (self-contained)
-- ============================================================

/-- An evaluation structure: codes `Ob`, values `Val`, and an evaluation map. -/
structure EvalStructure where
  Ob : Type*
  Val : Type*
  eval : Ob → Ob → Val

/-- Point-surjectivity: every function `Ob → Val` is represented by some code. -/
def EvalStructure.IsPointSurjective (E : EvalStructure) : Prop :=
  ∀ g : E.Ob → E.Val, ∃ a : E.Ob, ∀ x : E.Ob, E.eval a x = g x

/-- **Lawvere Fixed-Point Theorem (abstract)**: a point-surjective evaluation
    structure has the property that every endomorphism of its values has a fixed
    point. -/
theorem lawvere_abstract (E : EvalStructure) (hE : E.IsPointSurjective)
    (f : E.Val → E.Val) : ∃ v : E.Val, f v = v := by
  obtain ⟨a₀, ha₀⟩ := hE (fun a => f (E.eval a a))
  exact ⟨E.eval a₀ a₀, (ha₀ a₀).symm⟩

-- ============================================================
-- SECTION II: Reflexive objects and the fixed-point property
-- ============================================================

/-- The **fixed-point property**: every self-map of `A` has a fixed point. -/
def HasFixedPointProperty (A : Type*) : Prop :=
  ∀ f : A → A, ∃ a : A, f a = a

/-- `A` is a **reflexive object** (in Set) when some `e : A → (A → A)` is point-
    surjective: every self-map `g : A → A` equals `e a` for some `a`. This is the
    diagonal case `B = A` of the categorical Lawvere hypothesis, and the defining
    feature of a model of the untyped λ-calculus. -/
def IsReflexiveObject (A : Type*) : Prop :=
  ∃ e : A → (A → A), ∀ g : A → A, ∃ a : A, ∀ x : A, e a x = g x

/-- **Reflexive ⟹ fixed-point property.** Lawvere's theorem with `B = A`:
    if `A` is reflexive then *every* endomorphism `f : A → A` has a fixed point.
    In an untyped λ-model this is exactly the existence of the `Y`-combinator. -/
theorem reflexive_hasFixedPointProperty {A : Type*}
    (h : IsReflexiveObject A) : HasFixedPointProperty A := by
  obtain ⟨e, he⟩ := h
  intro f
  -- Package `e` into an evaluation structure with `Ob = Val = A`.
  let E : EvalStructure := { Ob := A, Val := A, eval := fun a x => e a x }
  have hE : E.IsPointSurjective := he
  exact lawvere_abstract E hE f

/-- Any type with two distinct elements admits a **fixed-point-free** self-map:
    the map sending `a ↦ b` and everything else `↦ a`. -/
theorem exists_fixedPointFree_of_ne {A : Type*} {a b : A} (hab : a ≠ b) :
    ∃ f : A → A, ∀ x : A, f x ≠ x := by
  classical
  refine ⟨fun x => if x = a then b else a, ?_⟩
  intro x
  by_cases hx : x = a
  · subst hx
    simpa using hab.symm
  · simp only [if_neg hx]
    exact fun h => hx h.symm

/-- **The fixed-point property forces a subsingleton** (in Set): if every self-map
    of `A` has a fixed point, then `A` has at most one element, because two distinct
    elements would furnish a fixed-point-free map. -/
theorem subsingleton_of_hasFixedPointProperty {A : Type*}
    (h : HasFixedPointProperty A) : Subsingleton A := by
  refine ⟨fun a b => ?_⟩
  by_contra hab
  obtain ⟨f, hf⟩ := exists_fixedPointFree_of_ne hab
  obtain ⟨a₀, ha₀⟩ := h f
  exact hf a₀ ha₀

/-- A reflexive object is nonempty (take `g = id`). -/
theorem nonempty_of_reflexive {A : Type*} (h : IsReflexiveObject A) :
    Nonempty A := by
  obtain ⟨e, he⟩ := h
  obtain ⟨a, _⟩ := he id
  exact ⟨a⟩

/-- **Main theorem: in Set, a reflexive object is a subsingleton.**
    Combining Lawvere (`reflexive ⟹ fixed-point property`) with the fact that
    only subsingletons have the fixed-point property. -/
theorem reflexive_subsingleton {A : Type*} (h : IsReflexiveObject A) :
    Subsingleton A :=
  subsingleton_of_hasFixedPointProperty (reflexive_hasFixedPointProperty h)

/-- **Converse: a one-point type is reflexive.** When `A` is a nonempty
    subsingleton, any `e` works, so `A` is reflexive. -/
theorem reflexive_of_subsingleton_nonempty {A : Type*}
    [Subsingleton A] [Nonempty A] : IsReflexiveObject A := by
  refine ⟨fun _ => id, ?_⟩
  intro g
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨a, fun x => Subsingleton.elim x (g x)⟩

/-- **Sharp characterization of reflexive objects in Set.**
    `A` is reflexive ⟺ `A` is a nonempty subsingleton (a one-point type).
    Equivalently: the terminal object is the only reflexive object of **Set**. -/
theorem reflexive_iff_subsingleton_nonempty {A : Type*} :
    IsReflexiveObject A ↔ (Subsingleton A ∧ Nonempty A) := by
  constructor
  · intro h
    exact ⟨reflexive_subsingleton h, nonempty_of_reflexive h⟩
  · rintro ⟨hs, hn⟩
    exact @reflexive_of_subsingleton_nonempty A hs hn

-- ============================================================
-- SECTION III: Concrete non-reflexive types
-- ============================================================

/-- `Bool` is not reflexive: it has two distinct elements. Concretely there is no
    point-surjection `Bool → (Bool → Bool)`, blocked by the fixed-point-free map
    `not`. -/
theorem not_reflexive_bool : ¬ IsReflexiveObject Bool := by
  intro h
  have hsub : Subsingleton Bool := reflexive_subsingleton h
  exact absurd (hsub.elim true false) (by decide)

/-- `ℕ` is not reflexive (blocked by the fixed-point-free successor map). -/
theorem not_reflexive_nat : ¬ IsReflexiveObject ℕ := by
  intro h
  have hsub : Subsingleton ℕ := reflexive_subsingleton h
  exact absurd (hsub.elim 0 1) (by decide)

-- ============================================================
-- SECTION IV: General Lawvere–Cantor obstruction & Cantor's theorem
-- ============================================================

/-- **Generalized Lawvere–Cantor obstruction.** If `B` admits a fixed-point-free
    self-map `f`, then no `e : A → (A → B)` is point-surjective. Cantor's theorem,
    Russell's paradox, Gödel incompleteness and the halting problem are all
    instances (varying `B` and `f`). The reflexive case is `B = A`. -/
theorem no_pointSurjection_of_fixedPointFree {A B : Type*}
    (f : B → B) (hf : ∀ b : B, f b ≠ b) (e : A → (A → B)) :
    ¬ ∀ g : A → B, ∃ a : A, ∀ x : A, e a x = g x := by
  intro he
  let E : EvalStructure := { Ob := A, Val := B, eval := fun a x => e a x }
  have hE : E.IsPointSurjective := he
  obtain ⟨v, hv⟩ := lawvere_abstract E hE f
  exact hf v hv

/-- **Cantor's theorem (point form).** No `e : A → (A → Prop)` is point-surjective;
    the obstruction is `Not : Prop → Prop`, which is fixed-point-free
    (`¬P = P` is impossible). -/
theorem cantor_no_surjection_prop {A : Type*} (e : A → (A → Prop)) :
    ¬ ∀ g : A → Prop, ∃ a : A, ∀ x : A, e a x = g x := by
  apply no_pointSurjection_of_fixedPointFree Not
  intro P h
  -- `h : (¬P) = P` gives both `P → ¬P` and `¬P → P`, hence a contradiction.
  have hpn : P → ¬P := cast h.symm
  have hnp : ¬P → P := cast h
  have np : ¬P := fun p => hpn p p
  exact np (hnp np)

/-- **Recovering Mathlib-style Cantor**: no `e : A → (A → Prop)` is surjective.
    Since `Set A` is definitionally `A → Prop`, this is `Function.cantor_surjective`. -/
theorem cantor_surjective_recovered {A : Type*} (e : A → (A → Prop)) :
    ¬ Function.Surjective e := by
  intro hsurj
  apply cantor_no_surjection_prop e
  intro g
  obtain ⟨a, ha⟩ := hsurj g
  exact ⟨a, fun x => congrFun ha x⟩

/-- Sanity check: our recovered statement matches Mathlib's `cantor_surjective`
    on power sets (`Set A = A → Prop`). -/
example {A : Type*} (f : A → Set A) : ¬ Function.Surjective f :=
  cantor_surjective_recovered f

-- ============================================================
-- Summary checks
-- ============================================================

#check @reflexive_hasFixedPointProperty
#check @reflexive_subsingleton
#check @reflexive_iff_subsingleton_nonempty
#check @not_reflexive_bool
#check @no_pointSurjection_of_fixedPointFree
#check @cantor_surjective_recovered

end CantorDiagonalizationOQ03OQ01Incomplete01OQ01
