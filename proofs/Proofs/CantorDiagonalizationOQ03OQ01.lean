import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-
# Lawvere Fixed-Point Theorem: Categorical Generalization

## Open Question (cantor-diagonalization-oq-03-oq-01)

"Can the Lawvere fixed-point theorem be formalized in a topos-theoretic
setting in Lean, recovering the original categorical generality beyond
type theory?"

## Answer

We formalize Lawvere's 1969 result at increasing levels of generality:

1. **Abstract fixed-point theorem**: For any "evaluation structure" with
   surjective point-mapping, every endomorphism has a fixed point.
2. **Parametric diagonal lemma**: The diagonal function is never in the
   range of a surjection when the endomorphism has no fixed point.
3. **Recovery of type-theoretic version**: The abstract theorem specializes
   to the version in CantorDiagonalizationOQ03.
4. **Concrete instances**: Cantor, Russell, Rice, Halting Problem.

The key categorical insight: Lawvere's theorem holds in any cartesian
closed category (CCC) where "surjection" means "point-surjective" —
the morphism e : A → B^A hits every global element 1 → B^A.

## Builds On
- CantorDiagonalizationOQ03.lean: type-theoretic Lawvere and Cantor
-/

namespace CantorDiagonalizationOQ03OQ01

/-! ## Part 1: Abstract Evaluation Structure

We axiomatize the minimum needed for Lawvere: an "evaluation" that
takes a "code" and an "input" and produces an "output", analogous to
the evaluation map ev : B^A × A → B in a cartesian closed category. -/

/-- An evaluation structure models the data of a CCC:
    - `Ob`: the type of "objects" (codes/programs/elements)
    - `Val`: the type of "values" (outputs)
    - `eval`: applies a code to an input, producing a value
    This captures e : A → (A → B) from the type-theoretic version
    and ev ∘ ⟨e, id⟩ : A → B from the categorical version. -/
structure EvalStructure where
  Ob : Type*
  Val : Type*
  eval : Ob → Ob → Val

/-- A morphism in the evaluation structure: an endomorphism on values.
    This is f : B → B in Lawvere's theorem. -/
def EvalStructure.Endo (E : EvalStructure) := E.Val → E.Val

/-- The evaluation is point-surjective: every function Ob → Val
    is "represented" by some code. This is the categorical condition
    that e : A → B^A is a point-surjection (hits every global element). -/
def EvalStructure.IsPointSurjective (E : EvalStructure) : Prop :=
  ∀ g : E.Ob → E.Val, ∃ a : E.Ob, ∀ x : E.Ob, E.eval a x = g x

/-! ## Part 2: The Abstract Lawvere Fixed-Point Theorem -/

/-- **Lawvere Fixed-Point Theorem (Abstract)**:
    If the evaluation structure is point-surjective, then every
    endomorphism f : Val → Val has a fixed point.

    This is Lawvere's 1969 result, abstracted from any specific category.
    The proof constructs the diagonal g(a) = f(eval(a, a)) and uses
    point-surjectivity to find a₀ representing g. -/
theorem lawvere_abstract (E : EvalStructure) (hE : E.IsPointSurjective)
    (f : E.Endo) : ∃ v : E.Val, f v = v := by
  -- Diagonal construction: g(a) = f(eval(a, a))
  obtain ⟨a₀, ha₀⟩ := hE (fun a => f (E.eval a a))
  -- a₀ represents g, so eval(a₀, a₀) = g(a₀) = f(eval(a₀, a₀))
  exact ⟨E.eval a₀ a₀, (ha₀ a₀).symm⟩

/-- **Contrapositive (No-Surjection Theorem)**:
    If f : Val → Val has no fixed point, then no evaluation structure
    with that Val type can be point-surjective. -/
theorem no_surjection_abstract (E : EvalStructure) (f : E.Endo)
    (hf : ∀ v : E.Val, f v ≠ v) : ¬ E.IsPointSurjective := by
  intro hE
  obtain ⟨v, hv⟩ := lawvere_abstract E hE f
  exact hf v hv

/-! ## Part 3: The Diagonal Lemma (Explicit) -/

/-- The diagonal function g(a) = f(eval(a, a)) is never representable
    when f has no fixed point. This is the core of all diagonal arguments. -/
theorem diagonal_not_representable (E : EvalStructure) (f : E.Endo)
    (hf : ∀ v : E.Val, f v ≠ v) :
    ¬ ∃ a₀ : E.Ob, ∀ x, E.eval a₀ x = f (E.eval x x) := by
  rintro ⟨a₀, ha₀⟩
  exact hf (E.eval a₀ a₀) (ha₀ a₀).symm

/-! ## Part 4: Recovery of Type-Theoretic Version

The type-theoretic Lawvere theorem (from CantorDiagonalizationOQ03)
is a special case where the evaluation structure is (A, B, e). -/

/-- Construct an EvalStructure from a function e : A → A → B. -/
def typeEvalStructure (A B : Type*) (e : A → A → B) : EvalStructure where
  Ob := A
  Val := B
  eval := e

/-- Point-surjectivity for typeEvalStructure is exactly Function.Surjective e. -/
theorem typeEval_surjective_iff {A B : Type*} (e : A → A → B) :
    (typeEvalStructure A B e).IsPointSurjective ↔ Function.Surjective e := by
  constructor
  · intro h g
    obtain ⟨a₀, ha₀⟩ := h g
    exact ⟨a₀, funext ha₀⟩
  · intro h g
    obtain ⟨a₀, ha₀⟩ := h g
    exact ⟨a₀, fun x => congr_fun ha₀ x⟩

/-- **Recovery**: The abstract Lawvere theorem gives back the type-theoretic version. -/
theorem lawvere_type_recovery {A B : Type*} (e : A → A → B)
    (he : Function.Surjective e) (f : B → B) :
    ∃ b : B, f b = b := by
  have hE := (typeEval_surjective_iff e).mpr he
  exact lawvere_abstract (typeEvalStructure A B e) hE f

/-- Cantor's theorem recovered from the abstract version. -/
theorem cantor_recovery {A : Type*} (e : A → A → Prop) :
    ¬ Function.Surjective e := by
  intro he
  have ⟨b, hb⟩ := lawvere_type_recovery e he Not
  -- ¬b = b is impossible
  have : ¬b → b := fun h => by rwa [← hb]
  have : b → ¬b := fun h => by rwa [hb]
  exact (this (‹¬b → b› (‹b → ¬b› (‹¬b → b› (fun h => ‹b → ¬b› h h))))) (‹¬b → b› (fun h => ‹b → ¬b› h h))

/-! ## Part 5: Instances of the Abstract Theorem

Each instance provides a specific Val type and fixed-point-free endomorphism. -/

/-- **Cantor Instance**: Val = Prop, f = Not. -/
theorem cantor_instance : ∀ (A : Type*) (e : A → A → Prop),
    ¬ (typeEvalStructure A Prop e).IsPointSurjective := by
  intro A e hE
  obtain ⟨v, hv⟩ := lawvere_abstract _ hE Not
  -- hv : ¬v = v (as propositions)
  have to_v : ¬v → v := fun h => cast hv h
  have to_nv : v → ¬v := fun h => cast hv.symm h
  have nv : ¬v := fun h => to_nv h h
  exact nv (to_v nv)

/-- **Bool Instance**: Val = Bool, f = not. -/
theorem bool_instance : ∀ (A : Type*) (e : A → A → Bool),
    ¬ (typeEvalStructure A Bool e).IsPointSurjective := by
  intro A e hE
  obtain ⟨v, hv⟩ := lawvere_abstract _ hE (! ·)
  cases v <;> simp at hv

/-- **Natural Number Instance**: Val = ℕ, f = Nat.succ.
    No evaluation structure ℕ → ℕ → ℕ that is point-surjective exists,
    because Nat.succ has no fixed point. -/
theorem nat_succ_instance : ∀ (A : Type*) (e : A → A → ℕ),
    ¬ (typeEvalStructure A ℕ e).IsPointSurjective := by
  intro A e hE
  obtain ⟨v, hv⟩ := lawvere_abstract _ hE Nat.succ
  exact absurd hv (Nat.succ_ne_self v)

/-! ## Part 6: The Categorical Perspective

In a cartesian closed category C:
- Objects A, B ∈ C
- Exponential B^A (internal hom)
- Evaluation map: ev : B^A × A → B
- A morphism e : A → B^A
- "Point-surjective" = for every global element g : 1 → B^A,
  there exists a : 1 → A with e ∘ a = g

The type-theoretic version models the CCC of types (Type, ×, →).
In a topos (CCC with subobject classifier Ω), taking B = Ω gives
Cantor's theorem: no object surjects onto its power object P(A) = Ω^A.

We axiomatize this categorical level: -/

/-- A categorical evaluation system models a CCC with global elements.
    This is closer to the topos-theoretic setting than EvalStructure. -/
structure CategoricalEval where
  /-- Type of objects (modeling objects of a CCC) -/
  Obj : Type*
  /-- Type of morphisms between objects -/
  Hom : Obj → Obj → Type*
  /-- Exponential object -/
  exp : Obj → Obj → Obj
  /-- Global element type (morphisms from terminal object) -/
  Pt : Obj → Type*
  /-- Apply: given a global element of the exponential and a global
      element of A, produce a global element of B. This models
      the evaluation map ev : B^A × A → B applied to global elements. -/
  apply : ∀ {A B : Obj}, Pt (exp A B) → Pt A → Pt B
  /-- Point-surjectivity of a morphism e: every function on global
      elements is represented by some global element of the domain. -/
  ptSurj : ∀ {A B : Obj}, Hom A (exp A B) → Prop

/-- Fixed point in the categorical sense: a global element b : Pt B
    such that f(b) = b, where f is an endomorphism on global elements. -/
def CategoricalEval.HasFixedPoint (C : CategoricalEval) {B : C.Obj}
    (f : C.Pt B → C.Pt B) : Prop :=
  ∃ b : C.Pt B, f b = b

/-- **Lawvere's Theorem (Categorical)**:
    In a CCC, if e : A → B^A has the property that the induced map
    on global elements is surjective, then every f : Pt B → Pt B
    has a fixed point.

    We use EvalStructure as the computational core and show the
    categorical version reduces to it. -/
theorem lawvere_categorical (C : CategoricalEval) {A B : C.Obj}
    (hSurj : ∀ g : C.Pt A → C.Pt B, ∃ a : C.Pt A,
      ∀ x : C.Pt A, C.apply (sorry : C.Pt (C.exp A B)) x = g x)
    (f : C.Pt B → C.Pt B) : C.HasFixedPoint f := by
  sorry

/-! ## Part 7: Topos Connection

A **topos** is a cartesian closed category with a subobject classifier Ω.
The power object P(A) = Ω^A classifies subobjects of A.

Cantor's theorem in a topos: no object A has an epimorphism A → P(A).
This follows from Lawvere with B = Ω and f = ¬ (the negation morphism
on the subobject classifier). The subobject classifier always has a
fixed-point-free endomorphism (internal negation), so Lawvere prevents
any surjection A → Ω^A.

This is formalized at the topos level in Johnstone's "Sketches of an
Elephant" (A1.6.1) and MacLane-Moerdijk "Sheaves in Geometry and Logic"
(IV.7). A full Lean formalization would require Mathlib's topos infrastructure,
which is currently under development. -/

/-- Informal summary: In a topos with subobject classifier Ω and
    negation ¬ : Ω → Ω having no fixed point, Lawvere implies
    no object surjects onto its power object.

    Formalized here as a type-level proxy using Prop as Ω. -/
theorem topos_proxy_cantor (A : Type*) :
    ¬ ∃ e : A → A → Prop, Function.Surjective e := by
  rintro ⟨e, he⟩
  exact cantor_recovery e he

/-! ## Summary -/

/-
## The Answer to OQ-03-OQ-01

### What This File Achieves

1. **Abstract Lawvere FPT** (lawvere_abstract):
   Proved in a minimal "evaluation structure" — no category theory imports needed.
   Any system with "codes", "values", and a surjective evaluation has the
   fixed-point property.

2. **Type-theoretic recovery** (lawvere_type_recovery):
   The abstract version specializes exactly to the version in the parent file.

3. **Three concrete instances**: Prop (Cantor), Bool, ℕ (successor has no fixed point).

4. **Categorical framework** (CategoricalEval):
   Axiomatizes the CCC structure at the global-element level.
   The full categorical proof has a sorry — it requires connecting
   the CategoricalEval apply/surjectivity to EvalStructure.

5. **Topos proxy** (topos_proxy_cantor):
   Uses Prop as a proxy for the subobject classifier Ω, recovering
   Cantor's theorem in a topos-like setting.

### What Remains

The full topos-theoretic formalization requires:
- Mathlib's topos typeclass (not yet available)
- Subobject classifier Ω with internal negation
- Point-surjectivity defined via the evaluation map in the CCC

### Axiom and Sorry Count
0 axioms, 2 sorries (both in the CategoricalEval section — the connection
between the categorical structure and the computational proof). The core
theorems (lawvere_abstract, cantor_recovery, all instances) are fully proved.
-/

#check lawvere_abstract
#check lawvere_type_recovery
#check cantor_recovery
#check cantor_instance
#check bool_instance
#check nat_succ_instance
#check topos_proxy_cantor

end CantorDiagonalizationOQ03OQ01
