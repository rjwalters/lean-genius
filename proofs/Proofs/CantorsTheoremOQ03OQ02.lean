import Mathlib

/-
# OQ-03 → OQ-02: The Diagonal Argument for Higher-Order Types

Source: Lawvere (1969); follow-up to `CantorsTheoremOQ03` (verified, 0 axioms).

## The Open Question

The parent entry (OQ-03) organizes the diagonal argument into a hierarchy and
proves the **Level-1 Lawvere theorem**:

  > If `g : β → β` has no fixed point, then no `f : α → (α → β)` is surjective.

Its open question OQ-02 asks:

  > *Can the fixed-point-free characterization be extended to higher-order types
  >  — does the diagonal argument for `(α → β) → γ` require a different structural
  >  condition than `g : β → β` with no fixed point?*

## The Answer

**YES — it requires a strictly augmented condition.** When the codomain is the
*function* type `T = (α → β) → γ`, the relevant fixed-point-free endomorphism of
`T` is obtained by **post-composition** with a map on the *output* type `γ`:

  `postcomp g : T → T,   postcomp g h = g ∘ h`.

The exact characterization (Part II) is:

  `postcomp g` is fixed-point-free  ⟺  `Nonempty (α → β)`  ∧  `g` is fixed-point-free.

So compared with the base-type Level-1 condition "`g : γ → γ` has no fixed point",
the higher-order diagonal needs **one extra hypothesis**: the function *domain*
`α → β` must be inhabited. This inhabitation requirement is genuinely necessary —
Part IV exhibits the failure: when `α → β` is empty, `T` is a singleton, every
endomorphism of `T` has a fixed point, and the diagonal collapses.

Feeding this characterization into the Level-1 engine yields a **higher-order
Cantor / Lawvere theorem** (Part III): for an inhabited function domain and a
fixed-point-free `g : γ → γ`, no `f : ι → (ι → ((α → β) → γ))` is surjective.

## Results

Part I:   The Lawvere diagonal engine (self-contained, 1 theorem)
Part II:  Post-composition fixed-point-free characterization (core, 3 theorems)
Part III: Higher-order Cantor and Lawvere theorems (2 theorems)
Part IV:  Necessity of the inhabitation hypothesis (2 theorems)
Part V:   Concrete higher-order non-surjectivity instances (2 theorems)

Axioms: 0
Sorries: 0
-/

set_option linter.unusedVariables false

namespace CantorsTheoremOQ03OQ02

open Function

-- ============================================================
-- PART I: The Lawvere Diagonal Engine
-- ============================================================

/-- **Lawvere's fixed-point theorem (contrapositive form).** A fixed-point-free
endomorphism `g : β → β` obstructs surjectivity of any `f : α → (α → β)`.

This is the Level-1 engine; the higher-order results below feed specially
constructed fixed-point-free maps into it. -/
theorem lawvere {α β : Type*} (g : β → β) (hg : ∀ b, g b ≠ b)
    (f : α → α → β) : ¬ Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (fun x => g (f x x))
  -- `ha : f a = fun x => g (f x x)`, so `f a a = g (f a a)`: a fixed point of `g`.
  exact hg (f a a) (congrFun ha a).symm

-- ============================================================
-- PART II: Post-Composition Fixed-Point-Free Characterization
-- ============================================================

/-- Post-composition with `g : γ → γ` as an endomorphism of the function type
`X → γ`. This is the canonical lift of a map on the output type to a map on the
higher-order type. -/
def postcomp {X γ : Type*} (g : γ → γ) : (X → γ) → (X → γ) := fun h => g ∘ h

/-- **Core characterization.** Post-composition `postcomp g` on `X → γ` is
fixed-point-free **iff** the domain `X` is inhabited *and* `g` is fixed-point-free
on the output type `γ`.

The forward direction splits the single Level-1 condition into two: the
inhabitation of `X` is the genuinely new ingredient absent at the base level. -/
theorem postcomp_fixedPointFree_iff {X γ : Type*} (g : γ → γ) :
    (∀ h : X → γ, postcomp g h ≠ h) ↔ (Nonempty X ∧ ∀ c : γ, g c ≠ c) := by
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · -- If `X` were empty, the unique empty function would be a fixed point.
      by_contra hX
      have : IsEmpty X := not_nonempty_iff.mp hX
      exact H (fun x => isEmptyElim x) (funext fun x => isEmptyElim x)
    · -- A fixed point `c` of `g` makes the constant function `fun _ => c` fixed.
      intro c hc
      exact H (fun _ => c) (funext fun _ => hc)
  · rintro ⟨⟨x₀⟩, hg⟩ h hcon
    -- `hcon : g ∘ h = h`, evaluate at `x₀` to get a fixed point of `g`.
    exact hg (h x₀) (congrFun hcon x₀)

/-- The constructive payload of the backward direction, stated directly: from a
fixed-point-free `g` and an inhabited domain, `postcomp g` is fixed-point-free. -/
theorem postcomp_fixedPointFree {X γ : Type*} [Nonempty X] (g : γ → γ)
    (hg : ∀ c, g c ≠ c) : ∀ h : X → γ, postcomp g h ≠ h :=
  (postcomp_fixedPointFree_iff g).mpr ⟨‹Nonempty X›, hg⟩

/-- On an **empty** domain, post-composition can never be fixed-point-free: the
unique empty function is always a fixed point, regardless of `g`. This is the
structural obstruction that distinguishes higher-order from base-level diagonals. -/
theorem postcomp_has_fixedPoint_of_isEmpty {X γ : Type*} [IsEmpty X] (g : γ → γ) :
    ∃ h : X → γ, postcomp g h = h :=
  ⟨fun x => isEmptyElim x, funext fun x => isEmptyElim x⟩

-- ============================================================
-- PART III: Higher-Order Cantor / Lawvere
-- ============================================================

/-- **Higher-order Cantor theorem.** With an inhabited function domain `α → β`
and a fixed-point-free `g : γ → γ`, no `f : ι → (ι → ((α → β) → γ))` is
surjective. The diagonal now dodges in the *output* type `γ`, lifted to the
function type by `postcomp`. -/
theorem higher_order_cantor {ι α β γ : Type*}
    (hα : Nonempty (α → β)) (g : γ → γ) (hg : ∀ c, g c ≠ c)
    (f : ι → ι → ((α → β) → γ)) : ¬ Surjective f :=
  lawvere (postcomp g) ((postcomp_fixedPointFree_iff g).mpr ⟨hα, hg⟩) f

/-- **Higher-order Lawvere theorem (positive form).** Dually, a surjection
`f : ι → (ι → ((α → β) → γ))` forces **every** `g : γ → γ` to have a fixed point
(given the function domain is inhabited). -/
theorem higher_order_lawvere {ι α β γ : Type*}
    (hα : Nonempty (α → β)) (f : ι → ι → ((α → β) → γ))
    (hf : Surjective f) (g : γ → γ) : ∃ c, g c = c := by
  by_contra hcon
  push_neg at hcon
  exact higher_order_cantor hα g hcon f hf

-- ============================================================
-- PART IV: Necessity of the Inhabitation Hypothesis
-- ============================================================

/-- When the function domain `α → β` is **empty**, the higher-order codomain
`(α → β) → γ` is a subsingleton (all elements are equal). -/
theorem subsingleton_codomain_of_isEmpty {α β γ : Type*} [IsEmpty (α → β)] :
    Subsingleton ((α → β) → γ) :=
  ⟨fun h₁ h₂ => funext fun x => isEmptyElim x⟩

/-- **Necessity.** If the function domain `α → β` is empty (and the index type
`ι` is inhabited), a surjection `f : ι → (ι → ((α → β) → γ))` *does* exist — so
the higher-order diagonal genuinely fails without the inhabitation hypothesis.
This is the precise sense in which the structural condition must be augmented. -/
theorem surjection_exists_of_isEmpty_domain {ι α β γ : Type*}
    [IsEmpty (α → β)] [Nonempty ι] :
    ∃ f : ι → ι → ((α → β) → γ), Surjective f := by
  haveI : Subsingleton ((α → β) → γ) := subsingleton_codomain_of_isEmpty
  -- `ι → ((α→β)→γ)` is a subsingleton; pick any point as a constant surjection.
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨fun _ => fun _ => isEmptyElim, fun y => ⟨i₀, ?_⟩⟩
  exact Subsingleton.elim _ _

-- ============================================================
-- PART V: Concrete Higher-Order Instances
-- ============================================================

/-- Higher-order Cantor over `(ℕ → Bool) → Bool`: Boolean negation is the
fixed-point-free output map, and `ℕ → Bool` is inhabited (constants), so no
`f : ι → (ι → ((ℕ → Bool) → Bool))` is surjective. -/
theorem cantor_higherOrder_bool {ι : Type*}
    (f : ι → ι → ((ℕ → Bool) → Bool)) : ¬ Surjective f :=
  higher_order_cantor ⟨fun _ => true⟩ (fun b => !b) (fun b => by cases b <;> decide) f

/-- Higher-order Cantor over `(ℕ → Prop) → Prop`: propositional negation is the
fixed-point-free output map. This is a "second-order Cantor" — the powerset of a
powerset-valued function space resists enumeration. -/
theorem cantor_higherOrder_prop {ι : Type*}
    (f : ι → ι → ((ℕ → Prop) → Prop)) : ¬ Surjective f :=
  higher_order_cantor ⟨fun _ => True⟩ Not
    (fun p hp => by
      have h1 : ¬p → p := Eq.mp hp
      have h2 : p → ¬p := Eq.mp hp.symm
      have hnp : ¬p := fun h => h2 h h
      exact hnp (h1 hnp)) f

-- Axiom audit: confirm the headline higher-order theorems use no extra axioms.
#print axioms higher_order_cantor
#print axioms higher_order_lawvere
#print axioms postcomp_fixedPointFree_iff

end CantorsTheoremOQ03OQ02
