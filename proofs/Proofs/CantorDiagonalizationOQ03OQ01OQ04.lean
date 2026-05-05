/-
# Constructive Cantor Diagonal: Without Propositional Extensionality

## Open Question (cantor-diagonalization-oq-03-oq-01-oq-04)

"Prove the constructive analogue without classical logic: propositional
extensionality is used in `cantor_recovery`; can the theorem be restated
using explicit witnesses instead?"

## Answer: Yes.

The standard `cantor_recovery` theorem (in CantorDiagonalizationOQ03OQ01)
requires propositional extensionality (`propext`) because it relies on
`Function.Surjective e`, which means `∀ P : A → Prop, ∃ a, e a = P`.
The equation `e a = P` is a function equality, and rewriting along it
(via `rwa [← hb]`) implicitly invokes `propext`.

The constructive reformulation replaces function equality with pointwise Iff:

  **Classical (with propext)**:   ∀ P : A → Prop, ∃ a, e a = P
  **Constructive (no propext)**:  ∀ P : A → Prop, ∃ a, ∀ x, e a x ↔ P x

The pointwise Iff form is strictly weaker: it follows from function equality
(via `iff_of_eq ∘ congr_fun`), but does not require propext to USE for
contradiction. This gives a proof-theoretically clean diagonal argument.

## Key Insight

In the constructive proof, the diagonal fixed-point equation becomes:
  `hdd : e d d ↔ ¬(e d d)`
which is directly contradictory (no `propext` needed — `iff_not_self`).

In contrast, the classical proof derives `hb : ¬b = b` (Prop equality),
then `rwa [← hb]` implicitly coerces through `propext` to use `hb` as an Iff.

## Status: 0 sorries, 0 axioms (constructive!)
-/

import Proofs.CantorDiagonalizationOQ03OQ01
import Mathlib.Tactic

namespace CantorDiagonalizationOQ03OQ01OQ04

open CantorDiagonalizationOQ03OQ01

-- ===========================================================================
-- PART I: THE CONSTRUCTIVE SURJECTIVITY CONDITION
-- ===========================================================================

/-- The **constructive surjectivity** condition for e : A → A → Prop.

    Unlike `Function.Surjective e` (which requires propext to use in proofs),
    this version only requires pointwise logical equivalence, making it valid
    in constructive logic. -/
def IsPointwiseSurjective {A : Type*} (e : A → A → Prop) : Prop :=
  ∀ P : A → Prop, ∃ a : A, ∀ x : A, e a x ↔ P x

/-- Classical surjectivity (function equality) implies constructive surjectivity
    (pointwise Iff). The converse fails in general: e a = P requires propext
    to prove from ∀ x, e a x ↔ P x. -/
theorem surjective_implies_pointwise {A : Type*} (e : A → A → Prop)
    (he : Function.Surjective e) : IsPointwiseSurjective e := by
  intro P
  obtain ⟨a, ha⟩ := he P
  exact ⟨a, fun x => iff_of_eq (congr_fun ha x)⟩

-- ===========================================================================
-- PART II: CONSTRUCTIVE CANTOR DIAGONAL (NO PROPEXT)
-- ===========================================================================

/-- **Constructive Cantor Diagonal Theorem** (OQ-04 answer):

    If e : A → A → Prop is constructively surjective (pointwise Iff witnesses),
    then we derive a contradiction using only intuitionistic logic.

    **Proof structure**:
    1. Apply surjectivity to the diagonal predicate D(a) = ¬(e a a)
    2. Get d : A with: ∀ x, e d x ↔ ¬(e x x)
    3. Specialize to x = d: e d d ↔ ¬(e d d)
    4. Direct contradiction from iff_not_self

    **No axioms used** — this is valid in pure constructive type theory.
    The contradiction is `iff_not_self : ¬(p ↔ ¬p)` applied to `e d d`. -/
theorem cantor_constructive {A : Type*} (e : A → A → Prop)
    (he : IsPointwiseSurjective e) : False := by
  -- Step 1: Apply to the diagonal predicate D(a) = ¬(e a a)
  obtain ⟨d, hd⟩ := he (fun a => ¬e a a)
  -- Step 2: Specialize to x = d to get the self-referential Iff
  have hdd : e d d ↔ ¬e d d := hd d
  -- Step 3: Direct contradiction — iff_not_self : ¬(p ↔ ¬p)
  exact iff_not_self hdd

/-- **Cantor No-Surjection (Constructive)**:

    No function e : A → A → Prop is constructively surjective.
    This is the "no-surjection" form of the constructive Cantor theorem. -/
theorem cantor_no_pointwise_surjection {A : Type*} (e : A → A → Prop) :
    ¬IsPointwiseSurjective e :=
  fun he => cantor_constructive e he

/-- Corollary: Cantor's classical theorem follows from the constructive one.

    `cantor_recovery` (from the parent file) is implied by our stronger
    constructive result, since classical surjectivity implies pointwise
    surjectivity. This confirms our theorem is a genuine strengthening. -/
theorem cantor_recovery_from_constructive {A : Type*} (e : A → A → Prop) :
    ¬Function.Surjective e := by
  intro he
  exact cantor_constructive e (surjective_implies_pointwise e he)

-- ===========================================================================
-- PART III: EXPLICIT PROOF WITHOUT iff_not_self LEMMA
-- ===========================================================================

/-- Expanded proof showing the exact contradiction without citing `iff_not_self`.

    This makes the constructive argument completely transparent. -/
theorem cantor_constructive_explicit {A : Type*} (e : A → A → Prop)
    (he : IsPointwiseSurjective e) : False := by
  obtain ⟨d, hd⟩ := he (fun a => ¬e a a)
  have hdd := hd d
  -- hdd : e d d ↔ ¬e d d
  -- hdd.mp : e d d → ¬(e d d)
  -- hdd.mpr : ¬(e d d) → e d d
  have nev : ¬e d d := fun h => hdd.mp h h
  exact nev (hdd.mpr nev)

-- ===========================================================================
-- PART IV: WHY PROPEXT IS NEEDED IN cantor_recovery
-- ===========================================================================

/-- In `cantor_recovery` (parent file), the proof uses `Function.Surjective e`,
    which gives `∃ a, e a = Not`. The `rwa [← hb]` step then implicitly uses
    propext to rewrite under the equation `Not b = b` (i.e., `¬b = b`).

    Specifically:
    - `hb : ¬b = b`  (equation of Prop-valued functions, requires propext to USE)
    - `rwa [← hb] : ¬b → b` rewrites `b` to `¬b` using propext implicitly

    Our constructive version avoids this by never claiming `e d = Not ∘ e d`
    as function equality — only that `∀ x, e d x ↔ ¬(e x x)`. -/
example : True := trivial  -- placeholder comment anchor

-- ===========================================================================
-- PART V: AXIOM VERIFICATION
-- ===========================================================================

-- The constructive theorems use NO non-constructive axioms:
#print axioms cantor_constructive
-- Expected output: 'cantor_constructive' does not depend on any axioms

#print axioms cantor_constructive_explicit
-- Same: uses no axioms

-- ===========================================================================
-- PART VI: INSTANCES
-- ===========================================================================

/-- The identity relation e(a,b) = (a = b) is not constructively surjective.
    There's no a with ∀ x, (a = x) ↔ ¬(x = x), since ¬(a = a) would hold. -/
theorem eq_not_pointwise_surjective (A : Type*) :
    ¬IsPointwiseSurjective (fun a b : A => a = b) :=
  cantor_no_pointwise_surjection _

/-- For Bool: no e : Bool → Bool → Prop is constructively surjective. -/
theorem bool_not_pointwise_surjective (e : Bool → Bool → Prop) :
    ¬IsPointwiseSurjective e :=
  cantor_no_pointwise_surjection e

/-- For ℕ: no e : ℕ → ℕ → Prop is constructively surjective. -/
theorem nat_not_pointwise_surjective (e : ℕ → ℕ → Prop) :
    ¬IsPointwiseSurjective e :=
  cantor_no_pointwise_surjection e

end CantorDiagonalizationOQ03OQ01OQ04
