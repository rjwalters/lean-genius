import Mathlib.Logic.Function.Basic
import Mathlib.Order.BooleanAlgebra

/-
# Lawvere Fixed-Point Theorem and Cantor's Theorem

## What This Proves
The Lawvere fixed-point theorem: if there exists a surjection e : A → (A → B),
then every endomorphism f : B → B has a fixed point. As a corollary, Cantor's
theorem follows: there is no surjection from any type to its power type (A → Prop),
because negation (not) has no fixed point in Prop.

This unifies Cantor's diagonal argument, Russell's paradox, the halting problem,
and Gödel's incompleteness theorem as instances of a single categorical principle.

## Approach
- **Foundation**: Pure type theory — no Mathlib dependencies beyond basic logic
- **Key idea**: The diagonal g(a) = f(e(a)(a)) must equal some e(a₀) by surjectivity
- **Cantor**: Instantiate with B = Prop, f = not; no fixed point → no surjection

## Proof Techniques
- Diagonal construction (Lawvere's categorical trick)
- Proof by contradiction (Cantor from Lawvere)
- Functional extensionality argument

Historical Note: F. William Lawvere (1969) showed that Cantor's diagonal argument
is an instance of a general fixed-point theorem in cartesian closed categories.
This formalization presents the type-theoretic version.
-/

namespace LawvereCantor

/-
  Part 1: The Lawvere Fixed-Point Theorem

  If e : A → (A → B) is surjective, then every f : B → B has a fixed point.
  The proof constructs the diagonal function g(a) = f(e(a)(a)) and uses
  surjectivity to find a₀ with e(a₀) = g, giving f(g(a₀)) = g(a₀).
-/

-- The Lawvere fixed-point theorem
theorem lawvere_fixpoint {A B : Type*} (e : A → A → B)
    (he : Function.Surjective e) (f : B → B) :
    ∃ b : B, f b = b := by
  -- Define the diagonal: g(a) = f(e(a)(a))
  obtain ⟨a₀, ha₀⟩ := he (fun a => f (e a a))
  -- a₀ satisfies e(a₀) = g, so e(a₀)(a₀) = g(a₀) = f(e(a₀)(a₀))
  exact ⟨e a₀ a₀, by rw [← congr_fun ha₀ a₀]⟩

/-
  Part 2: No Fixed-Point-Free Endomorphism Corollary

  Contrapositive: if some f : B → B has no fixed point, then no
  e : A → (A → B) can be surjective.
-/

-- If f has no fixed point, there is no surjection A → (A → B)
theorem no_surjection_if_no_fixpoint {A B : Type*} (f : B → B)
    (hf : ∀ b, f b ≠ b) : ¬ ∃ e : A → A → B, Function.Surjective e := by
  rintro ⟨e, he⟩
  obtain ⟨b, hb⟩ := lawvere_fixpoint e he f
  exact hf b hb

/-
  Part 3: Cantor's Theorem via Lawvere

  There is no surjection from A to (A → Prop), because negation
  (not : Prop → Prop) has no fixed point: ¬p = p is impossible.
-/

-- Negation has no fixed point in Prop
theorem not_has_no_fixpoint : ∀ p : Prop, (¬p) ≠ p := by
  intro p h
  -- Transport along the equality ¬p = p
  have to_np : p → ¬p := cast h.symm
  have to_p : ¬p → p := cast h
  -- Construct ¬p by self-application (the Russell-like trick)
  have np : ¬p := fun hp => to_np hp hp
  -- Derive contradiction
  exact np (to_p np)

-- Cantor's theorem: no surjection A → (A → Prop)
theorem cantor {A : Type*} (e : A → A → Prop) :
    ¬ Function.Surjective e := by
  intro he
  obtain ⟨b, hb⟩ := lawvere_fixpoint e he Not
  exact not_has_no_fixpoint b hb

-- Alternative statement: the power type has strictly larger cardinality
theorem cantor_no_surjection (A : Type*) :
    ¬ ∃ e : A → A → Prop, Function.Surjective e :=
  no_surjection_if_no_fixpoint Not not_has_no_fixpoint

/-
  Part 4: Cantor's Theorem for Bool (Decidable Version)

  The same argument works with Bool instead of Prop: boolean negation
  has no fixed point, so there is no surjection A → (A → Bool).
-/

-- Boolean negation has no fixed point
theorem bnot_has_no_fixpoint : ∀ b : Bool, (!b) ≠ b := by
  intro b
  cases b <;> decide

-- Cantor's theorem for Bool: no surjection A → (A → Bool)
theorem cantor_bool {A : Type*} (e : A → A → Bool) :
    ¬ Function.Surjective e := by
  intro he
  obtain ⟨b, hb⟩ := lawvere_fixpoint e he (! ·)
  exact bnot_has_no_fixpoint b hb

/-
  Part 5: Russell's Paradox as a Lawvere Instance

  If we could form the set of all sets, we would have a surjection
  from the universe to its power set. Lawvere prevents this.
  We formalize this as: no type can enumerate all its subtypes.
-/

-- Russell's paradox: no type can classify all predicates on itself
-- (This is exactly Cantor's theorem restated)
theorem russell (A : Type*) :
    ¬ ∃ e : A → A → Prop, ∀ S : A → Prop, ∃ a, e a = S :=
  cantor_no_surjection A

/-
  Part 6: The Diagonal Lemma (Explicit Construction)

  Makes the diagonal construction explicit: given any e : A → (A → B),
  the function g(a) = f(e(a)(a)) is not in the range of e when f has
  no fixed point.
-/

-- The diagonal function is not in the range of e
theorem diagonal_not_in_range {A B : Type*} (e : A → A → B)
    (f : B → B) (hf : ∀ b, f b ≠ b) :
    (fun a => f (e a a)) ∉ Set.range e := by
  rintro ⟨a₀, ha₀⟩
  exact hf (e a₀ a₀) (congr_fun ha₀ a₀).symm

end LawvereCantor

-- Verification
#check LawvereCantor.lawvere_fixpoint
#check LawvereCantor.cantor
#check LawvereCantor.cantor_bool
#check LawvereCantor.russell
#check LawvereCantor.diagonal_not_in_range
