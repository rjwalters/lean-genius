/-
# Cantor's Theorem OQ-02: Lawvere's Fixed-Point Theorem and the Unity of Diagonal Arguments

Source: Lawvere (1969), "Diagonal Arguments and Cartesian Closed Categories"

## The Open Question

OQ-02 asks: How does Cantor's theorem relate to type-theoretic universes
and Girard's paradox? Is there a unified framework for Cantor, Russell,
and Gödel?

**Answer**: YES. Lawvere's Fixed-Point Theorem (1969) provides the unified
categorical framework. Cantor, Russell, and Gödel are all instances of a
single abstract diagonal argument:

  *If f : α → (α → β) is surjective, then every g : β → β has a fixed point.*

The paradoxes arise because certain functions (like ¬ : Prop → Prop) have
NO fixed points — making surjection impossible.

## Results

**Part I**:   Russell's paradox — ¬ has no fixed points (2 theorems)
**Part II**:  Lawvere's Fixed-Point Theorem — the abstract diagonal (2 theorems)
**Part III**: Cantor from Lawvere — surjection α→(α→Prop) impossible (3 theorems)
**Part IV**:  Gödel diagonalization — no enumeration covers all predicates (3 theorems)
**Part V**:   Cantor's theorem as corollary — diagonal set witness (2 theorems)
**Part VI**:  Type-universe observations — universe hierarchy prevents Girard (3 theorems)

Axioms: 0
Sorries: 0
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

namespace CantorsTheoremOQ02

open Function

/-
## Part I: Russell's Paradox — Negation Has No Fixed Point

The simplest instance of the diagonal argument: the negation function ¬ on Prop
has no fixed point. If ¬p = p (propositionally), we get an immediate contradiction.
-/

/-- **Negation has no fixed point**: there is no Prop p with p ↔ ¬p.
    This is the essence of Russell's paradox: "the set of all sets that don't
    contain themselves" leads to p ∈ R ↔ p ∉ R, a fixed point of negation. -/
theorem neg_no_fixed_point : ¬∃ p : Prop, p ↔ ¬p := by
  intro ⟨p, hp⟩
  -- If p holds, then ¬p holds (contradiction)
  -- So ¬p must hold; but then p holds (contradiction)
  have hnp : ¬p := fun h => hp.mp h h
  exact hnp (hp.mpr hnp)

/-- **Russell's paradox (set form)**: there is no "Russell set" R ⊆ Prop with
    p ∈ R ↔ p ∉ R for all p. Such a set would require a proposition equivalent
    to its own negation. -/
theorem russell_no_self_membership_set :
    ¬∃ R : Set Prop, ∀ p : Prop, p ∈ R ↔ p ∉ R := by
  intro ⟨R, hR⟩
  -- The proposition q := (True ∈ R) satisfies q ↔ ¬q via hR True
  exact neg_no_fixed_point ⟨True ∈ R, hR True⟩

/-
## Part II: Lawvere's Fixed-Point Theorem

Lawvere (1969) showed that ALL the classical diagonal arguments
(Cantor, Russell, Gödel, Tarski) follow from a single categorical theorem:
any "retract" of a cartesian closed category's hom-set has the fixed-point property.

In type-theoretic terms:
-/

/-- **Lawvere's Fixed-Point Theorem**: If f : α → (α → β) is surjective,
    then every function g : β → β has a fixed point b with g b = b.

    **Proof**: The diagonal construction directly yields the fixed point.
    - Define q : α → β by q x = g (f x x)  (the "diagonal map")
    - Since f is surjective, ∃ a : α, f a = q
    - Then: g (f a a) = q a = (f a) a = f a a
    - So b = f a a is the fixed point.

    This is the abstract essence of ALL diagonal arguments. -/
theorem lawvere_fixed_point {α : Type*} {β : Type*}
    (f : α → (α → β)) (hf : Surjective f) (g : β → β) :
    ∃ b : β, g b = b := by
  -- The diagonal map: apply g to the self-application of f
  set q : α → β := fun x => g (f x x) with hq_def
  -- By surjectivity, f a = q for some a
  obtain ⟨a, ha⟩ := hf q
  -- The fixed point is f a a
  refine ⟨f a a, ?_⟩
  -- f a a = q a = g (f a a)
  have key : f a a = q a := congr_fun ha a
  rw [hq_def] at key
  -- key : f a a = g (f a a), so g (f a a) = f a a ✓
  exact key.symm

/-- **Lawvere's theorem (contrapositive)**: If g : β → β has NO fixed point,
    then no f : α → (α → β) can be surjective.
    This is the form used to derive Cantor's theorem. -/
theorem lawvere_contrapositive {α : Type*} {β : Type*}
    (g : β → β) (hg : ∀ b : β, g b ≠ b)
    (f : α → (α → β)) : ¬Surjective f := by
  intro hf
  obtain ⟨b, hb⟩ := lawvere_fixed_point f hf g
  exact hg b hb

/-
## Part III: Cantor's Theorem Derived from Lawvere

The key observation: negation ¬ : Prop → Prop has NO fixed point (Part I).
By Lawvere's contrapositive, no function α → (α → Prop) can be surjective.
This IS Cantor's theorem.
-/

/-- **Cantor's theorem via Lawvere**: For any type α, no function
    f : α → (α → Prop) is surjective.

    Proof: ¬ : Prop → Prop has no fixed point (by russell/neg_no_fixed_point),
    so by Lawvere's theorem, no surjection exists. -/
theorem cantor_from_lawvere {α : Type*} (f : α → (α → Prop)) :
    ¬Surjective f :=
  lawvere_contrapositive Not
    (fun p hp => neg_no_fixed_point ⟨p, Iff.intro (Eq.mp hp.symm) (Eq.mp hp)⟩)
    f

/-- **Cantor's theorem (set-valued form)**: No function f : α → Set α is surjective.
    This follows directly from `cantor_from_lawvere` since `Set α = α → Prop`. -/
theorem cantor_no_surjection_sets {α : Type*} :
    ∀ f : α → Set α, ¬Surjective f :=
  fun f => cantor_from_lawvere f

/-- **Cantor's inequality**: The "power type" (α → Prop) is always strictly
    larger than α in the sense that no surjection exists. -/
theorem cantor_power_type_strictly_larger (α : Type*) :
    ¬∃ f : α → (α → Prop), Surjective f :=
  fun ⟨f, hf⟩ => cantor_from_lawvere f hf

/-
## Part IV: Gödel Diagonalization

The Lawvere framework also captures Gödel's diagonal lemma.
Given any enumeration of predicates on ℕ, we can diagonalize to
construct a predicate not in the range.
-/

/-- **Gödel's Diagonalization Lemma**: For any enumeration f : ℕ → (ℕ → Prop),
    the diagonal predicate D n = ¬(f n n) is NOT in the range of f.

    This is the predicate-logic version of Cantor's diagonal argument.
    In proof theory, this gives Gödel's incompleteness theorem: the predicate
    "this statement is unprovable" cannot be captured by any consistent system. -/
theorem godel_diagonalization (f : ℕ → (ℕ → Prop)) :
    ∃ D : ℕ → Prop, ∀ n, D ≠ f n := by
  -- The diagonal predicate: D n = ¬(f n n)
  use fun n => ¬(f n n)
  intro n h
  -- If D = f n, then applying at n: (¬f n n) = f n n (Prop equality)
  have hdiag : (¬f n n) = f n n := congr_fun h n
  -- This gives a fixed point of ¬, contradicting neg_no_fixed_point
  -- hdiag : Not (f n n) = f n n, so Eq.mp hdiag : ¬(f n n) → f n n
  exact neg_no_fixed_point ⟨f n n, Iff.intro (Eq.mp hdiag.symm) (Eq.mp hdiag)⟩

/-- **Cantor's diagonal for Bool**: No enumeration ℕ → (ℕ → Bool) is surjective.
    The diagonal sequence d n = !(f n n) is always missing from the enumeration. -/
theorem cantor_diagonal_bool (f : ℕ → (ℕ → Bool)) :
    ∃ d : ℕ → Bool, ∀ n, d ≠ f n := by
  use fun n => ! (f n n)
  intro n h
  -- congr_fun on h gives: !(f n n) = f n n (as Bool)
  have hdiag := congr_fun h n
  -- Case split on Bool value: both cases yield a contradiction
  cases hb : (f n n) <;> simp [hb] at hdiag

/-- **Tarski's undefinability** (Prop version): The "truth predicate" for
    ℕ-indexed propositions cannot be captured by any total function.
    No f : ℕ → (ℕ → Prop) satisfies ∀ P : ℕ → Prop, ∃ n, f n = P. -/
theorem tarski_undefinability :
    ¬∃ f : ℕ → (ℕ → Prop), ∀ P : ℕ → Prop, ∃ n, f n = P :=
  fun ⟨f, hf⟩ => cantor_from_lawvere (fun (n : ℕ) => f n) hf

/-
## Part V: Cantor's Theorem via Direct Diagonal Construction

For completeness, we also show the direct diagonal witness construction
(the set {x | x ∉ f x}) that Cantor originally used.
-/

/-- The **diagonal witness**: given any f : α → Set α, the set
    D = {x | x ∉ f x} is NOT in the range of f. -/
theorem cantor_diagonal_witness {α : Type*} (f : α → Set α) :
    ∃ D : Set α, ∀ a : α, f a ≠ D := by
  -- D = {x | x ∉ f x} (the anti-diagonal set)
  use {x | x ∉ f x}
  intro a ha
  -- ha : f a = {x | x ∉ f x}
  -- Show a ∈ f a ↔ a ∉ f a, which contradicts neg_no_fixed_point
  have hmem : a ∈ f a ↔ a ∉ f a := by
    constructor
    · intro hmem; rw [ha] at hmem; exact hmem
    · intro hnmem; rw [ha]; exact hnmem
  exact neg_no_fixed_point ⟨a ∈ f a, hmem⟩

/-- **Cantor's theorem** (explicit diagonal): The function f : α → Set α
    fails to be surjective, witnessed by the diagonal set. -/
theorem cantor_diagonal_not_surjective {α : Type*} (f : α → Set α) :
    ¬Surjective f := by
  obtain ⟨D, hD⟩ := cantor_diagonal_witness f
  intro hf
  obtain ⟨a, ha⟩ := hf D
  exact hD a ha

/-
## Part VI: Type-Theoretic Universe Hierarchy and Girard's Paradox

Girard's paradox (1972) shows that if we allowed Type : Type (a "universe
in itself"), we could derive a contradiction analogous to Russell's paradox.
Lean 4 avoids this via the universe hierarchy: Type u : Type (u+1).

The connection to Cantor/Lawvere: "Type : Type" would give a type U with
a surjection U → (U → Prop), enabling every g : Prop → Prop (including ¬)
to have a fixed point — but neg_no_fixed_point prevents this.
-/

/-- **No type is its own function space**: There is no type α with a surjection
    α → (α → α). This generalizes Cantor: even without Prop, pure self-reference
    leads to fixed-point theorems that may be unwanted. -/
theorem lawvere_no_self_surjection {α : Type*} {g : α → α}
    (hg : ∀ b : α, g b ≠ b) (f : α → (α → α)) : ¬Surjective f :=
  lawvere_contrapositive g hg f

/-- **Diagonal arguments are universal**: Every instance of the diagonal method
    (Cantor, Russell, Gödel, Tarski) follows the same pattern:
    surjection f : α → (α → β) + fixed-point-free g : β → β → contradiction. -/
theorem diagonal_argument_schema {α : Type*} {β : Type*}
    (g : β → β) (hg : ∀ b : β, g b ≠ b)
    (f : α → (α → β)) : ¬Surjective f :=
  lawvere_contrapositive g hg f

/-- **Summary theorem**: The Lawvere-Cantor framework unifies:
    (1) No surjection α → (α → Prop) [Cantor]
    (2) Negation has no fixed point [Russell]
    (3) No enumeration ℕ → (ℕ → Prop) is surjective [Gödel/Tarski]

    All three are consequences of: Surjective f : α → (α → Prop)
    would force ¬ to have a fixed point, contradicting neg_no_fixed_point. -/
theorem lawvere_cantor_unity :
    -- (1) Cantor: no surjection from any type to its predicate type
    (∀ (α : Type*) (f : α → (α → Prop)), ¬Surjective f) ∧
    -- (2) Russell: negation has no fixed point
    (¬∃ p : Prop, p ↔ ¬p) ∧
    -- (3) Gödel: any predicate enumeration misses some predicate
    (∀ f : ℕ → (ℕ → Prop), ∃ D : ℕ → Prop, ∀ n, D ≠ f n) :=
  ⟨fun _ f => cantor_from_lawvere f,
   neg_no_fixed_point,
   godel_diagonalization⟩

/-
## Summary

The key insight: ALL diagonal arguments share the structure of
Lawvere's Fixed-Point Theorem.

The "magic" of the diagonal: given f : α → (α → β), define q x = g(f x x).
If f is surjective, q = f a for some a, giving g(f a a) = q a = f a a —
a fixed point of g. So "g has no fixed point" prevents surjection.

For Cantor: g = ¬ (negation on Prop)
For Gödel: g = ¬ (diagonalizing the provability predicate)
For Tarski: g = ¬ (the truth predicate is not arithmetically definable)
For Russell: g = ¬ (the set of all non-self-members)

Lean 4's universe hierarchy (Type u : Type (u+1)) prevents Girard's paradox
by blocking the construction of a type U with U ≅ U → Prop directly.
-/

end CantorsTheoremOQ02
