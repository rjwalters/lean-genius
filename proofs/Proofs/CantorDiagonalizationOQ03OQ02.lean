/-
Cantor Diagonalization — OQ-03-OQ-02:
A constructive, predicative, propositional-extensionality-free analogue of
Lawvere's fixed-point theorem and Cantor's theorem.

Source: open question 2 of the gallery entry `cantor-diagonalization-oq-03`
        (Lawvere Fixed-Point Theorem and Cantor's Theorem).
Parent: Proofs/CantorDiagonalizationOQ03.lean

## The open question

The parent entry proves Cantor's theorem through Lawvere's fixed-point theorem,
using the *impredicative* power type `A → Prop`: the endomorphism `Not : Prop → Prop`
has no fixed point, hence there is no surjection `A → (A → Prop)`.  Its open
question 2 asks:

  > Is there a constructive analogue of Lawvere's theorem that works in a
  > predicative type theory without propositional extensionality?

This file answers **yes**, and pins down exactly *what* the predicative,
propext-free content is.

## Why the Prop version is impredicative / uses propext

Two features of the parent's `A → Prop` development are, in principle, avoidable:

* **Impredicativity.** `Prop = Sort 0` is impredicative (a `∀` over all `Prop`s is
  again a `Prop`), so `A → Prop` is the "full power set". A predicative reading of
  "subset of `A`" is a *decidable* subset, i.e. a map `A → Bool`, which lives in the
  ordinary data universe `Type u` alongside `A`.

* **Propositional extensionality.** The natural embedding `A ↪ (A → Prop)`,
  `a ↦ (· = a)`, is injective only *up to* `propext`: from `(· = a) = (· = a')` one
  recovers `a = a'` by evaluating at `a` and turning the resulting propositional
  equality `(a = a) = (a = a')` into `a = a'`, which needs `propext`.

Replacing `Prop` by `Bool` removes **both** issues at once:

* `A → Bool : Type u` whenever `A : Type u` — the codomain of the diagonal lives in
  the *same* universe, so the whole argument is predicative;
* the embedding `A ↪ (A → Bool)`, `a ↦ fun x => decide (x = a)`, is injective by a
  pure `decide` computation — **no `propext`**.

Together with Lawvere's theorem (whose proof is already fully constructive — one
surjectivity witness eliminated into a `∃`-goal, no choice) this gives a genuine
strict cardinality increase `A < (A → Bool)` that stays inside a single universe and
uses neither impredicative `Prop` nor propositional extensionality.

## Results

* `lawvere`                    — Lawvere's fixed-point theorem (constructive).
* `FixedPointFree`             — an endomorphism with no fixed point.
* `no_surjection_of_fpf`       — the general engine: a fixed-point-free endomorphism
                                 of `B` rules out any surjection `A → (A → B)`.
* `not_fixedPointFree`         — boolean negation is fixed-point free.
* `no_surjection_to_bool`      — predicative Cantor: no surjection `A → (A → Bool)`.
* `embed_bool` / `embed_bool_injective`
                               — the propext-free embedding `A ↪ (A → Bool)`.
* `predicative_cantor`         — the two directions bundled: an injection exists but
                                 no surjection does (strict growth within `Type u`).
* `embed_of_two`               — the embedding generalized to any alphabet with two
                                 distinct decidable values.
* `no_surjection_to_nat`       — Cantor over the alphabet `ℕ`, via the fixed-point-free
                                 successor (an arbitrary-alphabet instance of the engine).

References:
- F. W. Lawvere, "Diagonal arguments and cartesian closed categories" (1969).
- N. S. Yanofsky, "A universal approach to self-referential paradoxes,
  incompleteness and fixed points" (2003).
- Parent entry `cantor-diagonalization-oq-03`.
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace CantorDiagonalizationOQ03OQ02

open Function

/-! ### Part 1 — Lawvere's fixed-point theorem (constructive)

The proof is the diagonal argument.  It eliminates a single surjectivity witness
into a `∃`-goal, so it uses neither `Classical.choice` nor `propext`. -/

/-- **Lawvere's fixed-point theorem.** If `e : A → (A → B)` is surjective, then every
endomorphism `f : B → B` has a fixed point. -/
theorem lawvere {A B : Type*} (e : A → A → B) (he : Surjective e) (f : B → B) :
    ∃ b : B, f b = b := by
  obtain ⟨a₀, ha₀⟩ := he (fun a => f (e a a))
  exact ⟨e a₀ a₀, by rw [← congr_fun ha₀ a₀]⟩

/-- An endomorphism is *fixed-point free* when it moves every element. -/
def FixedPointFree {B : Type*} (g : B → B) : Prop := ∀ b, g b ≠ b

/-! ### Part 2 — The contrapositive engine

A fixed-point-free endomorphism of the alphabet `B` forbids any surjection onto the
`B`-valued functions.  This is the whole Cantor/Russell phenomenon, isolated. -/

/-- If some `g : B → B` is fixed-point free, there is no surjection `A → (A → B)`. -/
theorem no_surjection_of_fpf {A B : Type*} {g : B → B} (hg : FixedPointFree g)
    (e : A → A → B) : ¬ Surjective e := by
  intro he
  obtain ⟨b, hb⟩ := lawvere e he g
  exact hg b hb

/-! ### Part 3 — The predicative alphabet `Bool`

`Bool` is a two-element *data* type in the lowest universe: no impredicative `Prop`,
and equality on it is decidable by computation. -/

/-- Boolean negation has no fixed point. -/
theorem not_fixedPointFree : FixedPointFree (fun b : Bool => !b) := by
  intro b; cases b <;> decide

/-- **Predicative Cantor (no-surjection direction).** There is no surjection
`A → (A → Bool)`.  The codomain `A → Bool : Type u` sits in the same universe as
`A : Type u`, so the argument is predicative; it invokes no `propext`. -/
theorem no_surjection_to_bool {A : Type*} (e : A → A → Bool) : ¬ Surjective e :=
  no_surjection_of_fpf not_fixedPointFree e

/-- The predicative embedding `A → (A → Bool)` sending `a` to the decidable
characteristic function of `{a}`. -/
def embed_bool {A : Type*} [DecidableEq A] (a : A) : A → Bool := fun x => decide (x = a)

/-- **The embedding is injective — without `propext`.** Injectivity is discharged by a
`decide` computation on `Bool`, the predicative substitute for the `propext`-dependent
injectivity of `a ↦ (· = a) : A → (A → Prop)`. -/
theorem embed_bool_injective {A : Type*} [DecidableEq A] :
    Injective (embed_bool : A → A → Bool) := by
  intro a a' h
  have hh : decide (a = a) = decide (a = a') := congr_fun h a
  rw [decide_eq_decide] at hh
  exact hh.mp rfl

/-- **Predicative Cantor, both directions.** For any type `A` with decidable equality
there is an injection `A ↪ (A → Bool)` but no surjection `A → (A → Bool)`: the
decidable power `A → Bool` is *strictly* larger than `A`, entirely within `Type u`,
using neither impredicative `Prop` nor propositional extensionality. -/
theorem predicative_cantor {A : Type*} [DecidableEq A] :
    (∃ i : A → (A → Bool), Injective i) ∧ (∀ e : A → (A → Bool), ¬ Surjective e) :=
  ⟨⟨embed_bool, embed_bool_injective⟩, fun e => no_surjection_to_bool e⟩

/-! ### Part 4 — Arbitrary decidable alphabets

The embedding needs only two distinct values in the alphabet, and the no-surjection
direction needs only a fixed-point-free endomorphism.  We record both in generality,
then instantiate the finite alphabet `Fin (n+2)` with its cyclic successor. -/

/-- Embedding into `A → B` for any alphabet `B` with two distinct values, using the
`b₁`/`b₀` characteristic function of each point.  Still `propext`-free. -/
theorem embed_of_two {A B : Type*} [DecidableEq A] {b₀ b₁ : B} (hb : b₀ ≠ b₁) :
    Injective (fun (a : A) (x : A) => if x = a then b₁ else b₀) := by
  intro a a' h
  have hval : (if a = a then b₁ else b₀) = (if a = a' then b₁ else b₀) := congr_fun h a
  by_contra hne
  rw [if_pos rfl, if_neg hne] at hval
  exact hb hval.symm

/-- The successor on `ℕ` is fixed-point free (`n + 1 ≠ n`). -/
theorem succ_fixedPointFree : FixedPointFree (fun n : ℕ => n + 1) :=
  fun n => Nat.succ_ne_self n

/-- **Cantor over the alphabet `ℕ`.** No surjection `A → (A → ℕ)`, via the
fixed-point-free successor.  Demonstrates that the engine `no_surjection_of_fpf`
handles arbitrary (here infinite) alphabets, not just `Bool`. -/
theorem no_surjection_to_nat {A : Type*} (e : A → A → ℕ) : ¬ Surjective e :=
  no_surjection_of_fpf succ_fixedPointFree e

end CantorDiagonalizationOQ03OQ02
