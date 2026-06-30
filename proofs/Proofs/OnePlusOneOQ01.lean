/-
# ℕ as a Natural Numbers Object — the categorical face of Peano arithmetic

## What This Proves
The parent entry (`OnePlusOne.lean`) builds the natural numbers as a *type-theoretic*
inductive type and proves `1 + 1 = 2` by definitional computation. This follow-up answers
the entry's open question — *how do the foundations of mathematics (set theory, type
theory, category theory) relate?* — with one concrete, machine-checked bridge:

  **The inductively-defined `ℕ` is a Natural Numbers Object (Lawvere, 1964): it is the
  initial algebra of the endofunctor `X ↦ 1 + X`.**

Concretely, for every type `A` with a chosen point `a : A` and an endomap `f : A → A`,
there is a **unique** `u : ℕ → A` with `u 0 = a` and `u (succ n) = f (u n)`.  In categorical
language `a` is an arrow `1 → A`, `f` is `A → A`, and `u` is the unique mediating arrow out
of the initial `(point, endomap)`-algebra `(ℕ, zero, succ)`.  This single universal property
is simultaneously:

  * the **type-theoretic** recursor / iterator (`iter` below — existence is just `ℕ.rec`),
  * the **set-theoretic** Dedekind recursion theorem (in ZFC it is a *theorem* requiring a
    transfinite-free but non-trivial construction; here existence is a computation rule),
  * the **category-theoretic** statement that `(ℕ, zero, succ)` is an initial object in the
    category of `(point, endomap)`-algebras.

We then *recover* addition and multiplication as the unique maps named by this universal
property, and prove **Lambek's lemma** in concrete form: the structure map `1 + ℕ → ℕ`
(i.e. `none ↦ 0`, `some n ↦ succ n`) is a bijection, so `ℕ ≅ 1 + ℕ`.

## Approach
- **Foundation (from Mathlib):** None.  Like the parent, this file imports nothing.  The
  recursor, `funext` (which rests only on `Quot.sound`), `Option`, and `ExistsUnique` are all
  Lean-core.  This keeps the foundational point honest: the universal property is genuinely
  available with no analytic or set-theoretic scaffolding.
- **Original Contributions:** A self-contained proof that the Peano naturals satisfy the
  Lawvere Natural Numbers Object universal property (existence + uniqueness), the derivation
  of `+` and `*` from that property, and a concrete Lambek isomorphism `ℕ ≅ 1 + ℕ`.
- **Proof Techniques Demonstrated:** Initial-algebra reasoning, `∃!` over a function space
  (closed by `funext`), iteration/catamorphism, structural induction for uniqueness.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
None.  Self-contained; the only non-constructive ingredient is `Quot.sound` (used by
`funext` to phrase uniqueness as an equality of functions), one of Lean's three foundational
axioms and not a mathematical assumption.
-/

namespace PeanoNNO

-- ============================================================
-- PART 1: The Peano naturals (the same inductive type as the parent)
-- ============================================================

/-- The Peano naturals: the initial algebra of `X ↦ 1 + X`, presented as an inductive type.
The two constructors `zero : 1 → ℕ` and `succ : ℕ → ℕ` are precisely the structure map of the
algebra, split into its two components. -/
inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr

open ℕ

def one : ℕ := succ zero
def two : ℕ := succ (succ zero)

-- ============================================================
-- PART 2: The iterator — the EXISTENCE half of the universal property
-- ============================================================

/-- `iter f a` is the canonical map out of `ℕ`: it sends `zero ↦ a` and iterates `f`.

Categorically this is the unique algebra homomorphism `(ℕ, zero, succ) → (A, a, f)`, a.k.a.
the *catamorphism* (`fold`) for the `(point, endomap)`-algebra structure.  Its very
definition *is* the recursor `ℕ.rec`, so existence of a mediating arrow is a computation
rule, not a proof obligation. -/
def iter {A : Type} (f : A → A) (a : A) : ℕ → A
  | zero   => a
  | succ n => f (iter f a n)

/-- First defining equation: `iter` respects the point `zero ↦ a`.  Holds by `rfl`. -/
theorem iter_zero {A : Type} (f : A → A) (a : A) : iter f a zero = a := rfl

/-- Second defining equation: `iter` is an algebra homomorphism, `iter ∘ succ = f ∘ iter`.
Holds by `rfl` (the recursor's iota rule). -/
theorem iter_succ {A : Type} (f : A → A) (a : A) (n : ℕ) :
    iter f a (succ n) = f (iter f a n) := rfl

-- ============================================================
-- PART 3: Uniqueness — the INITIALITY half of the universal property
-- ============================================================

/-- Any map satisfying the two algebra-homomorphism equations *is* `iter f a`.  This is the
content of initiality: the mediating arrow is unique.  Proved by structural induction — the
induction principle of the inductive type delivers exactly the uniqueness that the
set-theoretic recursion theorem must establish by a separate argument. -/
theorem iter_unique {A : Type} (f : A → A) (a : A) (u : ℕ → A)
    (h0 : u zero = a) (hs : ∀ n, u (succ n) = f (u n)) :
    ∀ n, u n = iter f a n := by
  intro n
  induction n with
  | zero => rw [h0, iter_zero]
  | succ n ih => rw [hs, ih, iter_succ]

/-- **Lawvere's Natural Numbers Object universal property.**
For every type `A`, point `a : A`, and endomap `f : A → A`, there is a *unique* `u : ℕ → A`
with `u zero = a` and `u (succ n) = f (u n)`.

This says `(ℕ, zero, succ)` is the **initial** `(point, endomap)`-algebra, i.e. the initial
algebra of the functor `X ↦ 1 + X`.  Existence is `iter`; uniqueness is `iter_unique` lifted
to an equality of functions via `funext`.

(We spell out the `∃!` by hand — `there is one solution, and any solution equals it` — to keep
the file Mathlib-free, since the `∃!` notation lives in Mathlib.) -/
theorem nno_universal {A : Type} (a : A) (f : A → A) :
    ∃ u : ℕ → A, (u zero = a ∧ ∀ n, u (succ n) = f (u n)) ∧
      ∀ v : ℕ → A, (v zero = a ∧ ∀ n, v (succ n) = f (v n)) → v = u := by
  refine ⟨iter f a, ⟨iter_zero f a, fun n => iter_succ f a n⟩, ?_⟩
  intro v hv
  exact funext (fun n => iter_unique f a v hv.1 hv.2 n)

-- ============================================================
-- PART 4: Addition and multiplication, RECOVERED from the universal property
-- ============================================================

/-- Addition is the map named by the universal property at the algebra `(n, succ)`:
`add n = iter succ n`.  Thus `+` is not an extra primitive — it is forced by initiality. -/
def add (n : ℕ) : ℕ → ℕ := iter succ n

theorem add_zero (n : ℕ) : add n zero = n := rfl
theorem add_succ (n m : ℕ) : add n (succ m) = succ (add n m) := rfl

/-- 1 + 1 = 2, recovered through the universal property rather than as a bare `rfl`. -/
theorem one_add_one : add one one = two := rfl

/-- **Addition is characterized by the universal property.**  Any `g` solving the same two
equations as `add n` must equal `add n` — a direct corollary of initiality. -/
theorem add_eq_unique (n : ℕ) (g : ℕ → ℕ)
    (h0 : g zero = n) (hs : ∀ m, g (succ m) = succ (g m)) : g = add n :=
  funext (fun m => iter_unique succ n g h0 hs m)

/-- Multiplication is the map named by the universal property at the algebra `(zero, add n)`:
`mul n = iter (add n) zero`.  So `*` too is forced by initiality, layered over `+`. -/
def mul (n : ℕ) : ℕ → ℕ := iter (add n) zero

theorem mul_zero (n : ℕ) : mul n zero = zero := rfl
theorem mul_succ (n m : ℕ) : mul n (succ m) = add n (mul n m) := rfl

-- ============================================================
-- PART 5: Lambek's lemma — the structure map is an isomorphism, ℕ ≅ 1 + ℕ
-- ============================================================

/-- The structure map of the algebra, `1 + ℕ → ℕ`, presented via `Option` (`Option ℕ` is the
type `1 + ℕ`): `none` is the point `zero`, `some n` is `succ n`. -/
def structMap : Option ℕ → ℕ
  | none   => zero
  | some n => succ n

/-- The candidate inverse `ℕ → 1 + ℕ`: `zero ↦ none`, `succ n ↦ some n`.  Its existence is the
"every natural is zero or a successor, uniquely" fact. -/
def structInv : ℕ → Option ℕ
  | zero   => none
  | succ n => some n

theorem structMap_leftInv : ∀ x : Option ℕ, structInv (structMap x) = x
  | none   => rfl
  | some _ => rfl

theorem structInv_rightInv : ∀ n : ℕ, structMap (structInv n) = n
  | zero   => rfl
  | succ _ => rfl

/-- **Lambek's lemma, concrete form.**  `structMap : 1 + ℕ → ℕ` is a two-sided inverse of
`structInv`, hence a bijection: `ℕ ≅ 1 + ℕ`.  Lambek's lemma says the structure map of an
*initial* algebra is always an isomorphism; here we exhibit the iso explicitly, witnessing
that `ℕ` is a fixed point of the functor `X ↦ 1 + X`. -/
theorem lambek : (∀ x : Option ℕ, structInv (structMap x) = x) ∧
    (∀ n : ℕ, structMap (structInv n) = n) :=
  ⟨structMap_leftInv, structInv_rightInv⟩

-- Axiom audit: the headline results rest only on `Quot.sound` (used by `funext`), with no
-- `sorryAx` and no `Lean.ofReduceBool`.  The defining-equation and Lambek lemmas are fully
-- axiom-free (`rfl` / structural case analysis).
#print axioms nno_universal
#print axioms iter_unique
#print axioms add_eq_unique
#print axioms lambek

end PeanoNNO

/-
## PART 6: How the three foundations meet at `ℕ`

The single theorem `nno_universal` is the meeting point of the three foundational traditions
named in the open question:

* **Type theory.**  Existence of the mediating map is `ℕ.rec`; its computation rules
  (`iter_zero`, `iter_succ`) hold by `rfl`.  Recursion is *built in*.

* **Set theory.**  The same statement is Dedekind's recursion theorem (1888): given a set `A`,
  an element `a ∈ A`, and `f : A → A`, there is a unique `u : ℕ → A` with `u 0 = a` and
  `u(n⁺) = f(u n)`.  In ZFC this is a genuine theorem — one proves the recursion *exists* by
  taking a union of approximating partial functions and verifying it is functional.  Russell
  and Whitehead's 362 pages live on this side of the bridge.

* **Category theory.**  Lawvere (1964) packaged the universal property as the definition of a
  *Natural Numbers Object*: an initial algebra for `X ↦ 1 + X`.  `nno_universal` is exactly
  initiality, and Lambek's lemma (`lambek`) is the categorical reason `ℕ ≅ 1 + ℕ`.

The point is not that one foundation is "right".  It is that `ℕ` is *the same object* in all
three — pinned down, up to unique isomorphism, by one universal property.  Type theory makes
that property a definitional computation; set theory makes it a theorem to be proved; category
theory makes it a definition to be characterized.  This file checks, with no axioms beyond
`Quot.sound`, that the type-theoretic `ℕ` satisfies the categorical specification.
-/
