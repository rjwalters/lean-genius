/-
  The infinite analogue of subset counting: Cantor's theorem |𝒫(S)| > |S|.

  The parent entry `subset-count` proves the finite count: an `n`-element set has
  exactly `2^n` subsets (`Fintype.card (Finset α) = 2 ^ Fintype.card α`).  Two facts
  are hiding inside that formula.  First, the count `2^n` already *strictly* exceeds
  `n` — a finite set has strictly more subsets than elements.  Second, this strict
  gap is not an accident of finiteness: it persists at *every* cardinality.  That is
  Cantor's theorem, the infinite analogue of subset counting.

  This file makes the lineage explicit:

    * an explicit diagonal set `diagonalSet f = {x | x ∉ f x}`, proved never to lie in
      the range of any `f : α → Set α` — a self-contained diagonal argument;
    * Cantor's theorem in surjection form (`not_surjective_to_set`) and injection form
      (`not_injective_from_set`);
    * the cardinal form `#α < #(Set α) = 2 ^ #α`, the literal infinite analogue of the
      parent's finite `2^n`;
    * the finite shadow `Fintype.card α < Fintype.card (Finset α)`, i.e. the parent's
      `2^n` already strictly dominates `n`.

  The core inequality reuses Mathlib's `Cardinal.cantor` / `Cardinal.mk_set`; the
  contributions are the explicit diagonal witness and the bridge tying the finite
  subset count to its infinite analogue.  Fully verified: 0 sorries, 0 axioms, no
  `native_decide`.
-/
import Mathlib

open Function
open scoped Cardinal

namespace SubsetCountOQ01

universe u
variable {α : Type u}

/-- The **diagonal set** of a candidate enumeration `f : α → Set α`: the elements
that are *not* contained in their own image set.  This is the set Cantor's argument
uses to defeat any attempt to list every subset of `α` by elements of `α`. -/
def diagonalSet (f : α → Set α) : Set α := {x | x ∉ f x}

/-- **The diagonal argument, explicitly.** The diagonal set of `f` is never in the
range of `f`: if `f a = diagonalSet f` then `a ∈ f a ↔ a ∉ f a`, a contradiction. -/
theorem diagonalSet_not_mem_range (f : α → Set α) :
    diagonalSet f ∉ Set.range f := by
  rintro ⟨a, ha⟩
  have h : a ∈ f a ↔ a ∉ f a := by
    have hmem : a ∈ f a ↔ a ∈ diagonalSet f := by rw [ha]
    simpa [diagonalSet, Set.mem_setOf_eq] using hmem
  tauto

/-- **Cantor's theorem, surjection form.** No map `f : α → Set α` is surjective: the
subsets of `α` cannot be enumerated by the elements of `α`.  Witnessed by the diagonal
set, which lies outside every range. -/
theorem not_surjective_to_set (f : α → Set α) : ¬ Surjective f := fun hf =>
  diagonalSet_not_mem_range f (Set.mem_range.mpr (hf (diagonalSet f)))

/-- **Cantor's theorem, injection form.** No map `g : Set α → α` is injective: there is
no way to label distinct subsets of `α` by distinct elements of `α`. -/
theorem not_injective_from_set (g : Set α → α) : ¬ Injective g :=
  cantor_injective g

/-- The cardinality of the powerset: `#(Set α) = 2 ^ #α` — the infinite-cardinal
analogue of the parent's finite count `Fintype.card (Finset α) = 2 ^ Fintype.card α`. -/
theorem mk_set_eq_two_pow (α : Type u) : #(Set α) = 2 ^ #α := Cardinal.mk_set

/-- **Cantor's theorem, cardinal form.** `#α < #(Set α)`: every set has strictly fewer
elements than subsets.  Equivalently `#α < 2 ^ #α`. -/
theorem mk_lt_mk_set (α : Type u) : #α < #(Set α) := by
  rw [mk_set_eq_two_pow]
  exact Cardinal.cantor _

/-- The strict cardinal inequality in exponential form: `#α < 2 ^ #α`. -/
theorem mk_lt_two_pow_mk (α : Type u) : #α < 2 ^ #α := Cardinal.cantor _

/-- **Finite shadow / bridge to the parent.** For a finite type the number of subsets
strictly exceeds the number of elements: `Fintype.card α < Fintype.card (Finset α)`.
Since `Fintype.card (Finset α) = 2 ^ Fintype.card α` (the parent's count), this says
`n < 2^n` — the parent's `2^n` already strictly dominates `n`, the finite case of
Cantor. -/
theorem card_lt_card_finset (α : Type u) [Fintype α] :
    Fintype.card α < Fintype.card (Finset α) := by
  rw [Fintype.card_finset]
  exact Nat.lt_two_pow_self

/-- The finite inequality stated arithmetically: an `n`-element set has strictly more
than `n` subsets, `n < 2^n`. -/
theorem card_lt_two_pow (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self

end SubsetCountOQ01
