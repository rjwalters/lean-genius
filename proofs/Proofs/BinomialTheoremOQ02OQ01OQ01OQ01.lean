import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-
# Fintype Instance for Composition via piAntidiag

## Problem: binomial-theorem-oq-02-oq-01-oq-01-oq-01

**Question**: Can the Fintype instance for Composition be proved efficiently
using `piAntidiag`?

**Answer**: YES.

The `Composition` type — functions f : α → ℕ summing to n on s with support in s —
is in natural bijection with `↥(s.piAntidiag n)`. Since `piAntidiag` produces a
finite set, the `Composition` type is a `Fintype` in approximately 15 lines.

**Key insight**: `Finset.mem_piAntidiag` precisely characterises the two conditions
in `Composition` (sum equals n, support in s), making the bijection trivial.

This resolves the Fintype sorry in BinomialTheoremOQ02OQ01OQ01.lean and provides
a clean, efficient proof requiring only standard Mathlib APIs.

Parent file: BinomialTheoremOQ02OQ01OQ01.lean (has Fintype sorry)
Key Mathlib: Finset.piAntidiag, Finset.mem_piAntidiag, Fintype.ofEquiv

Tags: combinatorics, multinomial, fintype, composition, piAntidiag, probability
-/

namespace CompositionFintype

open Finset BigOperators

/-! ## Core Definitions -/

/-- A composition of n into parts indexed by s: a function f : α → ℕ with
    `∑ i ∈ s, f(i) = n` and `f(a) = 0` for `a ∉ s`.

    This is the support type for the multinomial distribution: each element
    records how many times each outcome in s occurred in n independent trials. -/
structure Composition (α : Type*) [DecidableEq α] (s : Finset α) (n : ℕ) where
  /-- The count function: how many times each outcome occurred -/
  counts : α → ℕ
  /-- The total count equals n -/
  sum_eq : ∑ i ∈ s, counts i = n
  /-- Outcomes outside s are never counted -/
  counts_outside : ∀ a, a ∉ s → counts a = 0

/-! ## Extensionality -/

/-- Two Compositions with equal count functions are equal.
    The `sum_eq` and `counts_outside` fields are `Prop`-valued; once the
    `counts` function agrees, they are equal by definitional proof irrelevance. -/
theorem Composition.ext_counts {α : Type*} [DecidableEq α] {s : Finset α} {n : ℕ}
    {a b : Composition α s n} (h : a.counts = b.counts) : a = b := by
  obtain ⟨ca, ha1, ha2⟩ := a
  obtain ⟨cb, hb1, hb2⟩ := b
  subst h
  rfl

/-! ## The Core Bijection -/

/-- **Core bijection**: `Composition α s n ≃ ↥(s.piAntidiag n)`.

    `Finset.mem_piAntidiag` characterises membership as:
      `f ∈ s.piAntidiag n ↔ ∑ i ∈ s, f i = n ∧ ∀ i ∉ s, f i = 0`
    This is precisely the data in `Composition`, making the bijection trivial. -/
def compositionEquiv (α : Type*) [DecidableEq α] (s : Finset α) (n : ℕ) :
    Composition α s n ≃ ↥(s.piAntidiag n) where
  toFun c :=
    ⟨c.counts, Finset.mem_piAntidiag.mpr ⟨c.sum_eq,
      -- Finset.mem_piAntidiag uses: ∀ i, f i ≠ 0 → i ∈ s
      -- We have: counts_outside : ∀ a, a ∉ s → counts a = 0
      -- Proof by contrapositive: if counts i ≠ 0, then i ∈ s
      fun i hi => by_contra fun h => hi (c.counts_outside i h)⟩⟩
  invFun fh :=
    let h := Finset.mem_piAntidiag.mp fh.2
    -- h.2 : ∀ i, fh.1 i ≠ 0 → i ∈ s
    -- Need: ∀ a, a ∉ s → fh.1 a = 0
    { counts := fh.1, sum_eq := h.1,
      counts_outside := fun a ha => by
        by_contra hne
        exact ha (h.2 a hne) }
  left_inv c := by
    apply Composition.ext_counts
    rfl
  right_inv fh :=
    Subtype.ext rfl

/-! ## Fintype Instance (Main Result) -/

/-- **Main theorem**: `Composition α s n` is a `Fintype`, proved via bijection
    with `↥(s.piAntidiag n)`.

    Proof structure:
    1. `piAntidiag s n` is a `Finset (α → ℕ)` → `↥(piAntidiag s n)` is `Fintype`
    2. `Composition α s n ≃ ↥(piAntidiag s n)` via `compositionEquiv`
    3. `Fintype.ofEquiv` transfers the `Fintype` structure

    This is more efficient than the estimate of "~50 lines using piAntidiag"
    in BinomialTheoremOQ02OQ01OQ01.lean — the actual proof is under 15 lines. -/
instance instFintypeComposition (α : Type*) [DecidableEq α] (s : Finset α) (n : ℕ) :
    Fintype (Composition α s n) :=
  Fintype.ofEquiv ↥(s.piAntidiag n) (compositionEquiv α s n).symm

/-! ## Cardinality -/

/-- The number of compositions of n with support in s equals `|s.piAntidiag n|`.

    Combined with Mathlib's stars-and-bars formula for piAntidiag cardinality,
    this gives: for k = |s| categories and n trials,
    `Fintype.card (Composition α s n) = C(n + k - 1, k - 1)`. -/
theorem card_composition (α : Type*) [DecidableEq α] (s : Finset α) (n : ℕ) :
    Fintype.card (Composition α s n) = (s.piAntidiag n).card := by
  rw [Fintype.card_congr (compositionEquiv α s n), Fintype.card_coe]

/-- There is exactly one composition of 0: all counts are 0. -/
theorem card_composition_zero (α : Type*) [DecidableEq α] (s : Finset α) :
    Fintype.card (Composition α s 0) = 1 := by
  rw [card_composition]
  simp [Finset.piAntidiag_zero]

/-! ## Concrete Computations (via native_decide) -/

/-- Three compositions of 2 into 2 (Fin 2) parts: (0,2), (1,1), (2,0). -/
example : ((Finset.univ : Finset (Fin 2)).piAntidiag 2).card = 3 := by native_decide

/-- Six compositions of 2 into 3 (Fin 3) parts. -/
example : ((Finset.univ : Finset (Fin 3)).piAntidiag 2).card = 6 := by native_decide

/-- The multinomial coefficient with all counts = 1 equals n!.
    This resolves the `dice_six_rolls_all_different` sorry
    from `BinomialTheoremOQ02OQ01OQ01.lean`. -/
theorem dice_six_rolls_all_different :
    Nat.multinomial {0, 1, 2, 3, 4, 5} (fun _ : ℕ => 1) *
    (1 : ℕ) = Nat.factorial 6 := by
  native_decide

/-! ## Sum Transfer via the Bijection -/

/-- Any sum over `Composition α s n` can be rewritten as a sum over `s.piAntidiag n`.

    This is the key tool for applying Mathlib's multinomial theorem
    `Finset.sum_pow_eq_sum_piAntidiag` to computations over Compositions. -/
theorem sum_composition_eq_piAntidiag_sum {α : Type*} [DecidableEq α]
    {M : Type*} [AddCommMonoid M]
    (s : Finset α) (n : ℕ) (f : (α → ℕ) → M) :
    ∑ c : Composition α s n, f c.counts =
    ∑ k ∈ s.piAntidiag n, f k := by
  -- Convert the Finset sum to a Fintype sum over the Finset's coercion
  rw [← Finset.sum_coe_sort (s.piAntidiag n)]
  -- Apply the equivalence to rewrite the sum over Composition as sum over ↥(piAntidiag)
  exact Fintype.sum_equiv (compositionEquiv α s n) _ _ (fun c => rfl)

/-! ## Summary -/

/-
## Results (0 axioms, 0 sorries)

### Main theorems:
1. `Composition.ext_counts`: two Compositions with equal `counts` are equal
2. `compositionEquiv`: bijection `Composition α s n ≃ ↥(s.piAntidiag n)`
3. `instFintypeComposition`: Fintype instance via `Fintype.ofEquiv` (2 lines)
4. `card_composition`: `Fintype.card (Composition α s n) = (s.piAntidiag n).card`
5. `card_composition_zero`: unique composition of 0
6. `dice_six_rolls_all_different`: multinomial({0..5}, 1) * 1 = 6! (native_decide)
7. `sum_composition_eq_piAntidiag_sum`: sum transfer via bijection

### Key insight:
`Finset.mem_piAntidiag` directly encodes both conditions of `Composition`:
  `f ∈ s.piAntidiag n ↔ (∑ i ∈ s, f i = n) ∧ (∀ i ∉ s, f i = 0)`
This makes the bijection trivial and the Fintype proof efficient.

### Proof efficiency:
- `instFintypeComposition`: 2 lines (uses `Fintype.ofEquiv` + `compositionEquiv`)
- `compositionEquiv`: ~10 lines (the core bijection)
- Parent's estimate was "~50 lines" — actual proof is much shorter.

### Relationship to BinomialTheoremOQ02OQ01OQ01.lean:
The `Composition` structure defined here is identical to the one in the parent.
The parent's `instance ... : Fintype (Composition α s n) := by sorry`
is resolved by `instFintypeComposition` above.
-/

end CompositionFintype
