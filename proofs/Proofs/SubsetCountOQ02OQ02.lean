import Mathlib

/-
# Pascal's Recurrence from the Powerset Decomposition (OQ-02-OQ-02)

## Open Question

The parent entry counts distinct submultisets via the product formula
`∏ a, (mₐ + 1)` (Mathlib's `Multiset.card_Iic`). A natural follow-up asks: can
the *binomial* recurrences be recovered the same combinatorial way — by
decomposing the powerset itself, rather than by unfolding the recursive
definition of `Nat.choose`?

This file answers YES for the two canonical decompositions of a powerset:

1. **Fix an element.** The `(k+1)`-subsets of `a ::ₘ s` split into those that
   omit `a` (the `(k+1)`-subsets of `s`) and those that use `a` (in bijection
   with the `k`-subsets of `s`). Counting both sides yields **Pascal's
   recurrence**
   `(m+1).choose (k+1) = m.choose (k+1) + m.choose k`.

2. **Fix the size.** The full powerset of an `m`-set is the disjoint union of
   its size-`k` layers for `k = 0, …, m`. Counting both sides yields the
   **row-sum identity** `∑ k, m.choose k = 2^m`.

Both proofs are genuinely combinatorial: they read the arithmetic off a
structural decomposition of a finite collection of sets, not off the
`Nat.rec` definition of the binomial coefficient. Mathlib *does* contain
`Nat.choose_succ_succ` and `Nat.sum_range_choose`, but those are proved by
recursion/induction; here we derive them from `powersetCard_cons`,
`powersetCard_succ_insert`, and `powerset_card_disjiUnion`.

## Summary Statistics

- Sorries: 0
- Axioms: 0 (no `axiom`, no `native_decide`)
- Key Mathlib inputs: `Multiset.powersetCard_cons`, `Multiset.card_powersetCard`,
  `Finset.powersetCard_succ_insert`, `Finset.powerset_card_disjiUnion`,
  `Finset.card_powerset`
-/

namespace SubsetCountPascal

open Multiset Finset

-- ===========================================================================
-- Part I.  Fix an element  →  Pascal's recurrence
-- ===========================================================================

/-- **Structural decomposition (multisets).** The `(k+1)`-submultisets of
    `a ::ₘ s` are exactly the `(k+1)`-submultisets of `s` together with the
    image, under `cons a`, of the `k`-submultisets of `s`.

    This is `Multiset.powersetCard_cons` restated under the names used in this
    file; it is the entire combinatorial content of Pascal's recurrence. -/
theorem powersetCard_succ_cons {α : Type*} (k : ℕ) (a : α) (s : Multiset α) :
    powersetCard (k + 1) (a ::ₘ s)
      = powersetCard (k + 1) s + (powersetCard k s).map (cons a) :=
  Multiset.powersetCard_cons k a s

/-- **Pascal's recurrence, combinatorially.**
    `(m+1).choose (k+1) = m.choose (k+1) + m.choose k`.

    We instantiate the structural decomposition at a concrete `m`-element
    multiset (`Multiset.range m`, with the fresh element `m` consed on) and take
    cardinalities. The `+ map (cons a)` summand contributes `m.choose k` because
    `cons a` is injective, so `card (map (cons a) X) = card X`. No appeal to the
    recursive definition of `choose` is made. -/
theorem choose_succ_succ_comb (m k : ℕ) :
    (m + 1).choose (k + 1) = m.choose (k + 1) + m.choose k := by
  have hcard := congrArg Multiset.card
    (powersetCard_succ_cons k m (Multiset.range m))
  simp only [Multiset.card_powersetCard, Multiset.card_cons, Multiset.card_range,
    Multiset.card_add, Multiset.card_map] at hcard
  exact hcard

/-- **Pascal's recurrence via the Finset powerset.** The same identity, now read
    off the honest set-theoretic partition of the `(k+1)`-subsets of
    `insert x s`: those avoiding `x` (a disjoint copy of the `(k+1)`-subsets of
    `s`) and those containing `x` (the image, under the *injective* map
    `insert x`, of the `k`-subsets of `s`). -/
theorem choose_succ_succ_finset {α : Type*} [DecidableEq α]
    {x : α} {s : Finset α} (hx : x ∉ s) (k : ℕ) :
    (s.card + 1).choose (k + 1) = s.card.choose (k + 1) + s.card.choose k := by
  -- cardinality of `insert x s`
  have hins : (insert x s).card = s.card + 1 := Finset.card_insert_of_notMem hx
  -- the two layers are disjoint: one consists of subsets avoiding `x`, the other
  -- of subsets containing `x`.
  have hdisj : Disjoint (s.powersetCard (k + 1))
      ((s.powersetCard k).image (insert x)) := by
    rw [Finset.disjoint_left]
    rintro t ht htim
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htim
    -- `t ⊆ s` forces `x ∉ t`, but `t = insert x u` forces `x ∈ t`.
    exact hx (ht.1 (Finset.mem_insert_self x u))
  -- `insert x` is injective on the `k`-subsets of `s` (all avoid `x`).
  have hinj : Set.InjOn (insert x) (s.powersetCard k : Set (Finset α)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_powersetCard] at ha hb
    have hxa : x ∉ a := fun h => hx (ha.1 h)
    have hxb : x ∉ b := fun h => hx (hb.1 h)
    have := congrArg (Finset.erase · x) hab
    simpa [Finset.erase_insert hxa, Finset.erase_insert hxb] using this
  have hcard := congrArg Finset.card
    (Finset.powersetCard_succ_insert hx k)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_powersetCard,
      Finset.card_powersetCard, Finset.card_image_of_injOn hinj,
      Finset.card_powersetCard, hins] at hcard
  exact hcard

/-- The disjoint-partition statement behind `choose_succ_succ_finset`, isolated
    as a structural fact: the `(k+1)`-subsets of `insert x s` partition into the
    `(k+1)`-subsets of `s` and the `x`-augmented `k`-subsets of `s`. -/
theorem powersetCard_insert_decomp {α : Type*} [DecidableEq α]
    {x : α} {s : Finset α} (hx : x ∉ s) (k : ℕ) :
    (insert x s).powersetCard (k + 1)
      = s.powersetCard (k + 1) ∪ (s.powersetCard k).image (insert x) :=
  Finset.powersetCard_succ_insert hx k

-- ===========================================================================
-- Part II.  Fix the size  →  row sum  ∑ choose = 2^n
-- ===========================================================================

/-- **Row-sum identity, combinatorially.** `∑ k ∈ range (m+1), m.choose k = 2^m`.

    The powerset of an `m`-element set is the *disjoint* union of its size-`k`
    layers for `k = 0, …, m` (`Finset.powerset_card_disjiUnion`). Counting the
    left side directly gives `2^m` (`Finset.card_powerset`); counting the right
    side layer-by-layer gives `∑ k, m.choose k` (`Finset.card_powersetCard`).
    Equality of the two counts is the identity. -/
theorem sum_choose_eq_two_pow_comb {α : Type*} (s : Finset α) :
    (∑ k ∈ Finset.range (s.card + 1), s.card.choose k) = 2 ^ s.card := by
  have hpow := congrArg Finset.card (Finset.powerset_card_disjiUnion s)
  rw [Finset.card_powerset, Finset.card_disjiUnion] at hpow
  simp only [Finset.card_powersetCard] at hpow
  exact hpow.symm

/-- The same row sum stated purely arithmetically (for any `m : ℕ`), obtained by
    evaluating `sum_choose_eq_two_pow_comb` at `Finset.range m`. -/
theorem sum_range_choose_comb (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), m.choose k) = 2 ^ m := by
  have := sum_choose_eq_two_pow_comb (Finset.range m)
  simpa [Finset.card_range] using this

-- ===========================================================================
-- Part III.  Sanity checks
-- ===========================================================================

-- Pascal's triangle entries, recomputed via the combinatorial recurrence.
example : (4 : ℕ).choose 2 = 3 + 3 := choose_succ_succ_comb 3 1
example : (5 : ℕ).choose 3 = 6 + 4 := choose_succ_succ_comb 4 2

-- Row sums.
example : (∑ k ∈ Finset.range 5, (4 : ℕ).choose k) = 16 := by decide

-- The recurrence really does rebuild the triangle from the two boundary edges.
example : (∀ k, (0 : ℕ).choose (k + 1) = 0) ∧ (∀ m : ℕ, m.choose 0 = 1) :=
  ⟨fun k => Nat.choose_zero_succ k, fun m => Nat.choose_zero_right m⟩

end SubsetCountPascal
