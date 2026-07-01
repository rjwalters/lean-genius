/-
# Fermat Two Squares OQ-06-OQ-02: Non-Uniqueness of the Forms `x² + d·y²`

The parent entry (`fermat-two-squares-oq-06`) studies the Brahmagupta–Fibonacci
identity for **sums of two squares** (`d = 1`, the Gaussian integers `ℤ[i]`) and
its non-uniqueness phenomenon: a product of two sums of two squares is a sum of
two squares in *two* essentially different ways.  A sibling entry
(`fermat-two-squares-oq-07`) records that the general composition identity
`(a² + N·b²)(c² + N·e²) = X² + N·Y²` holds for every `N` (multiplicativity of the
norm form of `ℤ[√(−N)]`), but demonstrates the two-representation phenomenon only
at `N = 1`.

This entry answers the parent's open question

> *Does the Gaussian-integer derivation generalize to other norm-Euclidean rings
> `ℤ[√(−d)]` to produce analogous composition identities and non-uniqueness
> results for the forms `x² + d·y²`?*

**affirmatively for the non-uniqueness half**, for *every* `d ≠ 0`.  The key
observation is cleaner than in the symmetric case `d = 1`: because `x² + d·y²`
is **not** symmetric in `x` and `y` when `d ≠ 1`, a representation is an ordered
pair `(x, y)` (up to signs), so two representations are "the same" only if their
`x`-coordinates and `y`-coordinates agree up to sign.  We show the two
Brahmagupta forms *already differ in their `x`-coordinate* as soon as all inputs
are nonzero — the difference of the two squared `x`-coordinates is `4·d·(ac)(be)`,
which is nonzero whenever `d, a, b, c, e ≠ 0`.  No positivity or ordering
hypotheses are needed.

The concrete witnesses are the norm-Euclidean rings after `ℤ[i]`:

* `d = 2` (`ℤ[√−2]`, norm-Euclidean): `33 = 3 · 11 = 1² + 2·4² = 5² + 2·2²`.
* `d = 3` (`ℤ[√−3]`): `28 = 4 · 7 = 1² + 3·3² = 5² + 3·1²`.

## Main results

* `brahmagupta_gen_form1`, `brahmagupta_gen_form2` — the two sign-forms of the
  general composition identity `(a² + N·b²)(c² + N·e²) = X² + N·Y²`, over any
  commutative ring (the engine; the `N = 1` symmetric case is the parent's).
* `xcoord_sq_ne` — **headline lemma**: for `N ≠ 0` and nonzero `a, b, c, e`, the
  two forms' `x`-coordinates satisfy `(ac − N·be)² ≠ (ac + N·be)²`.
* `two_distinct_representations_gen` — the two forms are essentially distinct
  representations of the product for every `N ≠ 0`.
* `product_two_representations` — packages the two identities with distinctness.
* `thirtyThree_two_ways`, `twentyEight_two_ways` — concrete witnesses at `d = 2`
  and `d = 3`, both arising from the composition of two representable numbers.

The number-theoretic refinement — *which* primes `x² + d·y²` represents (a
class-number question, easy only for `d ∈ {1, 2, 3}`) — is left as a follow-up.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

import Mathlib

namespace FermatTwoSquaresOQ06OQ02

/-! ## The two Brahmagupta forms for `x² + N·y²`

These are the engine.  For `N = 1` they reduce to the Brahmagupta–Fibonacci
forms of the parent entry; the general `N` composition identity is the subject of
the sibling `fermat-two-squares-oq-07`.  We restate both sign-forms here for
self-containment, since the non-uniqueness argument compares them directly. -/

/-- **General Brahmagupta identity, first form.** The norm form `x² + N·y²` of
`ℤ[√(−N)]` is multiplicative; this is one of the two sign variants. -/
theorem brahmagupta_gen_form1 {R : Type*} [CommRing R] (N a b c e : R) :
    (a ^ 2 + N * b ^ 2) * (c ^ 2 + N * e ^ 2)
      = (a * c - N * b * e) ^ 2 + N * (a * e + b * c) ^ 2 := by
  ring

/-- **General Brahmagupta identity, second form** (the other sign variant). -/
theorem brahmagupta_gen_form2 {R : Type*} [CommRing R] (N a b c e : R) :
    (a ^ 2 + N * b ^ 2) * (c ^ 2 + N * e ^ 2)
      = (a * c + N * b * e) ^ 2 + N * (a * e - b * c) ^ 2 := by
  ring

/-! ## Non-uniqueness for every `d ≠ 0` -/

/-- **Headline lemma.** The `x`-coordinates of the two Brahmagupta forms differ
(even as squares) whenever `N` and all four inputs are nonzero.  The proof is a
one-line identity: `(ac + N·be)² − (ac − N·be)² = 4·(N·(ac)·(be))`, and the
right-hand side is a product of nonzero integers. -/
theorem xcoord_sq_ne {N a b c e : ℤ}
    (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) :
    (a * c - N * b * e) ^ 2 ≠ (a * c + N * b * e) ^ 2 := by
  intro h
  have hkey : (a * c + N * b * e) ^ 2 - (a * c - N * b * e) ^ 2
      = 4 * (N * (a * c) * (b * e)) := by ring
  rw [h, sub_self] at hkey
  -- `hkey : 0 = 4 * (N * (a*c) * (b*e))`
  have hprod : N * (a * c) * (b * e) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hN (mul_ne_zero ha hc)) (mul_ne_zero hb he)
  have hz : (4 : ℤ) * (N * (a * c) * (b * e)) = 0 := hkey.symm
  rcases mul_eq_zero.mp hz with h4 | ht
  · norm_num at h4
  · exact hprod ht

/-- **Non-uniqueness for `x² + N·y²`, `N ≠ 0`.** For nonzero inputs, the two
Brahmagupta forms are *essentially distinct* representations of the product:
since `x² + N·y²` is not symmetric in `x, y` for `N ≠ 1`, two representations
coincide only when their `x`- and `y`-coordinates agree up to sign, and here the
`x`-coordinates already disagree. -/
theorem two_distinct_representations_gen {N a b c e : ℤ}
    (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) :
    ¬ ((a * c - N * b * e) ^ 2 = (a * c + N * b * e) ^ 2 ∧
       (a * e + b * c) ^ 2 = (a * e - b * c) ^ 2) := by
  rintro ⟨h1, _⟩
  exact xcoord_sq_ne hN ha hb hc he h1

/-- **The two representations, packaged.** The product `(a² + N·b²)(c² + N·e²)`
is written as `X² + N·Y²` in two ways whose `x`-coordinates have distinct
squares, hence are essentially different representations. -/
theorem product_two_representations {N a b c e : ℤ}
    (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) :
    (a ^ 2 + N * b ^ 2) * (c ^ 2 + N * e ^ 2)
        = (a * c - N * b * e) ^ 2 + N * (a * e + b * c) ^ 2
      ∧ (a ^ 2 + N * b ^ 2) * (c ^ 2 + N * e ^ 2)
        = (a * c + N * b * e) ^ 2 + N * (a * e - b * c) ^ 2
      ∧ (a * c - N * b * e) ^ 2 ≠ (a * c + N * b * e) ^ 2 :=
  ⟨brahmagupta_gen_form1 N a b c e, brahmagupta_gen_form2 N a b c e,
    xcoord_sq_ne hN ha hb hc he⟩

/-! ## Concrete witnesses in the norm-Euclidean rings `ℤ[√−2]` and `ℤ[√−3]` -/

/-- **`d = 2` witness** (the ring `ℤ[√−2]`, norm-Euclidean like `ℤ[i]`).
Composing `3 = 1² + 2·1²` and `11 = 3² + 2·1²` via the two forms gives
`33 = 3 · 11 = 1² + 2·4² = 5² + 2·2²`, two essentially different representations
by `x² + 2·y²` (the `x`-coordinates `1` and `5` have distinct squares). -/
theorem thirtyThree_two_ways :
    (33 : ℤ) = 1 ^ 2 + 2 * 4 ^ 2 ∧ (33 : ℤ) = 5 ^ 2 + 2 * 2 ^ 2
      ∧ (1 : ℤ) ^ 2 ≠ (5 : ℤ) ^ 2 := by
  norm_num

/-- The `d = 2` witness arises from `product_two_representations` with
`N = 2, a = 1, b = 1, c = 3, e = 1` (representations of `3` and `11`). -/
theorem thirtyThree_from_composition :
    ((1 : ℤ) ^ 2 + 2 * 1 ^ 2) * (3 ^ 2 + 2 * 1 ^ 2)
        = (1 * 3 - 2 * 1 * 1) ^ 2 + 2 * (1 * 1 + 1 * 3) ^ 2
      ∧ ((1 : ℤ) ^ 2 + 2 * 1 ^ 2) * (3 ^ 2 + 2 * 1 ^ 2)
        = (1 * 3 + 2 * 1 * 1) ^ 2 + 2 * (1 * 1 - 1 * 3) ^ 2 :=
  ⟨brahmagupta_gen_form1 2 1 1 3 1, brahmagupta_gen_form2 2 1 1 3 1⟩

/-- **`d = 3` witness** (the ring `ℤ[√−3]`).
Composing `4 = 1² + 3·1²` and `7 = 2² + 3·1²` gives
`28 = 4 · 7 = 1² + 3·3² = 5² + 3·1²`, two essentially different representations
by `x² + 3·y²`. -/
theorem twentyEight_two_ways :
    (28 : ℤ) = 1 ^ 2 + 3 * 3 ^ 2 ∧ (28 : ℤ) = 5 ^ 2 + 3 * 1 ^ 2
      ∧ (1 : ℤ) ^ 2 ≠ (5 : ℤ) ^ 2 := by
  norm_num

end FermatTwoSquaresOQ06OQ02
