import Mathlib

/-
# Mason–Stothers: the additive `a + b = c` form and a clean characteristic-zero bound

Mathlib's `Mathlib/NumberTheory/FLT/MasonStothers.lean` proves the polynomial ABC
theorem `Polynomial.abc`: for nonzero coprime polynomials `a, b, c` over a field
with the **homogeneous** relation `a + b + c = 0`, either

  `max {deg a, deg b, deg c} + 1 ≤ deg (rad (a·b·c))`

or all three derivatives vanish (`a' = b' = c' = 0`).  The derivative-vanishing
escape clause is genuinely necessary in positive characteristic: e.g. over `𝔽_p`,
`Xᵖ + 1 = (X + 1)ᵖ` is a coprime relation whose factors have huge degree but tiny
radical, only avoided because every term is a `p`-th power with zero derivative.

This file packages two facts that Mathlib does **not** record directly:

* `mason_stothers_add` — the classical *inhomogeneous* statement in the form
  `a + b = c` (the way Mason–Stothers is almost always quoted), obtained from
  `Polynomial.abc` by feeding it `a + b + (-c) = 0` and using `radical_neg`,
  `natDegree_neg`, `derivative_neg` to translate back to `c`.

* `mason_stothers_charZero` — over a field of characteristic zero the escape
  clause collapses: `derivative p = 0 ⟺ p` is constant, so as soon as one of
  `a, b, c` is non-constant we get the unconditional degree bound

    `max {deg a, deg b, deg c} + 1 ≤ deg (rad (a·b·c))`.

From these we read off the headline inequality `deg c < deg (rad (a·b·c))` and a
rigidity corollary: in characteristic zero a coprime triple `a + b = c` whose
product has *few* distinct roots (`deg (rad (a·b·c)) ≤ deg c`) must be constant.
(`deg (rad p)` counts the number of distinct roots of `p` over an algebraically
closed field, so the rigidity statement is the usual "abc forces many distinct
roots" phenomenon.)

Everything is a 0-axiom derivation from Mathlib's `Polynomial.abc`.
-/

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

namespace MasonStothersOQ01

variable {k : Type*} [Field k] [DecidableEq k]

/-- **Mason–Stothers theorem, additive form `a + b = c`.**

For nonzero polynomials `a, b, c` over a field with `a` and `b` coprime and
`a + b = c`, either each of `a, b, c` has degree at least one less than the
number of distinct roots of `a·b·c` (i.e. `deg + 1 ≤ deg (rad (a·b·c))`), or all
three derivatives vanish.

This is `Polynomial.abc` rewritten for the inhomogeneous relation `a + b = c`
(rather than `a + b + c = 0`): apply it to the triple `a, b, -c`, then translate
`radical`, `natDegree` and `derivative` of `-c` back to `c`. -/
theorem mason_stothers_add {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b = c) :
    (a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
        b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
        c.natDegree + 1 ≤ (radical (a * b * c)).natDegree) ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  have hc' : (-c) ≠ 0 := neg_ne_zero.mpr hc
  have hsum' : a + b + (-c) = 0 := by rw [← hsum]; ring
  -- `radical (a * b * (-c)) = radical (a * b * c)` since the product only changes by a unit.
  have hrad : radical (a * b * (-c)) = radical (a * b * c) := by
    rw [show a * b * (-c) = -(a * b * c) by ring, radical_neg]
  have key := Polynomial.abc ha hb hc' hab hsum'
  rw [hrad] at key
  rcases key with ⟨h1, h2, h3⟩ | ⟨g1, g2, g3⟩
  · -- `natDegree (-c) = natDegree c`
    rw [Polynomial.natDegree_neg] at h3
    exact Or.inl ⟨h1, h2, h3⟩
  · -- `derivative (-c) = 0 ↔ derivative c = 0`
    rw [derivative_neg, neg_eq_zero] at g3
    exact Or.inr ⟨g1, g2, g3⟩

/-- **Mason–Stothers in characteristic zero.**

Over a field of characteristic zero the derivative-vanishing escape clause cannot
occur for a non-constant polynomial (`derivative p = 0 ⟹ p` constant).  Hence if
`a + b = c` is a coprime triple of nonzero polynomials with at least one of them
non-constant, the degree bound holds unconditionally for all three. -/
theorem mason_stothers_charZero [CharZero k] {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : IsCoprime a b) (hsum : a + b = c)
    (hnontrivial : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0) :
    a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  rcases mason_stothers_add ha hb hc hab hsum with h | ⟨ga, gb, gc⟩
  · exact h
  · -- the escape clause forces every factor to be constant, contradicting `hnontrivial`
    exfalso
    have da : a.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero ga
    have db : b.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero gb
    have dc : c.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero gc
    rcases hnontrivial with h | h | h
    · exact h da
    · exact h db
    · exact h dc

/-- **Headline ABC degree inequality (characteristic zero).**

If `a + b = c` is a coprime triple of nonzero polynomials over a characteristic-zero
field and `c` is non-constant, then `deg c < deg (rad (a·b·c))`: the degree of `c`
is strictly smaller than the number of distinct roots of the product `a·b·c`. -/
theorem natDegree_lt_radical_charZero [CharZero k] {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : IsCoprime a b) (hsum : a + b = c) (hcdeg : c.natDegree ≠ 0) :
    c.natDegree < (radical (a * b * c)).natDegree := by
  have h := mason_stothers_charZero ha hb hc hab hsum (Or.inr (Or.inr hcdeg))
  -- `c.natDegree + 1 ≤ …` is definitionally `c.natDegree < …`
  exact h.2.2

/-- **Rigidity corollary.**

In characteristic zero, a coprime additive triple `a + b = c` whose product has
*few* distinct roots (`deg (rad (a·b·c)) ≤ deg c`) must be totally degenerate:
`a, b, c` are all constant.  Equivalently, any genuinely non-constant coprime
relation `a + b = c` forces `a·b·c` to have strictly more than `deg c` distinct
roots. -/
theorem mason_stothers_rigidity [CharZero k] {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : IsCoprime a b) (hsum : a + b = c)
    (hfew : (radical (a * b * c)).natDegree ≤ c.natDegree) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  rcases mason_stothers_add ha hb hc hab hsum with ⟨_, _, h3⟩ | ⟨ga, gb, gc⟩
  · -- `c.natDegree + 1 ≤ deg rad ≤ c.natDegree` is impossible
    exact absurd (h3.trans hfew) (by omega)
  · exact ⟨natDegree_eq_zero_of_derivative_eq_zero ga,
      natDegree_eq_zero_of_derivative_eq_zero gb,
      natDegree_eq_zero_of_derivative_eq_zero gc⟩

end MasonStothersOQ01
