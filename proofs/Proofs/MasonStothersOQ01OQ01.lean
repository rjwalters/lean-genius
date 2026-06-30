import Mathlib
import Proofs.MasonStothersOQ01

/-
# Mason–Stothers via distinct roots: `deg(rad p) = #{distinct roots of p}`

The parent entry (`MasonStothersOQ01`) proves the polynomial ABC inequality in the
form `deg c < deg(rad(a·b·c))`, leaving the radical `rad(p)` as an algebraic black
box — the product of the *distinct* monic irreducible factors of `p`.  Over an
**algebraically closed field** every monic irreducible is linear (`X - α`), so the
degree of the radical is simply the number of distinct roots of `p`.

This file makes that translation precise:

  `(radical p).natDegree = p.roots.toFinset.card`,

the cardinality of the zero set of `p` in `k`.  Feeding it into the parent bound
turns the abstract inequality `deg c < deg(rad(a·b·c))` into the tangible
*distinct-roots* form

  `deg c < #{distinct roots of a·b·c}`,

which is the shape in which Mason–Stothers is actually applied (Fermat for
polynomials, Davenport's inequality): one counts roots, not factorisations.

## Proof outline

The argument splits into three independent facts, each valid over any field
(only the degree↔root-count step needs algebraic closure):

* `roots_toFinset_radical` — `radical p` and `p` have **the same set of roots**.
  For a fixed `a`, `α = a` is a root of `radical p` iff `X - C a ∣ radical p`,
  and `dvd_radical_iff_of_irreducible` (with `X - C a` irreducible) says this is
  equivalent to `X - C a ∣ p`, i.e. `a` is a root of `p`.  No closure needed.

* `nodup_roots_radical` — the roots of `radical p` are **distinct** (no
  multiplicity).  `radical p` is squarefree (`squarefree_radical`), so
  `(X - C a)² ∤ radical p`, hence `rootMultiplicity a (radical p) ≤ 1`, hence the
  root multiset has no repeats.  No closure needed.

* over an algebraically closed field `radical p` **splits**
  (`IsAlgClosed.splits`), so `natDegree = roots.card`
  (`Splits.natDegree_eq_card_roots`).

Combining: `deg(rad p) = #(rad p).roots = #(rad p).roots.toFinset =
#p.roots.toFinset`.  A `0`-axiom derivation from Mathlib's radical and root API.
-/

open Polynomial UniqueFactorizationMonoid

namespace MasonStothersOQ01OQ01

variable {k : Type*} [Field k] [DecidableEq k] {p : k[X]}

/-- **Same roots.** A field element `a` is a root of `radical p` exactly when it is
a root of `p`.  The radical strips multiplicities but keeps every distinct root:
`a` is a root iff `X - C a` divides, and `X - C a` (being irreducible) divides
`radical p` iff it divides `p` (`dvd_radical_iff_of_irreducible`). -/
theorem mem_roots_radical (hp : p ≠ 0) (a : k) :
    a ∈ (radical p).roots ↔ a ∈ p.roots := by
  rw [mem_roots', mem_roots', and_iff_right (radical_ne_zero), and_iff_right hp,
    ← dvd_iff_isRoot, ← dvd_iff_isRoot]
  exact dvd_radical_iff_of_irreducible (irreducible_X_sub_C a) hp

/-- **Same root set.** `radical p` and `p` have identical sets (finsets) of roots. -/
theorem roots_toFinset_radical (p : k[X]) :
    (radical p).roots.toFinset = p.roots.toFinset := by
  ext a
  by_cases hp : p = 0
  · subst hp; simp
  · simpa only [Multiset.mem_toFinset] using mem_roots_radical hp a

/-- **Distinct roots.** The roots of `radical p` carry no multiplicity: the root
multiset is `Nodup`.  Squarefreeness of `radical p` rules out `(X - C a)²` as a
factor, so every root multiplicity is at most one. -/
theorem nodup_roots_radical (p : k[X]) : (radical p).roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [count_roots, rootMultiplicity_le_iff radical_ne_zero a 1]
  intro hdvd
  rw [pow_succ, pow_one] at hdvd
  exact not_isUnit_X_sub_C a (squarefree_radical _ hdvd)

/-- **Radical degree = number of distinct roots (algebraically closed field).**

For a polynomial `p` over an algebraically closed field `k`,

  `deg(rad p) = #{distinct roots of p}  =  |p.roots.toFinset|`.

The radical degree is exactly the cardinality of the zero set of `p` in `k`.
Proof: `radical p` splits, so its degree equals the size of its root multiset;
that multiset is `Nodup` (radical is squarefree) and has the same underlying set
as `p`'s roots. -/
theorem natDegree_radical_eq_card_roots [IsAlgClosed k] (p : k[X]) :
    (radical p).natDegree = p.roots.toFinset.card := by
  rw [(IsAlgClosed.splits (radical p)).natDegree_eq_card_roots,
    ← roots_toFinset_radical p, Multiset.toFinset_card_of_nodup (nodup_roots_radical p)]

/-- **Mason–Stothers, distinct-roots form (characteristic-zero, algebraically
closed).**

For a coprime additive triple `a + b = c` of nonzero polynomials over an
algebraically closed field of characteristic zero, with `c` non-constant,

  `deg c < #{distinct roots of a·b·c}`.

This is the `abc`-inequality for polynomials stated as an explicit count of the
distinct roots of the product — the form used in the one-line proof of Fermat's
Last Theorem for polynomials.  It is `natDegree_lt_radical_charZero` from the
parent with the radical degree rewritten as the size of the zero set. -/
theorem natDegree_lt_card_roots_charZero [IsAlgClosed k] [CharZero k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b = c) (hcdeg : c.natDegree ≠ 0) :
    c.natDegree < (a * b * c).roots.toFinset.card := by
  have h := MasonStothersOQ01.natDegree_lt_radical_charZero ha hb hc hab hsum hcdeg
  rwa [natDegree_radical_eq_card_roots] at h

end MasonStothersOQ01OQ01
