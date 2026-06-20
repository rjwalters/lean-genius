import Mathlib

/-
# Factor/Remainder Theorem OQ-05: A Polynomial Has at Most deg-Many Roots

## Research Problem: factor-remainder-theorem-oq-05

The headline corollary of the factor theorem over an integral domain: a nonzero
polynomial p has at most deg(p) roots. Equivalently, if a polynomial of degree < n
vanishes at n distinct points, it is the zero polynomial — which yields the
**uniqueness** half of polynomial interpolation.

## Mathematical Content

The factor theorem says (X − a) ∣ p ⟺ p(a) = 0. Iterating it over an *integral domain*
(where (X − a)(X − b) cannot vanish without one factor vanishing) bounds the number of
roots by the degree: this is `Polynomial.card_roots'`,

  card(roots p) ≤ natDegree p.

This file packages that bound and derives the two classical consequences:
1. **Distinct-roots bound**: any finite set of roots of a nonzero p has size ≤ deg(p)
   (`card_le_degree_of_subset_roots`).
2. **Interpolation uniqueness**: if p and q both have degree < |s| and agree on the |s|
   distinct points of a finset s, then p = q. The proof applies the root bound to
   p − q: it would have |s| roots but degree < |s|, so it must be 0.

The integral-domain hypothesis is essential — over ℤ/6ℤ the polynomial X² − X has the
four roots 0, 1, 3, 4 despite degree 2.

## References
- Descartes / classical algebra: a degree-n polynomial has at most n roots
- Mathlib: `Polynomial.card_roots'`, `Polynomial.card_le_degree_of_subset_roots`
-/

open Polynomial

namespace FactorRemainderTheoremOQ05

variable {R : Type*} [CommRing R] [IsDomain R]

/-! ## Part I: The root-count bound -/

/-- **At most deg-many roots.** Over an integral domain, the number of roots of any
    polynomial (counted with multiplicity) is at most its degree. -/
theorem card_roots_le_natDegree (p : R[X]) :
    Multiset.card p.roots ≤ p.natDegree :=
  Polynomial.card_roots' p

/-- Degree-valued form for nonzero p: `card(roots p) ≤ degree p` in `WithBot ℕ`. -/
theorem card_roots_le_degree {p : R[X]} (hp : p ≠ 0) :
    (Multiset.card p.roots : WithBot ℕ) ≤ p.degree :=
  Polynomial.card_roots hp

/-! ## Part II: Distinct roots are bounded by the degree -/

/-- Any finite set of points at which a **nonzero** p vanishes has at most deg(p)
    elements. (Distinct-roots form, ignoring multiplicity.) -/
theorem card_roots_finset_le_natDegree {p : R[X]} (hp : p ≠ 0) {Z : Finset R}
    (hZ : ∀ x ∈ Z, p.eval x = 0) : Z.card ≤ p.natDegree := by
  apply card_le_degree_of_subset_roots
  intro x hx
  rw [Finset.mem_val] at hx
  exact (mem_roots' (p := p)).mpr ⟨hp, hZ x hx⟩

/-! ## Part III: Interpolation uniqueness -/

/-- **Uniqueness of interpolation.** If `p` and `q` both have degree `< |s|` and agree on
    the `|s|` distinct points of `s`, then `p = q`.

    Proof: `p - q` vanishes on all of `s` (that is `|s|` distinct roots) but has degree
    `≤ max(deg p, deg q) < |s|`; by the root bound it must be the zero polynomial. -/
theorem eq_of_natDegree_lt_card_of_eval_eq {p q : R[X]} {s : Finset R}
    (hp : p.natDegree < s.card) (hq : q.natDegree < s.card)
    (heval : ∀ x ∈ s, p.eval x = q.eval x) : p = q := by
  by_contra hne
  have hd : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hroots : ∀ x ∈ s, (p - q).eval x = 0 := by
    intro x hx; rw [eval_sub, heval x hx, sub_self]
  have hcard : s.card ≤ (p - q).natDegree :=
    card_roots_finset_le_natDegree hd hroots
  have hdeg : (p - q).natDegree < s.card :=
    lt_of_le_of_lt (natDegree_sub_le p q) (max_lt hp hq)
  omega

/-- A polynomial of degree `< |s|` that vanishes on all `|s|` points of `s` is zero. -/
theorem eq_zero_of_natDegree_lt_card_of_eval_zero {p : R[X]} {s : Finset R}
    (hp : p.natDegree < s.card) (heval : ∀ x ∈ s, p.eval x = 0) : p = 0 := by
  apply eq_of_natDegree_lt_card_of_eval_eq hp
  · simpa using lt_of_le_of_lt (Nat.zero_le _) hp
  · intro x hx; simpa using heval x hx

/-! ## Part IV: Verified examples -/

-- Over ℚ, X² − 1 has exactly the two roots {1, -1}, matching its degree 2.
example : (Multiset.card (X ^ 2 - 1 : ℚ[X]).roots) ≤ (X ^ 2 - 1 : ℚ[X]).natDegree :=
  card_roots_le_natDegree _

-- Two polynomials of degree < 2 agreeing at the two points {0, 1} are equal.
example (p q : ℚ[X]) (hp : p.natDegree < 2) (hq : q.natDegree < 2)
    (h0 : p.eval 0 = q.eval 0) (h1 : p.eval 1 = q.eval 1) : p = q := by
  refine eq_of_natDegree_lt_card_of_eval_eq (s := {0, 1}) ?_ ?_ ?_
  · simpa using hp
  · simpa using hq
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1

/-! ## Part V: Summary -/

/-- **Factor/Remainder OQ-05 Summary** (over an integral domain):
    (1) `card(roots p) ≤ deg(p)`;
    (2) any finite set of roots of nonzero p has size ≤ deg(p);
    (3) interpolation uniqueness: degree `< |s|` and agreement on `s` ⟹ equality. -/
theorem factor_remainder_oq05_summary (p q : R[X]) {s : Finset R}
    (hp : p.natDegree < s.card) (hq : q.natDegree < s.card)
    (heval : ∀ x ∈ s, p.eval x = q.eval x) :
    (Multiset.card p.roots ≤ p.natDegree) ∧ (p = q) :=
  ⟨card_roots_le_natDegree p, eq_of_natDegree_lt_card_of_eval_eq hp hq heval⟩

end FactorRemainderTheoremOQ05
