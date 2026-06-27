# Knowledge Base: picks-theorem-oq-03-ext-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Hibi's palindromy theorem (1991): a lattice polytope is reflexive iff its
h*-vector is palindromic (h*_i = h*_{d-i}). The parent entry
`picks-theorem-oq-03-ext` verified this only on examples (octahedron (1,3,3,1),
cube, simplex). The goal here is the **general algebraic characterization** those
examples instantiate.

---

## Insights

- The algebraic core is dimension-free: palindromy of the h*-VECTOR is exactly
  self-reciprocity of the h*-POLYNOMIAL H(X) = Σ h_i X^i, i.e. `reflect d H = H`,
  where `Polynomial.reflect d` reverses coefficients via `revAt d`. Proved over an
  arbitrary commutative semiring — no fixed dimension, no Ehrhart machinery.
- Key Mathlib primitives: `Polynomial.reflect`, `coeff_reflect`, `revAt`,
  `revAt_le`, `revAt_eq_self_of_lt` (Mathlib.Algebra.Polynomial.Reverse). These
  were sufficient for the equivalence.
- Ehrhart–Macdonald reciprocity L°(n) = (-1)^d L(-n) together with the reflexive
  identity L°(n) = L(n-1) yields self-reciprocity of the h*-polynomial; once that
  is granted, palindromy is pure algebra. The bridge theorem
  `reflexive_hStar_palindromic` takes self-reciprocity as an explicit hypothesis,
  honest about what is assumed.
- The octahedron (1,3,3,1) is recovered as a corollary (both directions of the
  iff), confirming the abstraction is faithful.

## Built Items (final — VERIFIED, 0 sorries / 0 axioms)

- `reflect_eq_iff_palindromic` — main theorem, the algebraic heart of Hibi's
  criterion, general over any Semiring.
- `reflexive_hStar_palindromic` — reflexive ⟹ palindromic reduction step.
- `hStar_constant_eq_leading` — palindromic ⟹ h_0 = h_d (Gorenstein normalization).
- `coeff_hStarPoly` — coefficient formula for the h*-polynomial.
- `octaH_palindromic` / `octaH_self_reciprocal` / `octaH_normalization` — parent
  octahedron example recovered as corollaries.

Build verified: `./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ03ExtOQ02`
→ "Build completed successfully (7743 jobs)" (only deprecation/unused-var warnings).

---

## Dead Ends

- None recorded. The polynomial-reflection approach went through cleanly.

---

## Next Steps (future work, not blocking)

- Build minimal Ehrhart-series infrastructure (formal power series H/(1-t)^{d+1})
  to discharge the self-reciprocity hypothesis and obtain an unconditional
  reflexive ⟹ palindromic theorem.
- Prove the full biconditional reflexive ↔ palindromic once interior-point
  reciprocity L°(n) = L(n-1) is available in Mathlib.
