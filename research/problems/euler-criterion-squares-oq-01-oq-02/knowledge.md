# Euler's Criterion OQ-01-OQ-02 — Supplementary Laws of Quadratic Reciprocity

## Summary
Leaf of `euler-criterion-squares-oq-01` (Euler's criterion in Legendre-symbol form). Derives
the two supplementary laws of quadratic reciprocity for an odd prime `p`.

## Session 2026-06-24 (Session 1) — FRESH
**Mode**: FRESH | **Outcome**: completed (verified, 0-axiom)

### What I Did
- Built `Proofs/EulerCriterionSquaresOQ01OQ02.lean` (131 lines, 11 theorems, 0 defs).
- First supplementary law `(−1 | p) = (−1)^((p−1)/2)` derived **from the parent's Euler
  criterion** `legendreSym_eq_pow` (not from Mathlib's `at_neg_one`): both sides are ±1 and
  congruent mod p, lifted to equality via a reusable `intCast_inj_of_pm_one` bridge that uses
  the parent's `one_ne_neg_one`.
- Residue forms: `neg_one_isSquare_iff` (p%4=1), `two_isSquare_iff` (p%8∈{1,7}).
- Legendre-value dictionary: `legendreSym_neg_one_eq_one_iff`, `legendreSym_two_eq_one_iff`,
  `legendreSym_two_eq_neg_one_iff` (p%8∈{3,5}), case splits via omega from oddness of p.

### Key Findings
- The (−1) law is a genuine derivation from Euler's criterion; the (2) law packages Mathlib's
  Gauss-sum result `ZMod.exists_sq_eq_two_iff` (not re-derived).
- `omit [inst] in` must precede the docstring, not follow it (syntax error otherwise).
- `Nat.even_or_odd` (not `Int.even_or_odd`) for a ℕ exponent feeding `Even.neg_one_pow`.
- `ZMod.natCast_zmod_eq_zero_iff_dvd` is deprecated → `ZMod.natCast_eq_zero_iff`.

### Files
- proofs/Proofs/EulerCriterionSquaresOQ01OQ02.lean
- src/data/proofs/euler-criterion-squares-oq-01-oq-02/meta.json

### Next Steps
- Possible follow-up: full Gauss-lemma derivation of (2 | p) from Euler's criterion alone
  (currently leans on Mathlib's Gauss-sum), or (−2 | p) / (3 | p) supplementary values.
