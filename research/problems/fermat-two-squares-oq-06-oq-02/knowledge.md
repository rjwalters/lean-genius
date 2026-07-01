# fermat-two-squares-oq-06-oq-02: Non-Uniqueness of x² + d·y² for Every d

**Parent open question (fermat-two-squares-oq-06):** Does the Gaussian-integer
derivation of the non-uniqueness of two-square representations generalize to
other norm-Euclidean rings ℤ[√−d], producing analogous composition identities
and non-uniqueness results for the forms x² + d·y²?

## Summary

Answered **affirmatively for the non-uniqueness half, for every d ≠ 0.** The two
Brahmagupta sign-forms of the general composition identity
`(a²+d·b²)(c²+d·e²) = (ac ∓ d·be)² + d·(ae ± bc)²` always yield representations of
the product whose **x-coordinates have distinct squares**, hence essentially
distinct representations. The composition identity itself was already formalized
(sibling `fermat-two-squares-oq-07`, general N); the parent (`oq-06`) proved
non-uniqueness only for d = 1 (Gaussian, symmetric form).

## Session 2026-07-01 (Session 1) — FRESH

**Mode:** FRESH · **Outcome:** proof written; build verification pending
(fleet contention on shared lake config lock).

### Key mathematical insight
For d ≠ 1 the form x²+d·y² is **not symmetric** in x and y, so a representation is
an ordered pair (x, y) up to signs — two representations coincide only if BOTH
coordinates match up to sign. The two Brahmagupta x-coordinates ac ∓ d·be satisfy
`(ac+d·be)² − (ac−d·be)² = 4·d·(ac)(be) ≠ 0` whenever d, a, b, c, e are nonzero
(a product of nonzero integers, `mul_ne_zero`). So distinct x-coordinates already
certify distinct representations — **no positivity/ordering hypotheses needed**,
a strict simplification over the parent's d = 1 argument (which needs 0 < x,y,u,v
to defeat the swap symmetry of x²+y²).

### Built items
- `proofs/Proofs/FermatTwoSquaresOQ06OQ02.lean` (152 lines, 8 theorems, 0 defs,
  targets 0-axiom): `xcoord_sq_ne` (headline), `two_distinct_representations_gen`,
  `product_two_representations`, `brahmagupta_gen_form1/2`, plus concrete
  witnesses `thirtyThree_two_ways`/`thirtyThree_from_composition` (d=2, ℤ[√−2])
  and `twentyEight_two_ways` (d=3, ℤ[√−3]).

### Mathlib gaps
- No general Lucas/quadratic-form non-uniqueness machinery needed; result is pure
  `ring` + `mul_ne_zero` + `norm_num`. Self-contained over Mathlib.

### Next steps (arithmetic layer, deliberately left as follow-up)
- Characterize which primes p are represented by x²+d·y² for d ∈ {1,2,3,4,7}
  (class number one) via congruence conditions, and count essentially-distinct
  representations of products of such primes — the arithmetic refinement.
- Derive the d=2 non-uniqueness from unique factorization in the norm-Euclidean
  ring ℤ[√−2] (Zsqrtd.norm), paralleling the parent's Gaussian derivation.
