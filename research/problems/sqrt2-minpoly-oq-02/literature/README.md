# Literature for sqrt2-minpoly-oq-02

This directory contains:
- Related papers and their summaries
- Links to relevant Mathlib documentation
- References to similar problems and their solutions

## Related Gallery Proofs

- `sqrt2-minpoly`: Direct predecessor — proves minpoly ℚ √2 = X² - 2. Identical strategy.
- `sqrt2-irrational`: Irrationality certificate; degree > 1 minimal polynomial implies irrationality.
- `cube-root-2-irrational`: Related proof that ∛2 is irrational (minimal poly X³ - 2).

## Relevant Mathlib Modules

- `Mathlib.RingTheory.Eisenstein.Basic` — `Polynomial.irreducible_of_eisenstein_criterion`
- `Mathlib.FieldTheory.Minpoly.Basic` — `minpoly.eq_of_irreducible_of_monic`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow` for n^(1/k)
- `Mathlib.RingTheory.RootsOfUnity.Basic` — for the root witness evaluation

## External References

- Lang, *Algebra* §V.4: Eisenstein irreducibility criterion and pure extensions
- Stewart, *Galois Theory* Ch. 3: Minimal polynomials of radicals
