# polynomial-derivative-leibniz-oq-01

**Problem**: Leibniz product rule for formal polynomial derivatives
**Tier**: A · significance 7 · tractability 8
**Status**: SKIPPED — fully subsumed by Mathlib (no novel formalization target)

## Summary

The problem asks to formalize the Leibniz product rule
`D(f·g) = D(f)·g + f·D(g)` for the formal derivative on `R[X]`. A Mathlib
audit (2026-07-01) found that this statement **and every standard
generalization of it** are already present in Mathlib. There is no
theorem here that Mathlib lacks, so a gallery entry would be a trivial
one-line wrapper (`exact Polynomial.derivative_mul`) with no mathematical
novelty. Per the research honesty standards, this is documented as a skip
rather than presented as an "original verified" result.

## Session 2026-07-01 (Session 1) — Mathlib coverage audit

**Mode**: FRESH
**Outcome**: skipped (subsumed by Mathlib)

### What I did
Audited `Mathlib/Algebra/Polynomial/Derivative.lean`,
`Mathlib/Algebra/Polynomial/HasseDeriv.lean`,
`Mathlib/Algebra/Polynomial/Derivation.lean`, and
`Mathlib/RingTheory/Derivation/` for coverage of the polynomial Leibniz
product rule and its natural generalizations.

### Key findings — every angle is already in Mathlib
| Statement | Mathlib lemma | Location |
|-----------|---------------|----------|
| Binary Leibniz `D(fg)=Df·g+f·Dg` | `Polynomial.derivative_mul` | `Algebra/Polynomial/Derivative.lean:247` |
| Higher-order general Leibniz `D^[n](pq)=Σ C(n,k)·D^[n-k]p·D^[k]q` | `Polynomial.iterate_derivative_mul` | `.../Derivative.lean:350` |
| Hasse-derivative Leibniz `Dₖ(fg)=Σ_{i+j=k} Dᵢf·Dⱼg` | `Polynomial.hasseDeriv_mul` | `Algebra/Polynomial/HasseDeriv.lean:206` |
| Finite (multiset) product rule | `Polynomial.derivative_prod` | `.../Derivative.lean:537` |
| Chain rule `D(p∘q)=Dq·(Dp∘q)` | `Polynomial.derivative_comp` | `.../Derivative.lean:519` |
| Derivative packaged as an `R`-derivation | `Polynomial.derivative'` | `Algebra/Polynomial/Derivation.lean:34` |
| Uniqueness (derivations agreeing on X are equal) | `Polynomial.derivation_ext` | `.../Derivation.lean:54` |
| Universal property `A ≃ₗ Derivation R R[X] A` | `Polynomial.mkDerivationEquiv` | `.../Derivation.lean:83` |

### Pre-work value assessment
- **Value question** ("meaningfully closer to a complete proof?"): No — the
  target and all generalizations are already fully proved in Mathlib.
- **Build vs block**: N/A — nothing to build; infrastructure is complete.
- A gallery entry would be `theorem leibniz {f g : R[X]} : derivative (f*g) = ... := derivative_mul`,
  i.e. a rename. This violates the "do not describe trivial results as
  significant" honesty rule.

### The one genuine gap (recorded, not pursued)
The *combination* of higher-order and finite-product Leibniz — the
multinomial form
`derivative^[n] (∏ᵢ fᵢ) = Σ (multinomial coeff)·∏ᵢ derivative^[kᵢ] fᵢ`
— does not appear to be in Mathlib (`iterate_derivative_mul` covers two
factors; `derivative_prod` covers the first derivative of many factors,
but not their composition). This would be a *real* theorem, but it is a
substantial multinomial induction and is only tangential to the stated
"product rule" question. If a future Seeker wants a genuine target in this
area, the multinomial iterated-product Leibniz rule is the candidate — as
a fresh problem, not as this one.

### Recommendation
Mark `polynomial-derivative-leibniz-oq-01` as **skipped** permanently.
Do not re-select. (It was already `SEEKER-REVISIT: SKIPPED` once.)
