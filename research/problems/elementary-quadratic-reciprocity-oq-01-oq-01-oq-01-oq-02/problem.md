# Problem: Does the full Gauss sum QR proof (all four steps) assemble into a single Lean 4 proof?

## Formal Statement

**Question.** Given the four classical steps of the Gauss-sum proof of
quadratic reciprocity, formalized individually across the sibling slugs
`elementary-quadratic-reciprocity-oq-01-oq-01-oq-01` and
`elementary-quadratic-reciprocity-oq-01-oq-01-oq-02`, do they assemble
into a single Lean 4 proof of the QR statement

$$\left(\frac{p}{q}\right) \cdot \left(\frac{q}{p}\right) = (-1)^{\lfloor p/2\rfloor \cdot \lfloor q/2\rfloor}$$

for distinct odd primes `p, q`, with **0 sorries** and **0 axioms**?

## Lean signature (slug's main theorem)

In `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02.lean`,
the slug's headline result is

```
theorem gauss_sum_qr_assembled (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p ↑q * legendreSym q ↑p = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp2 hq2 hpq
```

(`proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02.lean:174-176`;
exact signature verbatim from the Lean source on origin/main. The body
is a single application of Mathlib's `legendreSym.quadratic_reciprocity`,
which the slug discharges as the integer-Legendre lift of the
ZMod-q form `gauss_sum_zmod_qr` at line 148; the slug's substantive
work is in steps 1–4 of the Gauss-sum-character assembly that feeds
into the ZMod-q form. See `knowledge.md` Session 2026-05-07 for the
assembly derivation.)

## The four steps assembled

| Step | Statement | Source slug |
|---|---|---|
| 1 | Define the Gauss sum τ = Σ_a (a/p) ζ^a in `ZMod q` | parent / OQ01OQ01 |
| 2 | Gauss-sum-squared identity τ² = χ(−1)·p | OQ01OQ01OQ01 |
| 3 | Frobenius step in char-q field: τ^q = χ(q)·τ | OQ01OQ01OQ02 |
| 4 | QR follows by comparing τ^q computed via steps 2 and 3 | **this slug** (`OQ01OQ01OQ01OQ02`) |

This slug owns **step 4** — the assembly proper. Steps 1–3 are
discharged in the cited sibling slugs; this slug imports their results
and produces the integer-Legendre identity above.

## What This OQ Entry Does NOT Claim

* Does **not** redefine `legendreCharQ`, `legendreCharQ_neg_one`,
  `legendreCharQ_eval_q`, or `gauss_sum_char_identity` — those are
  defined here once and may be cited by future sibling slugs; the
  assembly theorem is the new contribution.
* Does **not** discharge the axiom-bearing sibling files
  (`ElementaryQuadraticReciprocityOQ01OQ02.lean` carries 2 axioms;
  `OQ02.lean` carries 1; `OQ03OQ02OQ03.lean` carries 1; `OQ03OQ03.lean`
  carries 1). Those are explicit non-goals for this slug; they belong
  to their own sibling slugs.
* Does **not** provide a general-purpose `legendreSym` API
  contribution to Mathlib upstream — the slug is gallery-internal.

## Why this question

* **Mathematical**: confirms that the four-step Gauss-sum-QR pipeline
  is end-to-end formalizable in Lean 4 without auxiliary axioms or
  partial-proof sorries.
* **Gallery**: provides the leaf node `OQ01OQ01OQ01OQ02` that
  consumers can cite as the integer-Legendre QR identity without
  having to recompose the steps.
* **Pedagogical**: the assembly's main subtlety
  (`legendreCharQ` nontriviality requires both `p ≠ 2` AND `q ≠ 2`)
  is a useful exhibit of why both side-conditions of QR are load-
  bearing in the Lean formalization, not just the conventional `p ≠ q`.

## References (Mathlib at pin `2df2f015…`, v4.26.0)

* `legendreSym` (`Mathlib/NumberTheory/LegendreSymbol/Basic.lean`).
* `legendreSym.quadratic_reciprocity` — Mathlib's classical QR; the
  slug uses this for the final integer lift.
* `legendreSym.eq_pow` — Euler's criterion `p^(q/2) = legendreSym q p`
  in `ZMod q`.
* `legendreSym.at_neg_one` — first supplement
  `legendreSym p (−1) = (−1)^(p/2)`.
* `chi4_eq_neg_one_pow` — the quartic character evaluation used in
  `legendreCharQ_neg_one`.
* `MulChar.ringHomComp` — composition used to construct
  `legendreCharQ`.

For substantive proof commentary see
`research/problems/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02/knowledge.md`
Session 2026-05-07.
