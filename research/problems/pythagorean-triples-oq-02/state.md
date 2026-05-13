# Current State

**Phase**: COMPLETED
**Since**: 2026-05-13T12:44:13Z
**Iteration**: 1

## Outcome

Open Question `pythagorean-triples-oq-02` is **fully verified** in Lean.

> **OQ**: How does the Pythagorean triple formula generalize to Gaussian integers,
> where $a^2 + b^2 = c^2$ factors as $(a+bi)(a-bi) = c^2$?

The work formalizes the algebraic reason behind the classical parametric
formula: $(m^2 - n^2,\, 2mn,\, m^2 + n^2)$ is exactly the image of
$z = m + ni$ under the squaring map in $\mathbb{Z}[i]$, and the
Pythagorean identity falls out of $|z^2|^2 = |z|^4$.

## Lean Source

`proofs/Proofs/PythagoreanTriplesOQ02.lean` — 173 LOC, 14 theorems, 4 definitions.

| Field | Value |
|---|---|
| `axiom` declarations | 0 |
| Structure-encoded assumptions | 0 |
| Tactic `sorry` | 0 |
| Definition `sorry` | 0 |

Gallery `src/data/proofs/pythagorean-triples-oq-02/meta.json` records
`status: "verified"`, `badge: "original"`, `axiomCount: 0`, `sorries: 0`.

## Result Inventory

Six parts (definitions, core properties, Pythagorean connection,
Brahmagupta-Fibonacci, factoring perspective, examples):

- `gaussMul`, `gaussNorm`, `gaussConj`, `gaussSq` — explicit formulas on
  pairs $(a, b) \in \mathbb{Z} \times \mathbb{Z}$ (no typeclass machinery).
- `norm_multiplicative` — $N(z_1 z_2) = N(z_1)\, N(z_2)$, proved by `ring`.
- `gaussSq_formula`, `mul_conj_eq_norm` — the squaring map and
  $z \cdot \bar z = N(z)$.
- `pythagorean_from_gaussian`, `gaussSq_pythagorean`,
  `gaussian_gives_pythagorean_triple` — connects to Mathlib's
  `PythagoreanTriple` predicate.
- `brahmagupta_fibonacci` — $(a^2+b^2)(c^2+d^2) = (ac-bd)^2 + (ad+bc)^2$.
- `pythagorean_triple_product` — closure of triples under Gaussian
  multiplication, via `nlinarith` + Brahmagupta-Fibonacci.
- `sum_sq_factors`, `triple_from_square_norm` — factoring perspective.
- Concrete examples: $(3,4,5)$, $(5,12,13)$, $(8,15,17)$.

## Mathlib Dependencies

- `PythagoreanTriple` (`Mathlib.NumberTheory.PythagoreanTriples`) —
  the predicate `a^2 + b^2 = c^2` used to interface the Gaussian
  squaring result with the rest of the library.

No further Mathlib infrastructure was required: most proofs reduce to
`ring`, with `nlinarith` doing the work for the product rule.

## Why "verified" rather than "axiomatized"

Per the axiom integrity policy: `axiomCount` must count both
`axiom` declarations and structure-encoded assumptions. This file
has neither — the proofs are pure polynomial identities and a single
`nlinarith` invocation, sitting on top of Mathlib's `PythagoreanTriple`.
Hence `status: "verified"` and `badge: "original"` are correct.

## Follow-Up Open Questions

Tracked in `src/data/proofs/pythagorean-triples-oq-02/meta.json`
under `conclusion.openQuestions`. The strongest candidates for
follow-up gallery entries:

1. **Primitive classification.** Formalize that every primitive
   Pythagorean triple has the form $(m^2-n^2,\, 2mn,\, m^2+n^2)$
   with $\gcd(m,n) = 1$, $m > n > 0$, $m \not\equiv n \pmod 2$.
   Uses unique factorization in $\mathbb{Z}[i]$.

2. **Fermat sum-of-two-squares.** A prime $p$ is $a^2 + b^2$ iff
   $p = 2$ or $p \equiv 1 \pmod 4$. This bridges to
   `elementary-quadratic-reciprocity` via the splitting behavior
   of primes in $\mathbb{Z}[i]$.

3. **Eisenstein generalization.** Transfer the Gaussian-integer
   pattern to $\mathbb{Z}[\omega]$ ($\omega = e^{2\pi i / 3}$) to
   handle Loeschian numbers $a^2 - ab + b^2$. The proof scaffold
   here would carry over directly.

These are forward levers, not deficiencies of the present
formalization.

## Active Approach

None — work complete.

## Blockers

None.

## Next Action

None. Future sessions on `pythagorean-triples-oq-02` should re-route
to one of the follow-up open questions above (each warrants its own
slug) rather than re-opening this slug.

## Status Drift Resolved By This Sync

Prior state (March 2026 seeker-init scaffold):

- `phase: "OBSERVE"`, `status: "active"`, `currentState.phase: "OBSERVE"` —
  inconsistent with `knowledge.progressSummary` (already `"COMPLETED:
  Fully verified..."`) and with the gallery `meta.status: "verified"`.
- `currentState.focus`: "Initial problem understanding..." — generic
  seeker scaffold, not actual state.
- `leanFiles[].lineCount` for `PythagoreanTriplesOQ02.lean`: 174 vs
  actual 173 (single-line drift).
- No `research/problems/pythagorean-triples-oq-02/state.md` file.

This PR brings the three sources of truth (research JSON, state.md,
gallery meta) into alignment. The companion Lean files
(`PythagoreanTriples.lean`, `PythagoreanTriplesOQ01.lean`,
`PythagoreanTriplesOQ01Aristotle.lean`) also have minor 1-line
`lineCount` drifts in this JSON, but they belong to sibling slugs and
are out of scope here — separate audit-sync if needed.
