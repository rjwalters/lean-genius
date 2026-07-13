# Research State: bertrands-postulate-oq-01

## Current State
**Phase**: OBSERVE (S1 — first directory-level research state for this slug; documents existing Lean axiomatization of Cramér's Conjecture and its implications chain)
**Path**: full
**Since**: 2026-04-22T12:51:58Z (initial pool entry; 7 weeks idle prior to S1)
**Last Updated**: 2026-06-10 (S1 OBSERVE: create research directory, audit existing Lean axiom chain, recommend `blocked` status; researcher-1)
**Iteration**: 2 (`src/data/research/problems/bertrands-postulate-oq-01.json` shows iteration 1 NEW; this S1 OBSERVE bumps to 2)

## Iter 1 / S1 OBSERVE (2026-06-10, researcher-1) — Directory creation + Cramér chain audit

This is the first agent visit to this slug since the pool entry was created 2026-04-22 (7 weeks ago). The slug was tracked only in `src/data/research/problems/bertrands-postulate-oq-01.json` (skeleton metadata); the directory `research/problems/bertrands-postulate-oq-01/` did not exist before this iteration. Creates the standard research state structure and documents the actual state of the work.

### Lean files referenced by this slug (already on `main`)

The conjecture and its implications chain are already axiomatized across the Bertrand family on `main`:

| File | LOC | Cramér-relevant content |
|------|----:|-------------------------|
| `proofs/Proofs/BertrandsPostulate.lean` | 151 | Foundation theorems (no Cramér) |
| `proofs/Proofs/BertrandsPostulateOQ03.lean` | 308 | `axiom cramer_conjecture` (line 183) — the OPEN conjecture itself; sibling axioms `bhp_short_interval` (Baker-Harman-Pintz 2001) and `legendre_conjecture` (also OPEN) |
| `proofs/Proofs/BertrandsPostulateOQ03OQ04.lean` | 357 | Prime gap framework |
| `proofs/Proofs/BertrandsPostulateOQ03OQ04OQ01.lean` | 257 | `axiom cramer_implies_nextPrime_bound` (line 146 — analytic NT bridge); `cramer_implies_primeGapConjecture_eventually` (line 166 — PROVED from Cramér); `cramer_implies_primeGapConjecture` (line 194 — PROVED); `cramer_hierarchy` (line 243 — PROVED, the structural chain) |
| `proofs/Proofs/BertrandsPostulateOQ03OQ04OQ03.lean` | 213 | Further consequences |
| `proofs/Proofs/BertrandsPostulateOQ03OQ04Aristotle.lean` | 124 | Aristotle companion for the OQ-03 family |

### Cramér's Conjecture statement (axiomatized)

`axiom cramer_conjecture : ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ≤ C * (Real.log (Nat.nth Nat.Prime n)) ^ 2`

This is the standard "$p_{n+1} - p_n = O((\log p_n)^2)$" formulation. The docstring on the axiom (line 175–182 of `BertrandsPostulateOQ03.lean`) correctly labels this as an **OPEN problem** — Cramér 1936 proved it under RH; unconditionally only Bertrand-style bounds (Baker-Harman-Pintz: gaps $\leq x^{0.525}$) are known.

### What's PROVED from `cramer_conjecture` (the implications chain)

`BertrandsPostulateOQ03OQ04OQ01.lean` lines 166–252 derive the standard consequences:

1. **`cramer_implies_primeGapConjecture_eventually ε hε`**: For any $\epsilon > 0$, Cramér implies "eventually, $\exists$ prime in $[x, x + x^\epsilon]$" (i.e., positive-exponent gap bounds follow from Cramér's logarithmic bound — since $\log^2 x = o(x^\epsilon)$ for any $\epsilon > 0$). 
2. **`cramer_implies_primeGapConjecture ε hε`**: The same statement uniformly in $x$, via combining the eventual case with `bhp_short_interval` (Baker-Harman-Pintz) for the small-$x$ case.
3. **`cramer_hierarchy`**: Documents the strict hierarchy `Cramér ⟹ PrimeGapConjecture(ε)` for all ε > 0, and the `existence_is_weaker_than_density` comparison.

The bridge axiom `cramer_implies_nextPrime_bound` (line 146) packages the statement "Cramér + Mathlib's `Nat.nth Nat.Prime` predicate ↔ `nextPrime`-indexed bound". The docstring explains why this is itself an axiom: "Formalizing the nth-prime index n as a function of x requires Mathlib's `Nat.nth Nat.Prime` predicate combined with the analytic estimate that `Nat.nth Nat.Prime n ≈ n * log n`" — i.e., this is the PNT bridge, also not in base Mathlib v4.26.0.

### Honest assessment: this slug is structurally COMPLETE

The slug `bertrands-postulate-oq-01` was framed as "Cramér's Conjecture: Prime Gaps Bounded by O((log p)²)". The candidate-pool notes describe its purpose as: "Open conjecture linked to six Bertrand-family Lean files; the Cramer implication file is now represented in metadata."

What is the maximally-meaningful Lean work an agent can do here?

1. **The conjecture itself is OPEN.** Removing the `cramer_conjecture` axiom requires actually proving Cramér's conjecture, a problem unsolved since 1936 and probably as hard as RH. No agent can do this in any number of iterations.
2. **The implications chain is already proved** (4 theorems in `OQ03OQ04OQ01.lean`).
3. **The `cramer_implies_nextPrime_bound` bridge axiom** could in principle be eliminated by formalizing the PNT-derived `Nat.nth Nat.Prime n ≈ n log n` asymptotic. But this requires analytic number theory (Riemann zeta function, complex contour integration, Mertens' theorems, etc.) not present in base Mathlib v4.26.0. Eliminating it would be a substantial Mathlib upstream contribution.

So the structural work is done: the OPEN conjecture is properly axiomatized with a clear docstring labeling it OPEN, the implications are derived, and the bridge axiom is documented with its analytic-NT prerequisites.

### Recommendation: slug should be marked `blocked` (open conjecture + Mathlib gap)

Status `blocked` accurately reflects:
- The mathematical statement is OPEN (unsolved by humanity since 1936).
- The remaining Lean-side work (eliminating the PNT bridge axiom) is gated on Mathlib analytic NT primitives.

Slug should remain available for future enricher work (e.g., better cross-references to Mathlib `Nat.nth Nat.Prime`, links to the `bertrands-postulate` gallery entry, references to BHP literature), but not for researcher-led axiom elimination.

## Active Approach

None applicable — the conjecture is OPEN.

## Attempt Count

- Total attempts: 2 (initial NEW state 2026-04-22; this S1 OBSERVE 2026-06-10)
- Current approach attempts: 1 (audit-only)
- Approaches tried: 1 (literature audit — confirmed open status)

## Blockers

1. **Cramér's conjecture is OPEN.** No known proof in any forum, formal or informal.
2. **Mathlib v4.26.0 lacks analytic NT.** Prime Number Theorem, Riemann zeta function, Dirichlet series, Selberg-Erdős elementary PNT, zero density estimates — none in Mathlib core as of v4.26.0. (Some `Mathlib.NumberTheory.PrimeCounting` infrastructure exists but does not include the asymptotic `π(x) ~ x/log x`.)

## Next Action

**Slug should be marked `blocked` in the candidate pool.** This iteration's action is exactly that: bring the slug into standard tracking format + accurately mark its status.

Future agent-led work on this slug (if any) should be **enricher-style**: cross-references to Mathlib's `Nat.nth Nat.Prime`, citation links for BHP, RH, and the Cramér 1936 paper, gallery cross-references between `bertrands-postulate`, `bertrands-postulate-oq-03`, and the rest of the family. No researcher-led axiom elimination is feasible.
