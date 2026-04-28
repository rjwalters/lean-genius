# Current State

**Phase**: MATURE-AXIOMATIZED
**Since**: 2026-04-27
**Iteration**: 2

## Current Focus

Open conjecture is fully formalized. No further unconditional progress is possible
without resolving the existence of the limit constant $c$, which is the open question
itself.

## Active Approach

Maintenance/reconciliation only. The Lean formalization
(`proofs/Proofs/Erdos390Problem.lean`, 538 lines) captures:

1. `ValidFactorization n` structure (sorted factors $> n$, product $= n!$)
2. `factorizationMax n` as the noncomputable `sInf` of maximum factors
3. Concrete witnesses with tight upper/lower bounds for $n \in \{3, 4, 5, 6, 7, 8\}$:
   - $f(3) = 6$, $f(4) = 24$, $f(5) = 12$, $f(6) = 10$, $f(7) = 20$, $f(8) = 16$
4. Structural lemmas: $f(n) > n$, $f(n) \leq n!$ for $n \geq 3$
5. The Erdős–Guy–Selfridge (1982) two-sided bound, axiomatized as
   `factorizationMax_asymptotic`: $\exists C, c > 0$ such that for $n \geq 10$,
   $c \cdot n/\log n \leq f(n) - 2n \leq C \cdot n/\log n$
6. The open conjecture stated as `ErdosProblem390 : Prop` using `Filter.Tendsto`

## Blockers

- **Open mathematical conjecture**: The existence and value of the limit constant
  $c = \lim_{n \to \infty} (f(n) - 2n) \log n / n$ is unresolved in the literature.
  No new mathematical insight is available to push this beyond the EGS asymptotic
  bound, which is itself axiomatized rather than derived.

## Next Action

Hold at `axiomatized` status. Possible future enrichment (not blocking):

- Extend the witness table to $n = 9, 10, 11, 12$ via OEIS A193429 values.
- Derive corollaries from the EGS axiom (e.g., $f(n)/n \to 2$).
- Replace the EGS axiom with an unconditional proof following the 1982 paper's
  argument (deep prime-redistribution combinatorics; a multi-month project).

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (reconciliation iteration)
- Approaches tried: 1 (constructive witness + axiomatized asymptotic + open Prop)

## Provenance

- Gallery slug: `erdos-390`
- Lean source: `proofs/Proofs/Erdos390Problem.lean` (538 lines, 14 theorems, 1 axiom, 0 sorries)
- Gallery meta: `src/data/proofs/erdos-390/meta.json` (status `axiomatized`)
- OEIS reference: A193429
- Primary citation: Erdős, Guy, Selfridge (1982), "Another property of 239 and some related questions"
