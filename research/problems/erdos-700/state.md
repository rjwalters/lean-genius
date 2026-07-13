# Current State

**Phase**: AXIOMATIZED
**Since**: 2026-01-14T21:07:11.724Z
**Iteration**: 4
**Last Update**: 2026-05-17T06:40:00Z (S2 STATE-SYNC)

## Current Focus

S2 STATE-SYNC: Reconcile research JSON registry, this state.md, and gallery `meta.json` with the actual Lean file. Before S2, the registry had top-level `phase: OBSERVE` and `currentState.phase: ACT` from 2026-03-13 (T-65d), state.md was still on the initial NEW-iter-1 template from 2026-01-14, and `leanFiles[0]` was substantially behind canonical (lineCount 420 vs actual 427, theoremCount 8 vs 14, axiomCount 0 vs 2). Gallery `meta.json` already correctly marked `status: "axiomatized"` + `badge: "axiom"` + canonical counts.

## Status Summary

| Surface | Value | Source |
|---------|-------|--------|
| Lean file | `proofs/Proofs/Erdos700Problem.lean` (427 LOC, 14 thm, 3 def, 2 axioms, 0 sorries) | `wc -l` + canonical inclusive grep |
| Axioms | `erdos_700_question2` (∞ many composite n with f(n)>√n), `erdos_700_question3` (f(n)≪_A n/(log n)^A) | `grep '^axiom '` |
| Gallery dir | `src/data/proofs/erdos-700/` (annotations.json + index.ts + meta.json) | `ls` |
| Gallery badge | `status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 2` | `src/data/proofs/erdos-700/meta.json` |
| Conjecture status | OPEN (Erdős-Szekeres 1978) | `erdosproblems.com/700` |

## Active Approach

None as of S2 — slug is at AXIOMATIZED rest state with all 3 Erdős-Szekeres questions still open. The 2 remaining axioms encode questions 2 and 3 specifically; question 1 is a characterisation problem rather than a conjecture to discharge.

## Major Progress Arc (iterations 1–3)

Initial scaffolding had 6 axioms. Incremental elimination via:

- **`prime_not_dvd_choose_shift`** (~80 lines, Kummer zero-carry argument): for prime power p^a and m with p∤m, p does not divide C(p^a·m, p^a). Key insight: K=p^a−1 and N−K=p^a·(m−1) have non-overlapping base-p digit support ⇒ 0 carries.
- **`gcd_choose_prime_pow_eq`**: gcd(p^a·m, C(p^a·m, p^a)) = m.
- **`choose_eq_mul_choose_pred`**: absorption identity C(n,k) = (n/k)·C(n-1,k-1).
- **`f_semiprime`** (sandwich argument): f(pq) = p for primes p ≤ q.
- **`f_upper_bound`** (originally axiomatized, converted to theorem via Kummer): f(n) ≤ n/P(n) for composite n.
- **infrastructure glue sorry**: connecting fBinom Finset.min definition to f-bound theorems — discharged.

Proven results: f(p²)=p (exact), f(pq)=p for primes p≤q, f(30)=6, bounds f(n)≥p(n) and f(n)≤n/P(n) for composite n.

## Blockers

- Question 1 (characterise composite n with f(n) = n/P(n)) is open. Known examples: n=pq (semiprimes) and n=30.
- Question 2 (∞ many composite n with f(n) > n^{1/2}) is open — currently only the n=p² family gives f(n) ≥ n^{1/2} non-strictly.
- Question 3 (f(n) ≪_A n/(log n)^A for every A>0) is open — connects to Hardy-Ramanujan-style asymptotic density.

## Next Action

Forward levers (none unblockable without substantial new mathematics):

- **A.** Characterize the f(n)=n/P(n) family for Q1 (e.g., n=pq with p<q gives f(n)=p=n/q=n/P(n); does n=30 generalise to n=p₁p₂p₃ with constraints?).
- **B.** Find a single composite n outside the p² family witnessing f(n)>√n strictly — would discharge `erdos_700_question2` axiom.
- **C.** Lower-bound study connecting f(n) growth to ω(n) or σ(n) for Q3.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 0
- Approaches tried: 4 (initial scaffold + 2 axiom-elimination iterations + S2 STATE-SYNC)

## Iteration Ledger

| Iter | Date | Agent | Result | Scope |
|------|------|-------|--------|-------|
| 1 | 2026-01-14 | (legacy) | NEW — created Erdos700Problem.lean scaffold with 6 axioms | initial creation |
| 2 | (legacy) | (legacy) | OBSERVE → ACT — eliminated 3 axioms via Kummer + sandwich + absorption | substantive Lean work, ~4 axioms remaining |
| 3 | 2026-03-13 | (legacy) | ACT — eliminated f_upper_bound axiom, 1 sorry in infrastructure glue noted | registry last touched here |
| (gap) | 2026-03-13 → 2026-05-17 | — | infrastructure glue sorry discharged in subsequent unrecorded work; registry stayed at iter 3 | T-65d drift |
| 4 | 2026-05-17 | researcher-11 | AXIOMATIZED STATE-SYNC — registry phase OBSERVE/ACT → AXIOMATIZED, state.md rewrite, leanFiles[0] catchup (420→427/8→14/0→2), attemptCounts.total 0→4 | doc-only, 2 files |

## Cross-references

- Research JSON registry: `src/data/research/problems/erdos-700.json`
- Gallery dir: `src/data/proofs/erdos-700/` (meta.json already canonical at AXIOMATIZED)
- Lean source: `proofs/Proofs/Erdos700Problem.lean`
- Sibling problems: erdos-7, erdos-70 (per `relatedProofs`)
