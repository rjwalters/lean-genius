# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 10
**Last Update**: 2026-05-08 (Session 10, researcher-11)

## Current Focus
Sessions 1–8 established the framework (Lemmas A, B; n=3,4 first-moment forms;
canonical-triple count at n=4). Session 9 added `lemma-c-roadmap.md`, the
four-layer plan. **Session 10 implements Layer 1** (≈ 95 lines): definition
`tripleCount d n f` (sum-of-indicators count over strictly-increasing triples)
plus the two zero-iff equivalences (strict-inequality form and pairwise-distinct
form, the latter matching the axiom predicate via a six-case sorting argument)
and the filter-equality lemma `noTriple_filter_eq_tripleCount_zero_filter`
that bridges the axiom's no-triple filter to `{f | tripleCount d n f = 0}`.
Layer 2 (general-n first moment) is queued for S11.

## Active Approach
Decomposition strategy:
- **Lemma A** (`lambda_tendsto`, Session 4 PROVED): `λ_c(d) → c³/6`.
- **Lemma B** (`exp_lambda_tendsto`, Session 4 PROVED): `exp(−λ_c(d)) → exp(−c³/6)`.
- **Lemma C** (`p_no_triple_tendsto`, axiom): `P_no_triple(n_c(d), d) → exp(−c³/6)`.
  Still requires method-of-factorial-moments → Poisson convergence (~500 lines
  not in Mathlib 4.26).

First-moment scaffolding (Sessions 6–8, on main / open PRs):
- `p_no_triple_n3` (Session 6): P(no triple|n=3) = 1 − 1/d²
- `p_triple_n3` (Session 7): P(triple|n=3) = 1/d²
- `p_triple_n3_eq_expectedTriples` (Session 7): n=3 first-moment identity
- `bad_count_n4_canonical`, `p_canonical_triple_n4` (Session 8 PR #16873):
  n=4 canonical triple count and probability

Layer 1 (Session 10, this session — DONE pending build):
- `tripleCount d n f` def (≈ 4 lines): card of strictly-increasing triples
  with `f i = f j = f k`.
- `tripleCount_eq_zero_iff_strict` (≈ 8 lines): bridges to `Finset.filter`
  emptiness; trivial direction.
- `tripleCount_eq_zero_iff_no_triple` (≈ 25 lines): the axiom-matching
  pairwise-distinct form; six-case sort over linear order of `(i, j, k)`.
- `noTriple_filter_eq_tripleCount_zero_filter` (≈ 6 lines): filter-level
  bridge to the axiom's no-triple filter.

Roadmap layers (Session 9, see `lemma-c-roadmap.md`):
- **Layer 1** (≈ 50 lines target / 95 actual): DONE this session.
- **Layer 2** (≈ 160 lines): `bad_count_general` (Next Action #1) and
  `expectedTripleCount_eq` (Markov / first-moment, general n).
- **Layer 3** (≈ 300 lines): factorial-moment expansion; convergence of disjoint
  contribution to `λ^r`; vanishing of non-disjoint patterns (`O(d^{−2/3})`).
- **Layer 4** (≈ 200 lines or upstream): Method of Factorial Moments theorem.

## Attempt Count
- Total attempts: 10
- Current approach attempts: 7 (Sessions 4–10 ACT)
- Approaches tried: 1 (decomposition into Lemmas A/B/C, with multi-layer Layer-C plan)

## Blockers
- Lemma C requires method-of-factorial-moments → Poisson convergence, which is
  not in Mathlib but admits a definite 4-layer decomposition (this session).
- 32 GB cgroup memory limit on Docker builds is causing all open Lean PRs
  (#16761, #16777, #16837, #16873) to land as "build pending" without
  verification — non-Lean documentation work (this session) sidesteps the issue.

## Next Action
1. ✅ **Layer 1 (S10, this session)**: `tripleCount` def + `tripleCount_eq_zero_iff_no_triple` + filter bridge — DONE pending build.
2. **Layer 2 part 1 (S11)**: `bad_count_general` — per-triple count `d^(n−2)` for distinct i,j,k.
3. **Layer 2 part 2 (S12)**: `expectedTripleCount_eq` — first-moment identity, general n. Connects `(∑ f, tripleCount d n f) / |Fin n → Fin d| = C(n,3)/d² = expectedTriples n d`.
4. **Layer 3 (S13–15)**: factorial-moment expansion + fusion-pattern bookkeeping.
5. **Layer 4 (S16–17)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
6. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
   contribution for Layer 4 in parallel with local Layer 3.
