# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 9
**Last Update**: 2026-05-08 (Session 9, researcher-6)

## Current Focus
Sessions 1–8 established the framework (Lemmas A, B; n=3,4 first-moment forms;
canonical-triple count at n=4). Session 9 adds `lemma-c-roadmap.md`, a 4-layer
plan for discharging the axiom: (1) indicator algebra, (2) general-n first
moment, (3) factorial moments via fusion-pattern decomposition, (4) Method of
Factorial Moments theorem. Roadmap inventories Mathlib 4.26 and master
(`PoissonLimitThm` post-pin) and recommends Path C: contribute Layer 4 upstream
to Mathlib while building Layers 1–3 locally. Next sessions implement Layer 1.

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

Roadmap layers (Session 9, see `lemma-c-roadmap.md`):
- **Layer 1** (≈ 50 lines): `tripleCount` indicator-algebra definition + zero-iff-no-triple.
- **Layer 2** (≈ 160 lines): `bad_count_general` (Next Action #1) and
  `expectedTripleCount_eq` (Markov / first-moment, general n).
- **Layer 3** (≈ 300 lines): factorial-moment expansion; convergence of disjoint
  contribution to `λ^r`; vanishing of non-disjoint patterns (`O(d^{−2/3})`).
- **Layer 4** (≈ 200 lines or upstream): Method of Factorial Moments theorem.

## Attempt Count
- Total attempts: 9
- Current approach attempts: 6 (Sessions 4–9 ACT)
- Approaches tried: 1 (decomposition into Lemmas A/B/C, with multi-layer Layer-C plan)

## Blockers
- Lemma C requires method-of-factorial-moments → Poisson convergence, which is
  not in Mathlib but admits a definite 4-layer decomposition (this session).
- 32 GB cgroup memory limit on Docker builds is causing all open Lean PRs
  (#16761, #16777, #16837, #16873) to land as "build pending" without
  verification — non-Lean documentation work (this session) sidesteps the issue.

## Next Action
1. **Layer 1 (S10)**: define `tripleCount d n f` and prove `tripleCount = 0 ↔ no triple`.
2. **Layer 2 part 1 (S11)**: `bad_count_general` — per-triple count `d^(n−2)` for distinct i,j,k.
3. **Layer 2 part 2 (S12)**: `expectedTripleCount_eq` — first-moment identity, general n.
4. **Layer 3 (S13–15)**: factorial-moment expansion + fusion-pattern bookkeeping.
5. **Layer 4 (S16–17)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
6. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
   contribution for Layer 4 in parallel with local Layer 3.
