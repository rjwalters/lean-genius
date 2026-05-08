# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 11
**Last Update**: 2026-05-08 (Session 11, researcher-4)

## Current Focus
Sessions 1–8 established the framework (Lemmas A, B; n=3,4 first-moment forms;
canonical-triple count at n=4). Session 9 added `lemma-c-roadmap.md`, the
four-layer plan. **Session 10 implemented Layer 1** (≈ 95 lines):
`tripleCount d n f` def, the two zero-iff equivalences, and the filter-equality
bridge `noTriple_filter_eq_tripleCount_zero_filter`.
**Session 11 implements Layer 2 part 1** (≈ 168 lines, this session):
the general-n per-triple coincidence count
`bad_count_general : card {f | f i = f j ∧ f j = f k} = d^(n-2)` for distinct
i, j, k via an explicit bijection with the (n-2)-element complement function
space `({m // m ≠ j ∧ m ≠ k} → Fin d)`; plus the real-number probability form
`p_triple_general : P(triple) = 1/d²` (independent of n). Generalises
`bad_count_n3` (n=3) and `bad_count_n4_canonical` (n=4 canonical) in one shot.
Layer 2 part 2 (`expectedTripleCount_eq`, the first-moment identity for general
n) is queued for S12.

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

Layer 1 (Session 10, on main):
- `tripleCount d n f` def: card of strictly-increasing triples with `f i = f j = f k`.
- `tripleCount_eq_zero_iff_strict`, `tripleCount_eq_zero_iff_no_triple`,
  `noTriple_filter_eq_tripleCount_zero_filter`.

Layer 2 part 1 (Session 11, this session — DONE pending build):
- `bad_count_general (d n : ℕ) (i j k : Fin n) (hij hjk hik) : card {f | f i = f j ∧ f j = f k} = d^(n-2)`
  via explicit `Equiv` to `({m // m ≠ j ∧ m ≠ k} → Fin d)`. ≈ 110 lines including the cardinality computation
  for the (n-2)-element complement (`Finset.univ \ {j, k}` of card 2 since j ≠ k).
- `p_triple_general` (≈ 15 lines): real-number probability form, P(triple) = 1/d² (independent of n).

Roadmap layers (Session 9, see `lemma-c-roadmap.md`):
- **Layer 1** (≈ 95 lines actual): DONE Session 10.
- **Layer 2** (≈ 110 lines actual for part 1): part 1 DONE this session;
  part 2 (`expectedTripleCount_eq`) queued for S12.
- **Layer 3** (≈ 300 lines): factorial-moment expansion; convergence of disjoint
  contribution to `λ^r`; vanishing of non-disjoint patterns (`O(d^{−2/3})`).
- **Layer 4** (≈ 200 lines or upstream): Method of Factorial Moments theorem.

## Attempt Count
- Total attempts: 11
- Current approach attempts: 8 (Sessions 4–11 ACT)
- Approaches tried: 1 (decomposition into Lemmas A/B/C, with multi-layer Layer-C plan)

## Blockers
- Lemma C requires method-of-factorial-moments → Poisson convergence, which is
  not in Mathlib but admits a definite 4-layer decomposition.
- 32 GB cgroup memory limit on Docker builds is causing all open Lean PRs
  (#16761, #16777, #16837, #16873) to land as "build pending" without
  verification — this session adds another build-pending PR following the same
  convention.

## Next Action
1. ✅ **Layer 1 (S10)**: `tripleCount` def + zero-iff equivalences + filter bridge — DONE on main.
2. ✅ **Layer 2 part 1 (S11, this session)**: `bad_count_general` — per-triple count `d^(n−2)` + `p_triple_general` — DONE pending build.
3. **Layer 2 part 2 (S12)**: `expectedTripleCount_eq` — first-moment identity, general n.
   Sum the per-triple count from S11 over the C(n,3) strictly-increasing triples;
   divide by |Fin n → Fin d| = d^n; reach `(∑ f, tripleCount d n f) / d^n = C(n,3)/d² = expectedTriples n d`.
4. **Layer 3 (S13–15)**: factorial-moment expansion + fusion-pattern bookkeeping.
5. **Layer 4 (S16–17)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
6. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
   contribution for Layer 4 in parallel with local Layer 3.
