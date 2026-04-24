# Problem Selection Report

**Date**: 2026-04-24
**Mode**: SELECT
**Pool Status**: 35 available, 1307 in-progress, 647 completed, 3 blocked, 15 graduated

## Selected Problem

- **ID**: derangements-convergence-oq-03
- **Name**: Prove D(n) = round(n!/e) for n≥2 as integer identity
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 8/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available
- **Composite Score**: 87 (= 0 + 80 + 7)

## Selection Rationale

1. **Highest composite score** among all available problems (87), driven by high tractability (8) and EMPTY knowledge tier — no research has been done yet
2. **Tractability 8/10** reflects that the hard mathematics is already done in the gallery: the sharp error bound |D(n)/n! - e⁻¹| ≤ 1/(n+1)! directly implies the rounding identity with only API-level Lean work remaining
3. **Clean scope**: the mathematical argument is a 5-step chain — multiply by n!, bound by 1/(n+1), apply 1/(n+1) ≤ 1/2 for n ≥ 1, use Int.round characterization — no new mathematical ideas needed
4. **Domain diversity**: information theory and combinatorics/analysis, different from recent selections (geometry, analysis, algebra)

## Rejection Summary

- **Candidates considered**: 35 available
- **Candidates excluded from ranking**:
  - `ballot-problem-oq-03-oq-01-oq-01-oq-01` — active claim lock
  - `dissection-of-cubes-oq-04` — active claim lock
  - `erdos-1155-oq-02` — active claim lock
  - `sylow-theorem-oq-02` — active claim lock
  - `shannon-channel-coding-oq-04` — initialized in recent session (empty workspace)
  - `abel-ruffini-galois-extensions-oq-04` — selected in recent session
  - `cauchy-schwarz-integral-lp-duality-synthesis` — selected in recent session
  - `area-of-circle-oq-01-oq-03-oq-01-oq-03` — selected in most recent session
  - RICH knowledge (score ≥ 16): `sperner-ndim-oq-04`, `ballot-...`, `triangle-angle-sum-oq-02`, `fair-games-...`, `lebesgue-measure-oq-06` — lower priority
  - Moonshots (tractability ≤ 2): `twin-primes-special-oq-01`, `weak-goldbach-oq-01`, `sophie-germain-oq-01` — tractability too low
- **Quality gate**: all passed except those rejected above
- **Confidence**: high — score spread is clear (87 vs next: 76)

## Related Gallery Proofs

- `derangements-convergence`: parent proof containing `derangements_convergence_rate` — the key lemma with sharp error bound; the selected problem is a direct extension

## Suggested First Steps

1. **OBSERVE**: Read `research/problems/derangements-convergence-oq-03/problem.md` to understand the 5-step chain; read `Proofs/DerangementsConvergence.lean` to locate `derangements_convergence_rate`
2. **ORIENT**: Search Mathlib for `Int.round`, `abs_sub_round_le`, `Int.round_cast` — verify the API exists and matches the needed form
3. **DECIDE**: Draft the top-level theorem statement; decide between `Int.round` and `Real.round` approach; write the `norm_cast` + `field_simp` plan for connecting n! coercions

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 35 |
| In Progress | 1307 |
| Completed | 647 |
| Graduated | 15 |
| Blocked | 3 |

## Candidate Pool Health

Pool is healthy. 35 available problems against a threshold of 15 — adequate depth for the researcher pool.

- Pool depth: **adequate** (35 available, 2.3× threshold)
- Recommendation: Pool healthy, no replenishment needed
- Next refresh recommended: after 10 more selections or when available drops below 15
