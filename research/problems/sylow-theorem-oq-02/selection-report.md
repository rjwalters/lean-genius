# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 28 available, 559 in-progress, 1405 completed, 3 graduated

## Selected Problem

- **ID**: sylow-theorem-oq-02
- **Name**: Sylow Theorem: Complexity of Finding All Sylow p-Subgroups
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Domain diversity**: The last 3 selections were `sqrt2-minpoly-oq-01` (algebra/number theory), `chinese-remainder-non-coprime-oq-02-oq-01` (algebra/number theory), and `shapley-folkman-oq-03` (economics/combinatorics). Algebra/number theory dominated this batch (5+ selections). Group theory + computational complexity is a fresh domain with zero batch coverage.
2. **Composite score 57** (tractability 5 × 10 + significance 7): Tied with `napoleons-theorem-oq-02` at 57, but group theory is less redundant than geometry (isoperimetric + triangle-angle-sum already in this batch).
3. **No existing workspace**: Unlike the higher-composite candidates (`feuerbachs-theorem-defs-oq-04` at 77, `newton-inductive-step-oq-03` at 67, Ptolemy × 2 at 67), `sylow-theorem-oq-02` had no research workspace — this selection creates one and makes it immediately researcher-ready.
4. **Clear tractable path**: Formalize the orbit enumeration `{g • P | g ∈ G}` as a `Finset` and prove its cardinality via orbit-stabilizer. All component lemmas are in Mathlib; the work is composition.

## Quality Gate

- Near-duplicate of recent completions? **No** — group theory/complexity is distinct from any recent work.
- Shallow specialization? **No** — orbit-based enumeration with certified bounds is genuinely new content; Mathlib has existential Sylow theory but not constructive enumeration.
- One-off example check? **No** — works for any finite group; theory-level scope.
- Significance >= 3? **Yes** (7/10)
- Last 3 same domain? **No** — algebra × 2, economics × 1; group theory is fresh.

## Rejection Summary

- **Candidates considered**: 14 with composite ≥ 47 and significance ≥ 6
- **Candidates rejected**: 13
  - `feuerbachs-theorem-defs-oq-04`, `minkowski-fundamental-theorem-oq-04`: composite 77 (highest), but both already have initialized workspaces from prior seeker batches — researcher-ready without new commit
  - `newton-inductive-step-oq-03`, `ptolemys-complex-proof-oq-02`, `ptolemys-theorem-oq-01-oq-02`: composite 67 — all have workspaces; geometry/q-combinatorics partially covered by this batch
  - `napoleons-theorem-oq-02`: composite 57, tied — geometry domain (DFT connection), already two geometry picks in this batch (isoperimetric, triangle-angle-sum)
  - `dissection-of-cubes-oq-04`: composite 57, no workspace — geometry-adjacent (3D dissection); group theory diversity wins tiebreaker for fresh domain
  - `divisibility-truncation-general-oq-03`: composite 56 — significance 6/10 lower
  - `hurwitz-theorem-oq-04`: composite 47 — tractability 4; Lie group exceptional connections speculative
  - `szemeredi-full-oq-01`, `szemeredi-full-oq-02`: composite 38–49 — Szemeredi domain over-covered; tractability ≤ 4
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`: composite 27–28 — tractability 2; open conjectures with no realistic Lean path
- **Confidence**: medium (tied with napoleons-theorem-oq-02; diversity tiebreaker needed)

## Related Gallery Proofs

- `sylow-theorem`: Parent proof (0 sorries, fully verified) — provides existence and conjugacy that the orbit enumeration extends
- `sylow-theorem-oq-04`: Sibling OQ on Schur-Zassenhaus — related extension theory infrastructure
- `chinese-remainder-non-coprime`: CRT machinery for direct product decompositions

## Suggested First Steps

1. **OBSERVE**: Audit `Mathlib.GroupTheory.Sylow` — specifically `Sylow.conj_eq` (conjugacy), `card_sylow_prime_pow_dvd` (count bound), and check if `ConjAct G` action on `Sylow p G` is in Mathlib
2. **ORIENT**: Check `MulAction.card_orbit_mul_card_stabilizer` and determine whether `Finset.image (· • P.toSubgroup) Finset.univ` constructs the right orbit set; identify what `Finset.card` lemmas apply
3. **DECIDE**: Choose between (a) formalizing the orbit enumeration count `n_p = [G : N_G(P)]` as a standalone theorem, or (b) constructing a `Finset (Sylow p G)` with decidable membership — pick whichever has denser Mathlib support

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 28 |
| In Progress | 559 |
| Completed | 1405 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

Pool has 28 available problems against a threshold of 15 — **healthy**.

- Pool depth: adequate (28 available, 87% above minimum threshold)
- Recommendation: Pool is healthy. No replenishment needed this cycle.
- Next refresh recommended: when available count drops below 20

## Initialized

- [x] Research workspace created: `research/problems/sylow-theorem-oq-02/`
- [x] problem.md populated with formal statement, approaches, and tractability assessment
- [x] knowledge.md initialized
- [ ] Ready for /researcher
