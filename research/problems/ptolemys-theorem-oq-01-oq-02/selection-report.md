# Problem Selection Report

**Date**: 2026-04-24
**Mode**: SELECT
**Pool Status**: 16 available, 557 in-progress, 1419 completed, 9 graduated, 3 blocked

## Selected Problem

- **ID**: ptolemys-theorem-oq-01-oq-02
- **Name**: Ptolemy Theorem: Extension to Spherical and Hyperbolic Geometry Metrics
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 67
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge tier (score=0)** — highest composite-score candidate with no prior research
   investment. Fresh start maximizes research output per iteration.
2. **Tractability=6** — the spherical and hyperbolic Ptolemy analogues are known mathematically
   (spherical version uses `sin` of chord half-angles; hyperbolic version uses `sinh`). Mathlib
   already has `EuclideanSpace`, `Metric.sphere`, and some hyperbolic geometry primitives.
   Path to formalization is not fully blocked.
3. **Domain diversity** — last selections were analysis (cauchy-schwarz) and number theory
   (Goldbach, twin primes). Geometry provides fresh domain coverage.
4. **No recent git activity** — unlike the next-ranked candidates (shapley-folkman-oq-03 had 4+
   enrichments in 30 days; erdos-476-oq-05-wip-01 has an active related claim), this problem
   has had no recent commits. No risk of collision.

## Rejection Summary

- **Candidates considered**: 16
- **Candidates rejected**: 15

| Candidate | Composite | Reason |
|-----------|-----------|--------|
| cauchy-schwarz-integral-oq-01-oq-03-oq-01 | 76 | Selected 2026-04-23 (yesterday); workspace just initialized |
| erdos-476-oq-05-wip-01 | 67 | Related claim `erdos-476-oq-05` active; heavy recent git activity |
| shapley-folkman-oq-03 | 67 | 4+ enrichment commits in 30 days; high churn risk |
| lebesgue-measure-oq-06 | -2932 | Actively claimed (`lebesgue-measure-oq-06.lock`) |
| sperner-ndim-oq-04 | -2932 | RICH knowledge (23 items); lower priority |
| erdos-268-incomplete-01 | -933 | WEAK knowledge (4 items); related active work |
| erdos-512-incomplete-01 | -942 | WEAK knowledge (8 items); below EMPTY tier |
| sophie-germain-oq-01 | 27 | Number theory (diversity penalty); tractability=2 |
| weak-goldbach-oq-01 | 28 | Number theory (recently selected); tractability=2 |
| twin-primes-special-oq-01 | 28 | Number theory (recently selected); tractability=2 |
| szemeredi-full-oq-02 | 38 | Tractability=3; very hard to prove |
| szemeredi-full-oq-01 | 49 | Tractability=4; ergodic theory proof is very involved |
| hurwitz-theorem-oq-04 | 47 | Tractability=4; requires exceptional Lie group theory |
| erdos-1155-oq-02 | 56 | Lower significance=6; limiting distribution is hard |
| dissection-of-cubes-oq-04 | 57 | Recent metadata fixes (#12122, #12116); Dehn invariants hard |

- **Confidence**: high — clear score separation between selected candidate and next viable option

## Related Gallery Proofs

- `ptolemys-theorem`: Main Ptolemy theorem (AC·BD = AB·CD + BC·DA), formalized, sorries=0
- `ptolemys-theorem-oq-01`: Ptolemy Inequality with concyclicity characterization, sorries=0
- `ptolemys-complex-proof`: Complex-number approach to Ptolemy, sorries=0
- `ptolemys-theorem-oq-01-oq-01`: Converse direction (equality ↔ CCW ordering)

## Mathematical Context

The parent OQ (from `ptolemys-theorem-oq-01`) asks:
> "Extend to other metrics (spherical geometry, hyperbolic geometry) where analogues of
>  Ptolemy's theorem exist."

**Spherical Ptolemy**: For a cyclic quadrilateral on the unit sphere,
`sin(AC/2)·sin(BD/2) = sin(AB/2)·sin(CD/2) + sin(AD/2)·sin(BC/2)`

**Hyperbolic Ptolemy**: In the hyperbolic plane,
`sinh(AC/2)·sinh(BD/2) = sinh(AB/2)·sinh(CD/2) + sinh(AD/2)·sinh(BC/2)`

## Suggested First Steps

1. **OBSERVE**: Survey what Ptolemy-related Lean files already exist (`proofs/Proofs/Ptolemys*.lean`);
   check what metric geometry primitives Mathlib 4 provides for spheres and hyperbolic planes.
2. **ORIENT (Scout)**: Request a scout survey on "spherical Ptolemy theorem Lean 4 Mathlib"
   to discover relevant Mathlib lemmas (`sin_dist`, chord length formulas, hyperbolic trig).
3. **DECIDE**: Choose the more tractable target first — likely spherical geometry (Mathlib has
   better sphere support than hyperbolic plane). Identify the key lemma chain needed.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 16 |
| In Progress | 557 |
| Completed | 1419 |
| Graduated | 9 |
| Blocked | 3 |

## Candidate Pool Health

Pool depth: **low** — 16 available is at threshold (minimum 15). One more selection or new
researcher claim will push below threshold.

- Recommendation: Consider adding new problems from the gallery in the next refresh cycle.
- Next refresh recommended: next cycle (30 min)

## Initialized

- [x] Research workspace created (exists from prior selection cycle)
- [x] problem.md populated with formal statement and context
- [x] state.md set to OBSERVE phase
- [x] Re-confirmed available in database and candidate-pool.json (2026-04-24)
- [x] Ready for /researcher
