# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 533 in-progress, 1238 completed

## Selected Problem

- **ID**: brouwer-fixed-point-oq-04-oq-04
- **Name**: Extract constructive content of Kakutani fixed-point theorem
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Only unselected EMPTY candidate in the correct domain**: All higher-composite EMPTY candidates
   (unit-distance-independence-oq-02, mean-value-theorem-oq-04, taylor-theorem-oq-02, etc.) were
   already selected by prior seeker runs. This problem and szemeredi-theorem-oq-01 are the remaining
   unselected available problems. Brouwer wins on composite score: 56 vs 48.
2. **Domain diversity**: Recent seeker selections span combinatorics (erdos-ko-rado-oq-04,
   factor-remainder-nullstellensatz-oq-02), number theory (wolstenholme-theorem-oq-03), and
   analysis (taylor-sincos-convergence-oq-01, triangular-reciprocals-oq-02). Topology and
   constructive mathematics is a fresh domain.
3. **Tractability 5**: The Kakutani theorem for convex-valued upper-semicontinuous correspondences
   is proved via Brouwer applied to a smoothed approximation (Michael's selection theorem or
   Schauder). The constructive content question — finding an algorithm for the approximate fixed
   point — is a well-defined research program (Abramsky, Longley, Normann have results here).
4. **Significance 6**: The Kakutani theorem is the backbone of Nash equilibrium existence proofs
   and general equilibrium theory. Extracting its constructive content has implications for
   computational economics and game theory formalization.
5. **Rejects szemeredi-theorem-oq-01**: Szemerédi's theorem (Kelley-Meka direction, significance 8,
   tractability 4) was rejected due to tractability penalty — Kelley-Meka is cutting-edge research
   (2023), requires polynomial method and energy increment arguments that are not yet in Mathlib,
   and is a domain already covered by recent combinatorics selections.

## Parent Proof Context

The parent gallery proof `brouwer-fixed-point` (OQ-04 line):
- Status: `axiomatized` with 2 axioms: `no_retraction_axiom` and `retraction_construction`
- OQ-04 asks: extract the constructive content from Kakutani's extension to convex-valued correspondences
- The existing proof has a 1D constructive example (via `exists_mem_Icc_isFixedPt_of_mapsTo`)
- The Lean file mentions Kakutani as an "application" but does not formalize it

## Rejection Summary

- **Candidates considered**: 15 available
- **Candidates rejected**: 14
  - `unit-distance-independence-oq-02` (score 78): Already selected in seeker commit 83e3f74152
  - `mean-value-theorem-oq-04` (score 77): Already selected in seeker commit 09d5fda292
  - `taylor-theorem-oq-02`, `euler-identity-oq-01-oq-04`, `vietas-formulas-oq-02` (score 76): Already selected
  - `taylor-sincos-convergence-oq-01`, `triangular-reciprocals-oq-02` (score 75): Already selected
  - `factor-remainder-nullstellensatz-oq-02` (score 67): Already selected
  - `erdos-ko-rado-oq-04` (score 57): Already selected
  - `wolstenholme-theorem-oq-03`, `buffons-needle-oq-01-oq-04` (score 66): Already selected
  - `szemeredi-theorem-oq-01` (score 48): REJECT — tractability 4, Kelley-Meka frontier too hard;
    combinatorics domain overlap with recent selections applies diversity penalty
  - `prime-gap-bounds-oq-03`: RICH knowledge (16+ items, 93-line knowledge.md) → score -2923
- **Confidence**: medium (only two genuinely unselected candidates; Szemerédi clearly rejected,
  leaving Brouwer as the sole viable choice)

## Related Gallery Proofs

- `brouwer-fixed-point`: Base proof — "Brouwer Fixed Point Theorem"; parent of this OQ.
  Contains 1D constructive example via IVT. Axiomatizes the 2 key topological axioms.
- `brouwers-fixed-point-theorem` (Wiedijk #36): 1D case formalized constructively via IVT
- `nash-equilibrium` (if present): Uses Kakutani for Nash existence — motivates this OQ
- `sperner` / `sperner-lemma`: Combinatorial route to Brouwer (triangulation argument)

## Suggested First Steps

1. **OBSERVE**: Check Mathlib for `Kakutani`, `uppersemicontinuous`, `correspondence`,
   `SetValued`, `convex_hull` combinators. Also search for Michael's selection theorem
   (continuous selection from convex-valued lsc correspondences). Key Mathlib modules:
   `Mathlib.Topology.ContinuousFunction`, `Mathlib.Analysis.Convex.Basic`.
2. **ORIENT**: Decide on scope: (a) full Kakutani theorem for finite-dimensional convex bodies,
   or (b) constructive approximate fixed-point extraction. Option (b) is more tractable:
   show that for any ε > 0 there exists a point x with d(x, F(x)) < ε.
3. **DECIDE**: If Mathlib lacks set-valued maps (`Correspondence : X → Set Y`) infrastructure,
   define a minimal `UpperSemicontCorrespondence` structure. Then approximate via Schauder
   or via Sperner-based triangulation. The triangulation route may be more Lean-friendly
   given existing Sperner infrastructure.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 533 |
| Completed | 1238 |
| **Total** | **~1787** |

## Candidate Pool Health

- Pool depth: **adequate** (15 available, 2 unselected by seeker this cycle)
- Note: Most available problems have existing seeker selection reports from prior runs;
  researchers should have ample choices. Pool is near replenishment threshold on
  "fresh unselected" dimension (~2 remaining).
- Recommendation: Consider adding 10–15 new problems from gallery open questions after
  this cycle completes to maintain seeker diversity. Key domains to add: functional analysis,
  algebraic geometry, differential topology.
- Next refresh recommended: after current batch of researcher runs completes
