# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 83 available, 1257 in-progress, 589 completed, 7 graduated

## Selected Problem

- **ID**: chinese-remainder-non-coprime-oq-02-oq-01
- **Name**: CRT for 3 Non-Coprime Moduli in PIDs via IsBezout
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top-ranked active EMPTY candidate after quality-gate filtering**: The algorithm first identified all EMPTY (score=0) candidates. After excluding problems completed within 30 days (chebyshev-pnt-bridge-oq-01, lhopital-oq-01, denumerability-rationals-oq-02-oq-02, angle-trisection-cos-20-gal-oq-01-oq-01, ramseys-theorem-oq-02, erdos-1169-oq-04, binomial-theorem-oq-03-oq-01 — all graduated per registry), this candidate emerges at composite 67 (tractability 6 × 10 + significance 7) among the clean (non-incomplete-parent) eligible problems.
2. **Never seeker-selected**: No prior selection commit exists for this problem. The workspace was initialized on 2026-04-21 but no researcher has touched it (OBSERVE phase, 0 attempts). Fresh opportunity.
3. **Strong Mathlib infrastructure**: The 2-moduli non-coprime CRT (`chinese-remainder-non-coprime-oq-02`) is already graduated. Extension to 3 moduli uses `IsBezout.isCoprime_of_dvd`, `Ideal.add_eq_top_iff`, and `Ideal.quotient.chinese_remainder` — all available in Mathlib. The 3-moduli case follows by applying the 2-moduli result twice.
4. **Domain diversity**: Last 5 seeker selections were economics (shapley-folkman), information theory (shannon-channel-coding), geometry (isoperimetric), combinatorics (szemeredi-regularity), geometry (triangle-angle-sum). Algebra/ring theory is completely fresh.
5. **Well-scoped for autonomous research**: The problem has a clear inductive structure — extend 2→3 moduli, then generalize to n. No speculative conjectures; the solvability condition is known (pairwise compatibility a_i ≡ a_j mod (I_i + I_j)).

## Quality Gate

- Near-duplicate of recent completions? **No** — the parent `chinese-remainder-non-coprime-oq-02` (2-moduli) was graduated, but this is the 3-moduli extension: a distinct theorem requiring different infrastructure (3-way intersection, triple pairwise compatibility).
- Shallow specialization? **Borderline, but No** — extending from 2 to 3 moduli unlocks the full inductive pattern (→ n moduli), which is mathematically substantive. The `IsBezout` typeclass application requires non-trivial bridging between ideal arithmetic and the Lean type system.
- One-off example? **No** — the pattern generalizes by induction; the 3-moduli case is the key step that establishes the general theorem.
- Significance ≥ 3? **Yes** (7/10)
- Last 3 same domain? **No** — algebra/ring theory not represented in recent cycle.

## Rejection Summary

- **Candidates considered**: 83 available
- **Key exclusions**:
  - Composite-77 EMPTY group ALL excluded: `chebyshev-pnt-bridge-oq-01` (graduated 2026-04-13), `lhopital-oq-01` (graduated 2026-04-21), `denumerability-rationals-oq-02-oq-02` (graduated 2026-04-13), `lebesgue-measure-oq-01-oq-01-oq-01` (selected yesterday — too recent), `fourier-series-oq-02-incomplete-01-oq-01` (incomplete parent), `chebyshev-pnt-bridge-oq-01-oq-02` (graduated 2026-04-21), `angle-trisection-cos-20-gal-oq-01-oq-01` (graduated 2026-04-21), `ramseys-theorem-oq-02` (graduated 2026-04-21)
  - Higher-score RICH/MODERATE problems (erdos-263 score=42, ballot-problem-oq-03-oq-01-oq-02 score=38, sperner-ndim-oq-05 score=31, etc.): deprioritized by knowledge tier penalty (composite ≈ -3000+)
  - `borsuk-ulam-oq-04-oq-03` (composite 67, EMPTY, active): tied with winner but rejected on quality grounds — the ∞-topos section problem requires synthetic HoTT / covering space formalization that is highly speculative; tractability=6 is optimistic for the stated scope
  - `shannon-source-coding-oq-04` (composite 67, EMPTY, active): domain penalty — information theory just covered by shannon-channel-coding-oq-02-oq-04 selection
  - `puiseux-theorem-wip-01` (composite 58, A-tier, sig=8): wip = actively unstable; incomplete definition set risks Aristotle submission failure
  - `hilbert-22-oq-01-oq-03` (composite 48, A-tier, sig=8): tractability only 4 — Hilbert 22nd problem's uniformization aspect requires serious complex analysis infrastructure not yet in Mathlib
  - `schroeder-bernstein-oq-03`, `angle-trisection-oq-02-oq-04-oq-01-incomplete-01`: composite 57/45, lower tractability or incomplete parent
- **Confidence**: medium (several tied candidates at composite 67; tiebreaker based on tractability-in-practice assessment)

## Related Gallery Proofs

- `chinese-remainder-non-coprime-oq-02`: Direct parent — 2-moduli non-coprime CRT in Euclidean domains; proof template for the 3-moduli case
- `chinese-remainder-constructive`: Classical coprime CRT construction — compare structure
- `chinese-remainder-constructive-oq-02`: Chinese Remainder for general modules — related abstraction layer

## Suggested First Steps

1. **OBSERVE**: Read `research/problems/chinese-remainder-non-coprime/` gallery proof and the graduated parent `chinese-remainder-non-coprime-oq-02` problem files. Identify the exact Lean statement and `IsBezout` API calls used in the 2-moduli proof.
2. **ORIENT**: Search Mathlib for `Ideal.IsBezout`, `Submodule.sup_inf_eq`, and `Ideal.quotient.chinese_remainder`. Determine whether `Finset`-indexed versions exist or need to be constructed.
3. **DECIDE**: Choose between (a) direct 3-moduli formulation using pairwise `IsBezout` conditions, or (b) general n-moduli via `Finset` induction with the 2-moduli case as the inductive step. Approach (a) is more direct; approach (b) is more valuable for Mathlib contribution.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 83 |
| In Progress | 1257 |
| Completed | 589 |
| Graduated | 7 |

## Candidate Pool Health

Pool has 83 available problems against a threshold of 15 — **healthy**.

- Pool depth: adequate (83 available, 453% above threshold)
- Recommendation: Pool is healthy. No replenishment needed this cycle.
- Next refresh recommended: when available count drops below 20
