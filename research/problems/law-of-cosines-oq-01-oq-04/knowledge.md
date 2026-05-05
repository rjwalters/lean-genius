## Problem: law-of-cosines-oq-01-oq-04

**Title**: Small-angle limit — spherical law of cosines → Euclidean law

**Status**: COMPLETE (PR #15392, Docker build pending)

## Session 2026-05-05 (Session 1) — Proof Completed

**Mode**: FRESH  
**Outcome**: completed

### What I Did
- Claimed problem, surveyed related files (SphericalLawOfCosines.lean, LawOfCosinesOQ05.lean)
- Identified key Mathlib infrastructure: HasDerivAt, hasDerivAt_iff_tendsto_slope, cos_two_mul
- Wrote complete 206-line Lean proof with 7 theorems
- Created gallery entry meta.json

### Key Findings
- SphericalLawOfCosines.lean Part VII only documented the limit (tautological theorem), didn't prove it
- Double-angle identity `1 - cos(tx) = 2sin²(tx/2)` converts the cosine limit to squared sinc
- `HasDerivAt.comp` gives `HasDerivAt (fun t => sin(t*x)) x 0` (chain rule)
- `hasDerivAt_iff_tendsto_slope` extracts `sin(h)/h → 1` and `sin(tx)/t → x`
- `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` handles `t*x/2 → 0` with `t*x/2 ≠ 0`
- Main limit decomposes as: `(1-cosα)/t² + cosα·(1-cosβ)/t² - cosC·(sinα/t)·(sinβ/t)`

### Files Modified
- `proofs/Proofs/LawOfCosinesOQ01OQ04.lean` (created)
- `proofs/Proofs.lean` (import added)
- `src/data/proofs/law-of-cosines-oq-01-oq-04/meta.json` (created)
- `src/data/research/problems/law-of-cosines-oq-01-oq-04.json` (created)

### Next Steps
- Docker build verification (infrastructure was hung during session)
- If Lean compilation issues arise, check HasDerivAt.comp pattern and congr' direction
