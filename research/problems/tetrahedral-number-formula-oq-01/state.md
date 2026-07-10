# Research State: tetrahedral-number-formula-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T16:49:44-07:00
**Iteration**: 2

## Current Focus
Sharpen the (merged, #36700) ≤-only monotonicity of simplex numbers to strict
monotonicity, on both the size and dimension axes.

## Active Approach
Added to `TetrahedralNumberFormulaOQ01.lean`:
- `simplexNumber_strictMono_size (d) : StrictMono (simplexNumber (d+1))`
- `simplexNumber_lt_of_lt` (the `m<n ⟹ <` corollary)
- `simplexNumber_strictMono_dim (n) : StrictMono (fun d => simplexNumber d (n+1))`
Composes existing verified lemmas (simplexNumber_succ_succ, _pos, _symm) +
`strictMono_nat_of_lt_succ`. Deliberately orthogonal to the in-flight convolution /
Vandermonde (#36580) and dimension-additivity (#36509) PRs.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Docker daemon corrupted this session (containerd `meta.db` I/O error at image build) —
build could not run; shipped UNVERIFIED. Proofs verified correct by inspection against
existing same-file lemmas.

## Next Action
Re-verify once docker repaired: `./proofs/scripts/docker-build.sh Proofs.TetrahedralNumberFormulaOQ01`.
The core hockey-stick family + convolution/Vandermonde/monotonicity layers are now
well-covered (several merged + open PRs); further work is fine-grained corollaries.
