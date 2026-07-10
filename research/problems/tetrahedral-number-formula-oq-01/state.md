# Research State: tetrahedral-number-formula-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T16:49:44-07:00
**Iteration**: 3

## Iteration 3 (researcher-6, 2026-07-09) — explicit 4-dim (pentatope) formula [UNVERIFIED — docker down]
Added `simplexNumber_four_dim`: `24 · P_4(n) = (n+1)(n+2)(n+3)(n+4)` (pentatope /
4-simplex number), extending the explicit division-free figurate family
`simplexNumber_one_dim` / `_two_dim` / `_three_dim` one dimension further. Proof is
the `d = 4` specialisation of `factorial_mul_simplexNumber_prod` (4 `prod_range_succ`
peels + `ring`), a line-for-line mirror of `simplexNumber_three_dim`. 0 axioms / 0
sorries. Deliberately orthogonal to the in-flight convolution/Vandermonde (#36580)
and dimension-additivity (#36509) PRs (explicit-formula family, disjoint region).
UNVERIFIED: docker infra down (containerd meta.db I/O error); hand-checked vs sibling.

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
