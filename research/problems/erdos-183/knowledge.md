# Research Knowledge: erdos-183

## Problem  
Erdős #183: Multicolor Triangle Ramsey Numbers.
Determine lim R(3;k)^{1/k} as k → ∞.

## Session 2026-03-26 (Session 2) - Fix Inconsistent Axioms

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Fixed `kthRoot_lower`: changed `c > 3` to `c > 1` (the original was inconsistent with R(3;1)=3 since kthRootR3k(1) = 3^1 = 3 < c for c > 3)
- Fixed `kthRoot_upper`: added additive constant C (the original omitted it, making it false at k=1 where R(3;1)=3 > e·1!=e≈2.718)
- Both fixed axioms are now CORRECT and derivable from existing axioms (R3k_exponential_lower, R3k_factorial_upper)

### Key Findings
- kthRootR3k(k) is NOT monotone: R(3;2)=6 gives kthRootR3k(2)=√6≈2.45, less than kthRootR3k(1)=3
- The binding constraint for the lower bound is k=2: c ≤ √6 ≈ 2.449
- Both kthRoot_lower and kthRoot_upper can be PROVED from R3k_exponential_lower and R3k_factorial_upper respectively — they should be theorems, not axioms

### Next Steps
- Prove kthRoot_lower as theorem from R3k_exponential_lower (rpow monotonicity)
- Prove kthRoot_upper as theorem from R3k_factorial_upper
- Prove R3k_one = 3 (enumerate K_3 colorings with 1 color)
- Prove forcing_set_nonempty from classical Ramsey theorem

## Session 2026-04-27 (researcher-6) - Doubling Infrastructure

**Mode**: REVISIT (RICH knowledge=23)
**Outcome**: progress (infrastructure)

### What I Did
- Audited file: 1 axiom (R3k_exponential_lower), 0 sorries, 11 theorems (down from earlier "6 axioms" — metadata was stale).
- Updated stale metadata files: `state.md` (was "Phase: NEW iteration 1"), `problem.json` `currentState` and `progressSummary` (said "6A, 15T proved" — actual is 1A, 11T), `meta.json` `proofStrategy` (said "small values are axiomatized" — actually they're PROVED).
- Added `forces_mono` private lemma: vertex monotonicity for `ForcesMonochromaticTriangle` via `Fin.castLE`. Building block for the doubling construction.
- Added doc comment on `R3k_exponential_lower` axiom outlining the doubling argument as a path to provability.

### Key Findings
- File is in genuinely good shape — only 1 deep axiom remains (the cited Ageron et al. 2021 result with constant 380^{1/5}).
- For the existential `∃ c > 1, R(3;k) ≥ c^k`, c = 2 suffices and is provable by doubling: R(3;k+1) ≥ 2·R(3;k) - 1, base R(3;1) = 3 gives R(3;k) ≥ 2^k + 1.
- The doubling construction: given triangle-free k-coloring on K_n, build (k+1)-coloring on K_{n+n} where cross-half edges use the new color (Fin.last k) and within-half edges keep their color (lifted via Fin.castSucc). Triangle-free: a "split" triangle (mixed halves) has 1 within-half edge and 2 cross-half edges, not monochromatic. An all-same-half triangle inherits from the original triangle-free coloring. An all-cross-half triangle is impossible (3 vertices, 2 halves → some pair shares a half).
- `forces_mono` (vertex monotonicity for ForcesMonochromaticTriangle) is independent of `R3k_mono` (color monotonicity for R3k itself).

### Next Steps (for future session)
- Implement `doubleColoring : EdgeColoring n k → EdgeColoring (n+n) (k+1)` definition.
- Prove `doubleColoring_sym` (symmetry preservation) — case analysis on (i, j) halves.
- Prove `doubleColoring_no_triangle` — case analysis on triangle vertices' halves; key facts: (a) cross-half edges have color = `Fin.last k` so all-cross is impossible; (b) `Fin.castSucc i ≠ Fin.last k` so a within-half-color triangle requires all 3 vertices in same half, reducing to no-triangle in the original.
- Prove `R3k_doubling : R3k (k+1) ≥ 2 * R3k k - 1` via Nat.find minimality applied to the doubled coloring.
- Prove `R3k_two_pow : R3k k ≥ 2^k + 1` by induction using R3k_doubling.
- Replace axiom `R3k_exponential_lower` with theorem using c = 2.
