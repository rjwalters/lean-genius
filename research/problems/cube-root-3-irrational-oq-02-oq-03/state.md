# Research State: cube-root-3-irrational-oq-02-oq-03

## Current State
**Phase**: VERIFIED-MILESTONE
**Path**: full
**Since**: 2026-07-05T02:16:00-07:00
**Iteration**: 7

## Current Focus
**VERIFICATION BLACKOUT IS OVER.** Docker is back up (`lean4-arm64:v4.26.0`). The full
Vahlen–Capelli scaffold — hand-audited but UNVERIFIED across the prior 4 sessions — now
**builds green**: `docker-build.sh Proofs.CubeRoot3IrrationalOQ02OQ03` → 3061 jobs,
0 axioms, exactly ONE `sorry` (line 705, the `8 ∣ n` + `−a ∈ K²` sub-case).

This is the first machine-check of `vahlen_capelli_four_suff`, `capelli_four_coeff_contra`,
`quartic_two_two_coeffs`, `no_linear_factor`, `monic_natDegree_two_eq`,
`leadingCoeff_inv_mul_monic`, `vahlen_capelli_even_mul_odd`,
`two_power_capelli_of_neg_not_square`, and the full `vahlen_capelli` assembly. All confirmed
correct — no API mismatches, no residual errors, no sign flips in the quartic finishers.

Gallery meta.json was stale (dated 2026-07-04, claimed 7/10 theorems, described the sorry as
"even n ≥ 4"). Updated this session to reflect the verified reality: 20 theorems, 799 lines,
and the sorry now correctly localised to `8 ∣ n` with `−a ∈ K²`.

## Active Approach
Elementary + norm-transfer factor analysis of `Xⁿ − C a`. Necessity (both parities), odd
sufficiency, n=2, n=4, odd-part peel-off, and the entire `−a ∉ K²` branch of the 2-power
tower are all PROVED and now VERIFIED. Only the `−a ∈ K²` 2-power tail remains.

## The Sole Remaining `sorry` — precise math
Case: `k ≥ 3`, `X^(2^k) − C a`, hypotheses `a ∉ K²` (h1), `a ≠ −4b⁴ ∀b` (h2), `−a ∈ K²`.
The tower reduction `X_pow_mul_sub_C_irreducible` requires: a root `x` of the irreducible
base `X^(2^(k-1)) − C a` is NOT a square in `K(x)`. Norm descent gives `N(x) = −a`; a square
root `x = β²` would force `N(β)² = −a`, i.e. `−a ∈ K²` — which is exactly the case
hypothesis, so norm descent is INCONCLUSIVE here. Closing it needs the general **crux lemma**

    (root x of irreducible X^m − C a, m = 2^(k-1) ≥ 4)  ⟹  ( x ∈ K(x)²  ⟺  a ∈ −4K⁴ )

whose `⟸` failure (given `a ∉ −4K⁴`) yields `x ∉ K(x)²` and closes the tower. The m=2
instance of this crux is exactly `vahlen_capelli_four_suff` (done, and verified by hand
above for m=2: x∈K(x)² ⟺ ±2√(−a)∈K² ⟺ a∈−4K⁴). The general m=2^(k-1)≥4 instance is the
multi-page hard part of Lang VI §9 (norm/trace descent in the tower) and is Mathlib's open
TODO. NOT closeable responsibly in one session — attempting to force it risks a false claim.

## Attempt Count
- Total attempts: 7
- Approaches tried: 1 (elementary + norm-transfer factor analysis — succeeding incrementally)

## Blockers
- None on infrastructure: Docker verifier RESTORED this session (blackout resolved).
- Mathematical: the `−a ∈ K²` 2-power crux lemma is genuinely research-hard (Lang VI §9),
  the exact content Mathlib leaves open.

## Next Action
The frontier is now a single, sharply-stated open lemma. A future session with time budget
should attempt the general crux lemma
`crux : Irreducible (X^(2^n) − C a) → a ∉ −4K⁴ → root x ∉ K(x)²` (n ≥ 2), following the
Lang VI §9 norm/trace descent. Aristotle is a candidate delegate for the mechanical
sub-steps once a clean paper reduction is written. Do NOT relocate the sorry again without
genuinely shrinking it — it is already minimal.
