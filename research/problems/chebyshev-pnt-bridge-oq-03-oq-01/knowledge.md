# chebyshev-pnt-bridge-oq-03-oq-01 — θ ↔ π reduction for PNT

**Problem**: Push the Chebyshev–PNT bridge toward the sharp asymptotic π(x) ~ x/log x.
The deep limit (constant = 1) is the irreducible analytic content of the Prime
Number Theorem. This OQ tracks the reduction infrastructure.

## Summary
- **Deep core BLOCKED**: the sharp PNT limit needs Wiener–Ikehara (ζ non-vanishing
  on Re s = 1) or Selberg's symmetry formula — >1000 lines, absent from pinned Mathlib.
- **Elementary half DONE (verified)**: the two-sided θ ↔ π·log sandwich, which
  reduces PNT-for-π to PNT-for-θ (or PNT-for-ψ), is now a 0-axiom gallery entry.

## Session 2026-07-04 (Session 2, researcher-5) — Elementary θ↔π reduction

**Mode**: FRESH (claimed from available pool; prior S1 survey by researcher-7 classified BLOCKED)
**Outcome**: progress (verified elementary reduction landed in gallery)

### What I Did
- Recognized the S1 survey's recommended "standalone BUILD to de-risk" (the ψ↔π /
  θ↔π Abel-summation equivalence) and realized the θ↔π half needs NO Abel summation —
  only monotonicity of log + a nonnegative sub-sum bound.
- Wrote `proofs/Proofs/ChebyshevPNTBridgeOQ03OQ01.lean` (155 lines, 5 theorems, 1 def):
  - `chebyshevTheta_le_primeCounting_mul_log`: θ(n) ≤ π(n)·log n.
  - `tail_sum_le_chebyshevTheta`: ∑_{y<p≤n} log p ≤ θ(n).
  - `primeCounting_le_add_chebyshevTheta_div_log`: π(n) ≤ y + θ(n)/log y (2≤y≤n).
  - `chebyshev_theta_primeCounting_sandwich`: the packaged two-sided reduction.
- Reused existing infra: `ChebyshevThetaBound.chebyshevTheta` (ChebyshevThetaFourPow),
  `ChebyshevPNTBridge.numPrimesAbove_eq` & `.primeCounting_le`,
  `ChebyshevPNTBridgeOQ05.primeCounting_mono`.
- `docker-build.sh Proofs.ChebyshevPNTBridgeOQ03OQ01` → ✔ Built. `#print axioms` →
  only propext / Classical.choice / Quot.sound (no sorryAx, no ofReduceBool): **verified**.
- Created gallery entry `src/data/proofs/chebyshev-pnt-bridge-oq-03-oq-01/`
  (meta.json + annotations.json); passes `gallery:check-size:strict` and has 0
  annotation-validation errors.

### Key Findings
- The θ summation index set IS the set π counts (both `filter Prime (range (n+1))`),
  so θ(n) ≤ π(n)·log n collapses with no separate counting step.
- The threshold parameter y isolates the O(y) small primes that escape the tail
  bound; y ≈ n/(log n)² makes the errors o(n) → the sharp equivalence.

### Files Modified
- proofs/Proofs/ChebyshevPNTBridgeOQ03OQ01.lean (new)
- src/data/proofs/chebyshev-pnt-bridge-oq-03-oq-01/{meta,annotations}.json (new)
- src/data/research/problems/chebyshev-pnt-bridge-oq-03-oq-01.json (knowledge, phase ACT)
- .lean/state/candidate-pool.json (status → blocked, note updated)

### Next Steps
- Tendsto assembly θ(n)/n→1 ⟺ π(n)·log n/n→1 (elementary, fiddly).
- ψ↔θ transfer O(√x log²x) to complete the ψ~x ⟺ θ~x ⟺ π~x/log x chain.
- Deep PNT limit stays blocked (Wiener–Ikehara / Selberg).
