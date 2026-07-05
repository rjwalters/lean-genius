# Research State: sperner-simplicial-instance-oq-04

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-07-02
**Iteration**: 1

## Current Focus
Prior work exists: part (a) (continuous-coloring → Sperner-coloring reduction) is
DONE in `proofs/Proofs/SpernerSimplicialInstanceOQ04.lean` (no sorry/axiom). The open,
tractable target is **part (b)**: the continuous 1-d IVT via mesh refinement +
Bolzano–Weierstrass, promoting `exists_sign_change_cell` to a genuine root
$f(x_0) = 0$. Read `problem.md` and `knowledge.md`, then resume at part (b).

## Active Approach
Mesh refinement + sequential compactness of `[0,1]` to pass the discrete sign-change
cells to a continuous root.

## Attempt Count
- Total attempts: 0 (this workspace); part (a) completed in prior session
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None. Part (c) ($n$-d Brouwer) is intentionally out of scope.

## Next Steps
1. Review `SpernerSimplicialInstanceOQ04.lean` and `exists_sign_change_cell`.
2. Formalize the Bolzano–Weierstrass limit argument (part (b)).
3. Keep part (c) deferred.
