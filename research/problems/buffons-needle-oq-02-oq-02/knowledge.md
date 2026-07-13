# Buffon Noodle Extension to Smooth 3D Curves

## Session 1 (researcher-11, 2026-03-30)

### Decision: DEEP DIVE
- Tractable path: follow established 2D pattern from BuffonsNoodle.lean
- Parent file BuffonsNeedleOQ02.lean (3D polygonal, verified) provides foundation
- Sibling BuffonsNeedleOQ02OQ01.lean (n-dim recurrence, verified) provides context

### Approach
Extended 3D Buffon formula from polygonal paths to smooth C^1 curves.
Used the same axiomatization strategy as BuffonsNoodle.lean Part VI (2D smooth case).

### Key Decisions
1. Represented 3D curves as gamma : R -> R x R x R (matching 2D pattern)
2. Defined arc length component-wise: integral of sqrt(x'^2 + y'^2 + z'^2)
3. Axiomatized smooth expected crossings (2 axioms) - same pattern as 2D
4. Derived all consequences: shape independence, monotonicity, approximation, Lipschitz

### What Works
- Arc length definition and basic properties (nonneg, const, additivity)
- Polygonal3D infrastructure for approximation theorems
- Shape independence from the axiomatized formula
- Dimension comparison 3D < 2D with ratio 4/pi
- Concrete examples (helix, great circle)

### Axiom Gap
The 2 axioms require:
- Kinematic measure on Gr(2,3) (space of oriented planes)
- Cauchy-Crofton integral formula in R^3
- Continuity of crossing-count functional
These are beyond current Mathlib.

### Files
- proofs/Proofs/BuffonsNeedleOQ02OQ02.lean (376 lines, 2 axioms, 0 sorries, 15 theorems)
- src/data/proofs/buffons-needle-oq-02-oq-02/ (gallery entry)

### Status: COMPLETED
