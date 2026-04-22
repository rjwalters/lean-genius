# sperner-ndim-oq-02: Boundary-Door Oddness by Dimensional Induction

## Problem Summary

**Goal**: Prove `SpernerGrid.boundary_doors_odd`: for the concrete Freudenthal grid
triangulation, the count of "boundary doors" (pairs (s, k) with `adj(s,k) = none`
and `IsDoor(c, gridComplex, s, k)`) is odd, for any Sperner coloring c.

This lemma is the key input to `CellComplex.sperner`, which then gives `sperner_grid`.

---

## Session 2026-04-22 (Session 1) - Critical Architectural Finding

**Mode**: FRESH
**Outcome**: BLOCKED — `boundary_doors_odd` is provably FALSE as stated.

### What I Did

1. Read `SpernerGrid.lean` thoroughly to understand the sorry structure (5 sorries)
2. Analyzed the abstract Sperner theorem in `SpernerMathlib4.lean`
3. Worked through a concrete counterexample for d=1, N=1

### Key Finding: `boundary_doors_odd` Is FALSE

**Counterexample**: d=1, N=1, unique Sperner coloring c(1,0)=0, c(0,1)=1.

The `gridComplex 1 1` has **2 GridSimplices** (not 1):
- S1: `miss=0, incDir(0)=1, verts(0)=(1,0), verts(1)=(0,1)`
- S2: `miss=1, incDir(0)=0, verts(0)=(0,1), verts(1)=(1,0)`

Both are valid (satisfy all `GridSimplex` axioms). They represent the **same geometric
edge** [(1,0),(0,1)] in **opposite orientations**.

**All 4 boundary pairs** (S1,k=0), (S1,k=1), (S2,k=0), (S2,k=1) have `adj = none`
(for N=1, all facets are boundary). Door check:
- (S1, k=1): c(verts 0) = c(1,0) = 0. **IS a door.** ✓
- (S1, k=0): c(verts 1) = c(0,1) = 1 ≠ 0. NOT a door.
- (S2, k=0): c(verts 1) = c(1,0) = 0. **IS a door.** ✓
- (S2, k=1): c(verts 0) = c(0,1) = 1 ≠ 0. NOT a door.

**Boundary door count = 2 (EVEN)**. The theorem claims Odd. **FALSE.**

### Root Cause

The `GridSimplex` structure uses ORIENTED simplices with a fixed "miss" direction.
Each geometric simplex appears **twice** in `gridComplex` — once per orientation:
- Orientation 1: `(miss=m1, incDir=σ1, verts=v₀→...→v_d)`
- Orientation 2: `(miss=m2, incDir=σ2, verts=v_d→...→v₀)` (reversed)

Consequence: both panchromatic count and boundary door count are ALWAYS EVEN.
The `sperner_parity` theorem still holds (both even ≡ both even mod 2), but
`CellComplex.sperner` (which needs ODD boundary doors) cannot be applied.

### Verification via `sperner_parity`

For d=1, N=1: panchromatic count = 2 (both S1 and S2 are panchromatic, since both
have vertex set {(1,0),(0,1)} with colors {0,1}). Boundary door count = 2. 
2 ≡ 2 (mod 2) ✓ — `sperner_parity` is consistent, but boundary ≠ odd.

### What IS Correct

- `sperner_parity`: panchromatic count ≡ boundary door count (mod 2) — **TRUE** (proved in SpernerMathlib4)
- `boundary_doors_odd` as stated in SpernerGrid.lean — **FALSE** (false for d ≥ 1)
- `sperner_grid` (conclusion): **TRUE** (panchromatic simplices do exist, count ≥ 2)

### The Fix Required

`boundary_doors_odd` cannot be proved as stated. The proof of `sperner_grid`
needs one of these alternatives:

**Option A: Canonical-orientation sub-complex**
- Define H ⊆ gridComplex using only "canonical" oriented simplices (one per geometric simplex)
- For d=1: choose the simplex with smaller miss coordinate
- H has boundary door count = (# geometric boundary doors) = ODD
- Apply `CellComplex.sperner` to H, conclude panchromatic in H → panchromatic in gridComplex

**Option B: Direct "reversal pairs" argument**
- Every GridSimplex s has a "reverse" s' (same vertex set, opposite orientation)
- s' is always a distinct valid GridSimplex
- panchromatic count in gridComplex = 2 × (# geometric panchromatic) = 2 × (odd) ≥ 2
- Requires proving the geometric count is odd via a separate argument

**Option C: Use SpernerNDim abstract structure**
- SpernerNDim.lean already has a working abstract Sperner theorem
- Define a `SpernerTriangulation` instance for the Freudenthal grid (with UNORIENTED simplices)
- Apply the existing abstract theorem

**Recommendation**: Option C is cleanest since the infrastructure in SpernerNDim.lean
already handles the parity argument correctly (using unoriented abstract simplices).

### Files Modified

None — pure analysis session.

### Other Sorries in SpernerGrid.lean

Beyond the false `boundary_doors_odd`, there are 2 other provable sorries:
1. `gridAdj_symm` (line 1154): adjacency symmetry — PROVABLE by case analysis
2. `gridAdj_vertex` (line 1163): shared vertices — PROVABLE for interior case at least
3. `boundary_verts_on_face` (line 1239): also appears incorrect (used only for `boundary_doors_odd` chain, which is now known-false)

### Next Steps

1. **Architectural decision**: Choose Option A, B, or C above
2. If Option C: define `SpernerTriangulation` instance for Freudenthal grid and apply SpernerNDim.sperner
3. Optionally prove `gridAdj_symm` and `gridAdj_vertex` (useful for any gridComplex application)
4. Remove or replace `boundary_doors_odd` and `boundary_verts_on_face` with correct formulations
