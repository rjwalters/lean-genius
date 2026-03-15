# Knowledge Base: borsuk-ulam-oq-03-oq-03

## Problem Understanding

The 2D Borsuk-Ulam theorem proved via Tucker's lemma. File has main theorem
`borsuk_ulam_2d_corrected` with complete proof chain modulo axioms.

## Key Finding: False Axiom

`complementary_edge_gives_approximate_zero` was FALSE as stated.
Counterexample: g(x,y)=(x,y), u=(0.01,1), v=(-0.01,1), delta=0.02, k=0.
The bound 0.02*(2*sup) ~ 0.08 but ||g(w)||_1 >= 0.98 for any w near u.

Fix: require k to be the dominant component (as Tucker's labeling guarantees).

## Axiom Status

### Current (session 9, 2026-03-14)
- `tucker_2d_grid` -- 1 remaining axiom, properly constrained to triangulated grid
- Previous `tuckers_lemma` was overly general (false for empty edges)

### Infrastructure Added (session 9)
- `gridAntipodalFin_involution`: antipodal map is an involution (proved)
- `gridAntipodalFin_maps_boundary`: preserves boundary (proved)
- `gridAntipodalFin_preserves_edges`: preserves edge set (proved)
- Fixed Fin API breakage in `discrete_ivt` and `tucker_1d`

### Previously Eliminated
- `complementary_edge_gives_approximate_zero` -- ELIMINATED (was false)
- `tucker_disk_approx_zero` -- ELIMINATED (reordered file)
- `x_cube_sub_2_gal_iso_s3` -- ELIMINATED (from InverseGalois)

## Dead Ends

### Single-path arguments for Tucker 2D (CONFIRMED DEAD END)
A single path through the grid (diagonal, row, column) CANNOT prove Tucker 2D.

Labels from {(0,T), (0,F), (1,T), (1,F)} allow complementary-free paths:
  (0,T) -> (1,F) -> (0,F) has 0 complementary edges despite complementary endpoints.

Parity analysis on diagonal path (0,0) -> (2N,2N):
- Sign changes (Ce + Cb) = ODD (antipodal condition)
- Component changes (Co + Cb) = EVEN (same start/end component)
- Ce - Co = ODD, but Ce = 0 is consistent (all sign changes coincide with component changes)

### Row-by-row 1D Tucker (CONFIRMED DEAD END)
Bottom row sign change NOT guaranteed from boundary conditions.
The antipodal condition links (0,j) <-> (2N, 2N-j), not same-row endpoints.

### Hex theorem (PARTIALLY VIABLE)
Hex gives connected same-component path. But monochromatic case
needs additional argument: must show antipodal vertex is in same
connected component, or use separation/Jordan curve theorem.

## Proof Approaches for tucker_2d_grid

All three are equivalent to Brouwer FPT in 2D. Multi-session project.

1. **Path-following / complementary pivoting** (~500-1000 lines)
2. **Hex theorem reduction** (~300 lines + Hex proof ~300-500 lines)
3. **Poincare-Miranda / intersection theory** (~300-500 lines)
