# Sperner Grid Instance: Mathematical Analysis

## Status

Analysis of the Freudenthal grid CellComplex instance (`SpernerGrid.lean`) for issue #8998.

## Key Finding: Boundary Flip Bug

### The Problem

`GridSimplex.boundaryFlip0` returns `none` (marking as boundary) when
`last_v.coords(miss) = 0`. This is correct for `d = 1` but **incorrect for d >= 2**.

**Concrete counterexample** (d=2, N=2):

```
Simplex s: miss=2, incDir=[0,1]
  v₀ = (0,0,2), v₁ = (1,0,1), v₂ = (1,1,0)

gridAdj at k=0: boundaryFlip0 checks v₂.coords(2) = 0 → returns none.

But the face {v₁, v₂} = {(1,0,1), (1,1,0)} is NOT on any geometric boundary:
  - v₁.coords(0)=1 ≠ 0, v₂.coords(0)=1 ≠ 0  (not on face 0)
  - v₁.coords(1)=0 but v₂.coords(1)=1 ≠ 0    (not on face 1)
  - v₁.coords(2)=1 ≠ 0                         (not on face 2)

The ACTUAL neighbor through this face is:
  s': miss=1, incDir=[0,2], base=(0,2,0)
  v₀'=(0,2,0), v₁'=(1,1,0), v₂'=(1,0,1)
```

### Why It's Missing

When the miss coordinate is depleted (`v_d.coords(miss) = 0`), the neighbor simplex
has a **different miss direction**. The current `boundaryFlip0` only handles
chain extension (same miss direction), not miss-direction changes.

### The Correct Fix

For face 0 when `v_d.coords(miss) = 0` and `d >= 2`:

```
new miss' = incDir(d-1)                           -- last incDir becomes new miss
new incDir' = (incDir(0), ..., incDir(d-2), miss)  -- old miss becomes last incDir
new v₀' = v_d + e_{incDir(d-1)} - e_{incDir(0)}   -- new base vertex
new vertices: v'_j for j >= 1 from the chain starting at v₀'
```

The shared face `{v₁, ..., v_d}` of `s` corresponds to
face 0 of `s'` with vertices in reversed order: `v'_j = s.verts(d+1-j)` for `j = 1,...,d`.

### Parity Argument: Bug Doesn't Affect Correctness

The mislabeled internal faces come in **symmetric pairs**: if `boundaryFlip0(s)` incorrectly
returns `none`, then `boundaryFlip0(s')` (the actual neighbor) also returns `none`.
Both sides count their shared face as "boundary," adding an **even** number to the
boundary door count. Since parity is preserved, `boundary_doors_odd` remains correct
despite the bug — but the boundary count is overcounted by an even number.

## Pre-existing Mathlib Compatibility Issues

Several helper proofs in `SpernerGrid.lean` are broken with the current Mathlib version:

1. **`miss_coord_at`** (line ~405): `Fin.val_natCast` and `Fin.castSucc` coercion API changed
2. **`base_miss_ge_d`** (line ~418): depends on `miss_coord_at`
3. **`incDir_surj_complement`** (line ~450): `Finset.mem_erase` / `Finset.card_erase_of_mem` API changed
4. **`BaryPoint.transfer.sum_eq`** (line ~459): `split_ifs <;> omega` needs `simp_all` for variable substitution

These were previously masked by `sorry`s in the step proofs. With the current Mathlib,
they need updates to use the current Fin and Finset API names.

## boundary_verts_on_face: Mathematically Incorrect

The lemma `boundary_verts_on_face` states:

> When `gridAdj s k = none` and `k < d`, all vertices `j ≠ k` have `(s.verts j).onFace k`.

This is **false**. Cell face position does NOT correspond to barycentric coordinate.
The same counterexample shows: face 0 of s has vertices v₁=(1,0,1) with coords(0)=1 ≠ 0.

### Impact on `no_boundary_doors_face_lt`

This lemma uses `boundary_verts_on_face` to argue that boundary doors at position `k < d`
can't exist. The argument is wrong because the face-coordinate correspondence doesn't hold.

However, for `0 < k < d`, `gridAdj` always returns `some` (dispatches to `interiorFlip`),
so `hbdry: gridAdj = none` is vacuously false and the lemma holds trivially.

For `k = 0`, the lemma is genuinely needed but the current proof approach is incorrect.

## Correct Architecture for boundary_doors_odd

The correct proof of `boundary_doors_odd` should:

1. **Fix `boundaryFlip0`** to handle the miss-change case
2. **Prove `boundaryFlipLast` correctly identifies geometric boundaries**:
   When `v₀.coords(incDir(d-1)) = 0`, all vertices `v₀,...,v_{d-1}` have
   coordinate `incDir(d-1) = 0`. This IS a correct geometric boundary identification. ✓
3. **Show boundary doors only occur at face d** (opposite last vertex):
   - Face k for 0 < k < d: always internal (interiorFlip), no boundary doors
   - Face 0: always internal for d >= 2 (after fixing boundaryFlip0), and
     for d = 1 it's on face `miss` where Sperner may or may not prevent doors
   - Face d: on geometric face `incDir(d-1)` when boundary. Sperner prevents
     color `incDir(d-1)` on this face, and if `incDir(d-1).val < d` then the
     door requiring color `incDir(d-1)` is blocked.
4. **Prove boundary doors at face d are odd by induction on d**

## interiorFlip: Verified Correct

The interiorFlip construction was verified correct by manual calculation:

```
s: miss=2, incDir=[0,1], verts=(0,0,2),(1,0,1),(1,1,0)
interiorFlip at k=1:
  s': miss=2, incDir=[1,0], verts=(0,0,2),(0,1,1),(1,1,0) ✓ valid

interiorFlip(s', 1) = s  ✓ self-inverse
```

The step proofs (step_inc, step_dec, step_same) follow a three-way case analysis:
- j = k_prev: use `transfer_coords_inc/dec/other` directly
- j = k: use `transfer_coords_other` + original step properties (step_same, step_inc)
- j ≠ k_prev, j ≠ k: delegates to original `s.step_inc/dec/same j`

## boundaryFlipLast: Verified Correct

Correctly identifies geometric boundary (v₀.coords(incDir(d-1)) = 0)
and correctly constructs neighbor in the non-boundary case.

## Recommended Next Steps

1. Fix pre-existing Mathlib compat issues (Fin API names, Finset API)
2. Complete interiorFlip step proofs (need interactive Lean session for Fin scoping)
3. Fix boundaryFlip0 with miss-change case
4. Prove boundaryFlip0 step proofs for both cases
5. Redesign boundary analysis (remove boundary_verts_on_face, prove boundary_doors_odd directly)
6. Complete gridAdj_symm, gridAdj_vertex, gridAdj_ne
