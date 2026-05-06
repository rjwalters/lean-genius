# Current State

**Phase**: ACT
**Since**: 2026-05-06
**Iteration**: 5

## Current Focus

1 axiom remaining: `sperner_panchromatic` — for each N>0, the Freudenthal grid of Δⁿ has a panchromatic (n+1)-tuple with f(vᵢ)ᵢ ≤ (vᵢ)ᵢ and diameter ≤ n/N.
PR #16308 open with session 5 changes (restructured proof, 341 lines, 0 sorries).

## Active Approach (Session 5 restructuring)

Sperner coloring: c(v) = min{i ∈ supp(v) : f(v)_i ≤ v_i}
- Well-definedness: algebraic (Finset.sum_lt_sum), PROVED
- Boundary condition: c(v) ∈ supp(v), PROVED
- brouwer_from_panchromatic: PROVED (0 sorries)
  - compactness + all vertices → x* via diameter bound
  - ge_of_tendsto on f(v_i)_i ≤ v_i_i limits → f(x*)_i ≤ x*_i
  - sum argument forces f(x*) = x*
- Main theorem: from 1 axiom (sperner_panchromatic), PROVED

## Blocker: FreudSimplex CellComplex

Must build a valid CellComplex for the Freudenthal grid triangulation.

### Why CellComplex (not SpernerTriangulation)

SpernerNDim.SpernerTriangulation requires `boundary_face` axiom:
`adj s k = none → ∀ j≠k, onFace (vertices s j) k`

This requires ALL non-k vertices to lie on face k simultaneously. For Freudenthal triangulations (any d≥2), different vertices have different k-th coordinates — impossible to all have coords[k]=0. INCOMPATIBLE.

Solution: use CellComplex from SpernerMathlib4.lean (only adj_symm, adj_vertex, adj_ne required).

### Correct FreudSimplex Design

```
FreudSimplex d N = { base : Fin d → ℕ, σ : Perm(Fin d) }
with: ∑ base[i] + d ≤ N  (so miss = N - ∑base ≥ d)
```

Fixed miss = last barycentric coordinate (canonical Fin.last d).

Vertex k (k : Fin(d+1)):
```
coords[j] = base[j] + (if σ⁻¹(j).val < k.val then 1 else 0)  for j : Fin d
miss = (N - ∑ base) - k.val
```

Adjacency:
- Face 0 (remove vertex 0): base' = vertex_1 = {base[j] + (if σ⁻¹(j).val = 0 then 1 else 0)}, σ' = shift left
- Face k (0 < k < d): swap σ(k-1) and σ(k), same base
- Face d (remove vertex d): none if miss = d (boundary); else extend
- adj_symm, adj_vertex, adj_ne: ~80 lines total

### boundary_doors_odd (needed as hypothesis to CellComplex.sperner)

For d=1: 1 boundary door (rightmost simplex, color 0 on last face). Trivial.
For d→d+1: boundary doors at face Fin.last d biject with FC simplices of FreudSimplex (d-1) N.
Apply sperner_ndim recursively → odd count. ~200 lines.

### Estimate

~280 lines total (FreudSimplex CellComplex ~80 + boundary_doors_odd ~200).
