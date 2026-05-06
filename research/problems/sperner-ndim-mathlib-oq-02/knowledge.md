# Problem: Brouwer's Fixed-Point Theorem via Sperner's Lemma

**Pool ID**: sperner-ndim-mathlib-oq-02  
**Status**: in-progress  
**Phase**: ACT
**Progress**: axiomCount 2→1 (fixed_point_from_approx proved, sperner_near_fixed_point remains)

## Summary

Prove Brouwer's fixed-point theorem for Δⁿ = {x : Fin(n+1) → ℝ | ∀i, xᵢ ≥ 0, Σxᵢ = 1}
using the combinatorial Sperner's lemma approach (SpernerNDimMathlib.lean, 0 axioms).

The key insight: for f: Δⁿ → Δⁿ, define the Sperner coloring c(v) = min{i ∈ supp(v) : f(v)ᵢ ≤ vᵢ}.
This is well-defined (proved algebraically) and satisfies the Sperner boundary condition (proved).
The existence of a fixed point then follows from Sperner's lemma + compactness.

## Session 2026-05-06 (Session 1) — Initial formalization

**Mode**: FRESH  
**Outcome**: progress

### What I Did

- Branched `feature/researcher-11-sperner-ndim-mathlib-oq-02` from origin/main
- Created `proofs/Proofs/SpernerNDimMathlibOQ02.lean` (254 lines, 0 sorries, 2 axioms)
- Created gallery entry `src/data/proofs/sperner-ndim-mathlib-oq-02/` (meta.json, index.ts, annotations.json)
- Added entry to `src/data/proofs/listings.json`
- PR pending Docker build

### Key Findings

- **Coloring well-definedness is purely algebraic**: if f(v)ᵢ > vᵢ for all i ∈ supp(v), and 0 ≤ f(v)ᵢ for i ∉ supp(v), then Σf(v)ᵢ > Σvᵢ = 1. Proved by `Finset.sum_lt_sum`.
- **Boundary condition follows trivially**: c(v) ∈ supp(v) by definition, so vⱼ = 0 → j ∉ supp(v) → c(v) ≠ j.
- **2 axioms are sufficient**: (1) grid triangulation + Sperner → near-fixed-point, (2) compactness → exact fixed point.
- **Fundamentally different from algebraic topology approach**: avoids homology theory entirely.

### Files Modified

- `proofs/Proofs/SpernerNDimMathlibOQ02.lean` (new)
- `src/data/proofs/sperner-ndim-mathlib-oq-02/` (new)
- `src/data/proofs/listings.json` (entry added)
- `src/data/research/problems/sperner-ndim-mathlib-oq-02.json` (knowledge updated)

### Next Steps

1. Eliminate `sperner_near_fixed_point` axiom: build the grid CellComplex for Δⁿ
   - Vertices: (a₀/N,...,aₙ/N) with Σaᵢ = N, aᵢ ∈ ℕ
   - Simplices: ordered chains with constant "miss" direction
   - Must fix boundary_doors_odd (broken in SpernerGrid.lean due to double-representation)
   - Estimated: ~200 lines
2. ~~Eliminate `fixed_point_from_approx` axiom~~ — **DONE in Session 2**

## Session 2026-05-06 (Session 2) — Prove compactness convergence step

**Mode**: REVISIT (continuing Session 1 work)  
**Outcome**: progress — axiomCount 2→1 (fixed_point_from_approx proved)

### What I Did

- Replaced `axiom fixed_point_from_approx` with a proved `theorem`
- Key API pattern from `SpernerNDimOQ03.lean`: `isCompact_univ_pi (fun _ => isCompact_Icc)`
- Key API pattern from `Erdos1201Problem.lean`: `tendsto_const_nhds.div_atTop`
- Build confirmed: `✔ Built Proofs.SpernerNDimMathlibOQ02 (12s)`
- PR #16235 updated

### Key Findings

- **Simplex compactness API**: `isCompact_univ_pi (fun _ => isCompact_Icc)` + `IsCompact.of_isClosed_subset` + `isClosed_iInter` + `isClosed_eq` — exact pattern from SpernerNDimOQ03.lean
- **Tendsto composition fix**: use `hf_cont.tendsto x` not `hf_cont.continuousAt.comp` for `Filter.Tendsto.comp`
- **Finset.single_le_sum API**: `(fun j _ => h j) (Finset.mem_univ i)` — no extra `_` argument between hf and ha
- **div_atTop**: `tendsto_const_nhds.div_atTop h_phi_atTop` proved the bound → 0 step cleanly
- **congr' step**: needs `simp only [Function.comp, Pi.add_apply, Pi.sub_apply]; ring` to unfold `u ∘ φ`

### Files Modified

- `proofs/Proofs/SpernerNDimMathlibOQ02.lean` (254→299 lines, axioms 2→1)
- `src/data/proofs/sperner-ndim-mathlib-oq-02/meta.json` (axiomCount, lineCount, sections updated)

### Next Steps

1. Eliminate `sperner_near_fixed_point` (the 1 remaining axiom)
   - Fix `boundary_doors_odd` in SpernerGrid.lean (known false for d=1, needs redesign)
   - Build a correct grid CellComplex and plug into SpernerAbstract.sperner
   - Very hard: requires fundamental redesign of GridSimplex/gridAdj

## Session 2026-05-06 (Session 3) — Axiom elimination assessment

**Mode**: REVISIT (continuing to work on last axiom)
**Outcome**: no code progress — fundamental barrier confirmed and documented

### What I Did

- Audited all related Lean files: SpernerGrid.lean (1782 lines), SpernerNDim.lean (669 lines),
  SpernerFreudenthal.lean (359 lines), SpernerNDimOQ03.lean (452 lines, uses undefined FSimplex)
- Confirmed `boundary_doors_odd` is FALSE for SpernerGrid.lean (d=1, double-counting)
- Assessed KKM approach: n-dim KKM not in Mathlib; equivalent effort required
- Assessed Schauder: available in gallery but not the intended proof strategy (OQ-02 = Sperner route)
- Assessed IVT for n=1: gives exact fixed point for Δ¹ but doesn't extend to arbitrary n
- Identified correct proof structure: induction on n using `SpernerNDim.SpernerTriangulation`

### Key Findings

- **Correct proof path**: Use `SpernerNDim.sperner_ndim` with a canonical Freudenthal grid triangulation
- **Inductive structure**: boundary doors on face d ↔ FC (n-1)-simplices on restriction to face d;
  base case n=0 trivial, inductive step reduces dimension by 1
- **Design requirement**: Canonical simplex representation — `GridSimplex n N = (base, σ)` where
  `σ : Equiv.Perm (Fin(n+1))` gives the step order, avoiding SpernerGrid's double-counting issue
- **Effort estimate**: ~400 lines for correct triangulation + adjacency proofs + restriction map
- **SpernerNDimOQ03.lean** uses `FSimplex` and `countPerm` that no longer exist in SpernerNDim.lean;
  that file likely doesn't compile (possibly stale gallery entry)

### Files Modified

- `research/problems/sperner-ndim-mathlib-oq-02/state.md` (updated with correct blocker description)

### Next Steps

1. Build canonical `SpernerTriangulation n N` for Freudenthal grid:
   - `GridSimplex n N` = `(base : Fin(n+1) → ℕ, σ : Equiv.Perm (Fin(n+1)))` with Σ base = N
   - `gridAdj`: swap adjacent steps (local transposition) for adjacency
   - Prove adj_symm, adj_vertices, adj_ne, boundary_face, adj_unique_facet
2. Prove `boundary_doors_odd` by induction via restriction to face d
3. Connect to `sperner_near_fixed_point` via `SpernerNDim.sperner_ndim`
