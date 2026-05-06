# Problem: Brouwer's Fixed-Point Theorem via Sperner's Lemma

**Pool ID**: sperner-ndim-mathlib-oq-02  
**Status**: in-progress  
**Phase**: ACT
**Progress**: axiomCount 2→1 (fixed_point_from_approx proved); sperner_near_fixed_point requires FreudSimplex triangulation (~400 lines, boundary_doors_odd is the core)

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

## Session 2026-05-06 (Session 4) — Deep analysis of triangulation barrier

**Mode**: REVISIT (continuing Session 3 analysis)
**Outcome**: no code progress — confirmed concrete implementation plan, ruled out shortcuts

### What I Did

- Verified Mathlib4 (from /Users/rwalters/GitHub/mathlib4) has NO topological Brouwer theorem
  (only order-theoretic Brouwer for lattices, not fixed points for compact convex sets)
- Confirmed the old FSimplex (constant miss = Fin.last d) approach from git eaab632 is broken:
  boundary_face axiom fails for face k < d because base[k] may be > 0
- Analyzed the correct FreudSimplex formulation with σ : Equiv.Perm (Fin(d+1))
- Confirmed boundary_doors_odd proof requires induction: boundaries of d-triangulation =
  FC simplices of (d-1)-triangulation, proved by applying sperner_ndim inductively
- Ruled out IVT shortcut (only gives one coordinate correct, not all simultaneously for n≥2)
- Confirmed no shortcut exists: full Freudenthal triangulation is required

### Key Findings

- **Mathlib has no Brouwer**: confirmed by searching /Users/rwalters/GitHub/mathlib4 — no
  topological fixed-point theorem for compact convex sets exists in current Mathlib
- **FSimplex constant-miss is broken**: old approach (countPerm, constant miss = Fin.last d)
  fails boundary_face for face k < d. The miss direction must encode which geometric face
  each simplex is "opposite" to, not be fixed globally
- **Correct FreudSimplex type**: `(base : Fin(d+1) → ℕ, σ : Equiv.Perm (Fin(d+1)))` where
  Σ base_i = N, base[σ(d)] ≥ d (miss direction has enough mass). Vertex k formula:
  - u_k[σ(j)] = base[σ(j)] + (1 if j < k else 0) for j < d (steps in non-miss directions)
  - u_k[σ(d)] = base[σ(d)] - k (miss direction decreases by 1 per step)
  - Σ u_k = N ✓ (sum preserved since each step adds e_{σ(j)} - e_{σ(d)})
- **Correct adjacency**: for face position k (removing vertex k from (base, σ)):
  - Middle faces (0 < k < d): swap σ(k-1) and σ(k) → (base, σ') where σ' transposes k-1 and k
  - Face 0 (remove vertex 0): base' = base + e_{σ(0)} - e_{σ(d)}, σ' = σ with σ(0) moved to end
  - Face d (remove vertex d): none if base[σ(d)] = d (boundary); otherwise modify base
  - The key: σ(d) = "miss direction", and changing the face changes which direction is missed
- **boundary_doors_odd induction**: boundary doors at (Fin.last d) of FreudSimplex d N
  biject with FC simplices of FreudSimplex (d-1) N restricted to "face σ(d)". By induction
  (sperner_ndim applied to d-1), FC count is odd → boundary doors are odd
- **Vertex labeling for boundary_doors**: must place vertex d = Fin.last d at the "largest"
  position (i.e., K.vertices S (Fin.last d) = vertex on the geometric boundary face d).
  Then isDoorAt condition checks that the remaining d vertices have all colors 0..d-1

### Files Modified

- `research/problems/sperner-ndim-mathlib-oq-02/knowledge.md` (this file)

### Next Steps

1. **Build FreudSimplex with correct full-permutation type** (Session 5):
   - `FreudSimplex d N = (base : Fin(d+1) → ℕ, σ : Perm(Fin(d+1)))` with Σbase=N, base[σ(d)]≥d
   - Vertex k formula: u_k[σ(j)] = base[σ(j)] + (j<k ? 1 : 0) for j<d; u_k[σ(d)] = base[σ(d)]-k
   - Convert u_k to Vertex d N: vertex.coords[j'] = u_k[Fin.castSucc j']
2. **Prove easy SpernerTriangulation axioms**:
   - vertices_injective: vertices at different k differ in exactly one coordinate
   - adj_ne: adjacent simplices differ (since adj swaps permutation elements, changing a vertex)
   - boundary_face: adj S (Fin.last d) = none ↔ base[σ(d)] = d; then all non-d vertices
     have their σ(d)-th coordinate = 0, so they're on face σ(d)
3. **Prove hard axioms** (adj_symm, adj_vertices, adj_unique_facet): ~150 lines
4. **Prove boundary_doors_odd by induction**: ~150 lines; the key is showing the restriction map
   FreudSimplex d N → FreudSimplex (d-1) N (by removing the σ(d) direction) is a bijection
   between boundary doors of d-triangulation and FC simplices of (d-1)-triangulation
5. **Connect to sperner_near_fixed_point**: after boundary_doors_odd, apply sperner_ndim,
   convert FC simplex to near-fixed-point using continuity + mesh size bound

## Session 2026-05-06 (Session 5) — Restructure: sperner_panchromatic + brouwer_from_panchromatic

**Mode**: REVISIT (continuing axiom elimination work)
**Outcome**: significant progress — restructured proof with cleaner axiom and new proved theorem

### What I Did

- Identified root cause of boundary_face incompatibility: for d≥2, no Freudenthal triangulation can have all non-k vertices simultaneously on face k (required by SpernerNDim.SpernerTriangulation.boundary_face). Session 4's state.md already documented this.
- Identified that sperner_near_fixed_point required Lipschitz continuity (not in hypothesis) to extract near-fixed-point bounds from panchromatic simplex — making it equivalent in difficulty to Brouwer itself.
- Redesigned proof: replaced near-fixed-point intermediary with direct limit of panchromatic tuples.
- Wrote and proved brouwer_from_panchromatic (0 sorries, 1 axiom sperner_panchromatic).
- Docker build confirmed: ✔ Built Proofs.SpernerNDimMathlibOQ02

### Key Findings

- **boundary_face incompatibility confirmed**: SpernerNDim.SpernerTriangulation requires adj s k = none → ∀ j≠k, onFace (vertex j) k. For Freudenthal, the non-k vertices span different coordinate values — only one vertex can be "on face k", never all d. This blocks SpernerNDim.sperner_ndim entirely.
- **sperner_near_fixed_point requires Lipschitz**: the near-fixed-point bound (n+1)/(N+1) per coordinate simultaneously requires Lipschitz continuity of f to extract from a panchromatic simplex — which is not in the hypothesis.
- **Correct approach — panchromatic tuples**: axiom sperner_panchromatic just states f(vᵢ)ᵢ ≤ (vᵢ)ᵢ (one-sided, per i) and diameter bound — exactly what CellComplex.sperner gives directly.
- **brouwer_from_panchromatic proof works via ge_of_tendsto**: limit of f(v_{φk,i})ᵢ ≤ v_{φk,i}ᵢ gives f(x*)ᵢ ≤ x*ᵢ. Sum of 1=1 forces all equalities.
- **CellComplex (not SpernerTriangulation)**: Mathlib's CellComplex from SpernerMathlib4.lean has only adj_symm, adj_vertex, adj_ne — no boundary_face required. This is the right target for the Freudenthal grid.

### Files Modified

- `proofs/Proofs/SpernerNDimMathlibOQ02.lean` (299→341 lines, axiom changed from sperner_near_fixed_point to sperner_panchromatic, fixed_point_from_approx replaced by brouwer_from_panchromatic)
- `src/data/proofs/sperner-ndim-mathlib-oq-02/meta.json` (lineCount, assumptions, sections updated)

### Next Steps

1. Build CellComplex for Freudenthal grid triangulation (~80 lines):
   - Type: `FreudSimplex d N = { base : Fin d → ℕ, σ : Perm(Fin d) }` with fixed miss = Fin.last d
   - Vertex k: coords[j] = base[j] + (if σ⁻¹(j).val < k.val then 1 else 0)
   - adj: swap σ positions for middle faces, shift for face 0, extend for face d
   - Prove adj_symm, adj_vertex, adj_ne (no boundary_face needed!)
2. Prove boundary_doors_odd by induction (~200 lines):
   - Base: d=0 trivial (1 simplex, 1 boundary door)
   - Inductive: boundary doors at face d = FC simplices of (d-1) triangulation (bijection)
   - Apply CellComplex.sperner for (d-1) recursively
3. Instantiate sperner_panchromatic from CellComplex.sperner + FreudSimplex
