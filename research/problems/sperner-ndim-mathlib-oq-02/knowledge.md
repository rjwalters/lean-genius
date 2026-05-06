# Problem: Brouwer's Fixed-Point Theorem via Sperner's Lemma

**Pool ID**: sperner-ndim-mathlib-oq-02  
**Status**: in-progress  
**Phase**: ACT
**Progress**: axiomCount 2→1 (fixed_point_from_approx proved); sperner_panchromatic requires FreudSimplex CellComplex (adjacency formulas now fully derived, boundary_doors_odd proof strategy identified)

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

## Session 2026-05-06 (Session 6) — Complete FreudSimplex adjacency derivation

**Mode**: REVISIT (continuing axiom elimination work)
**Outcome**: significant insight — complete adjacency formulas derived, proof strategy for boundary_doors_odd identified, companion file written

### What I Did

- Derived complete adjacency formulas for FreudSimplex CellComplex (all 3 cases)
- Identified the correct `leftRotPerm`/`rightRotPerm` helpers for face-0/face-n adjacency
- Proved that adj_symm and adj_ne hold (conceptually, via base-change and swap-involution arguments)
- Identified why boundary_doors_odd works: face-n boundary doors are NOT IsDoor (Sperner condition)
- Written companion file `SpernerFreudenthalSimplex.lean` with proof structure and sorry'd hard parts
- Key finding: boundary_doors_odd reduces to n-1 dimensional case by bijection

### Key Mathematical Findings

- **Correct adjacency for FreudCell(n,N)**:
  - Face k ∈ {1,...,n-1}: `adj (base,σ) k = some ((base, σ∘swap(k-1,k)), k)` — always valid
  - Face 0: `adj (base,σ) 0 = some ((base+e_{σ(0)}-e_{miss}, leftRot(σ)), Fin.last n)` when base[miss]>n; none when base[miss]=n
  - Face n: `adj (base,σ) n = some ((base-e_{σ(n-1)}+e_{miss}, rightRot(σ)), 0)` when base[σ(n-1)]≥1; none when base[σ(n-1)]=0

- **adj_symm**: face-0 and face-n are mutually inverse (leftRot∘rightRot=id), middle faces are involutions (swap²=id). ✓ provable.

- **adj_ne**: face-0 changes base at σ(0); face-n changes base at σ(n-1); middle changes σ. All give s≠s'. ✓ provable.

- **boundary_doors_odd strategy**:
  1. Boundary faces: face-0 (adj=none ↔ base[miss]=n) and face-n (adj=none ↔ base[σ(n-1)]=0)
  2. Face-n boundary doors are NOT IsDoor: kept vertices {v₀,...,v_{n-1}} all have σ(n-1)-th coord = 0 (since base[σ(n-1)]=0 means v_j[σ(n-1)]=base[σ(n-1)]+1 = 1 only for j>0, but v_0[σ(n-1)]=base[σ(n-1)]+0=0). Wait actually: v_j[σ(n-1)] = base[σ(n-1)] + 1_{σ^{-1}(σ(n-1))<j} = 0+1_{(n-1)<j} so v_{n-1}[σ(n-1)]=0, v_j[σ(n-1)]=0 for j<n-1, and the Sperner condition says c(v) ≠ σ(n-1) when v[σ(n-1)]=0. So no vertex can have color σ(n-1), so IsDoor (which requires all colors 0..n-1 to appear) fails if σ(n-1) ∈ {0,...,n-1}.
  3. Face-0 boundary doors (base[miss]=n) biject with FC cells of the (n-1)-dim FreudSimplex restricted to face `miss` (where coord[miss]=0). The bijection: drop the miss coordinate from vertices {v_1,...,v_n}.
  4. By induction, (n-1)-dim FC count is odd. So face-0 boundary door count is odd. ✓

- **Diameter bound**: |vertCoord k₁ i - vertCoord k₂ i| ≤ n (miss coord: |k₁-k₂| ≤ n; non-miss: ≤1). So real diameter ≤ n/N. ✓ proved.

- **Fintype FreudCell n N**: bounded subtype of (Fin(n+1)→Fin(N+1)) × Perm(Fin(n+1)), hence finite. Requires embedding proof (~20 lines). ✓ provable.

### Files Modified

- `research/problems/sperner-ndim-mathlib-oq-02/knowledge.md` (this file)
- `proofs/Proofs/SpernerFreudenthalSimplex.lean` (new companion file, proof structure, 6 sorries)

### Remaining Sorries in Companion File

1. `FreudCell.fintype`: subtype of finite type — HARD, ~20 lines
2. `perm_preimage_lt_card`: cardinality argument — HARD, ~15 lines
3. `FreudCell.vertCoord_sum`: algebraic sum — HARD, ~25 lines
4. `freudAdj_symm` (face 0/n cases): case analysis — HARD, ~40 lines
5. `freudAdj_vertex`: shared face correctness — HARD, ~50 lines
6. `freudBoundaryDoorsOdd`: inductive Sperner parity — OPEN (core mathematical content, ~150 lines)

### Next Steps

1. **Complete `freudAdj_symm`**: The leftRot/rightRot pair is mutually inverse. Key: leftRotPerm ∘ rightRotPerm applied to σ gives σ back. And base roundtrips. ~40 lines.
2. **Complete `freudAdj_vertex`**: Verify the shared vertices formula explicitly. For middle faces: v'_j = v_j for j≠k (proved). For face 0/n: follows from construction. ~50 lines.
3. **Prove `freudBoundaryDoorsOdd` by induction**:
   - Base n=0: 1 boundary face, coloring trivially gives IsDoor, count = 1 (odd) ✓
   - Inductive: face-n doors not IsDoor (proved above); face-0 doors = FC(n-1) cells by bijection; IH gives odd count. ~150 lines.
4. **Connect companion to main file**: Import `SpernerFreudenthalSimplex` and replace `axiom sperner_panchromatic` with `theorem sperner_panchromatic := SpernerBrouwer.freud_sperner_panchromatic`. ~5 lines.
5. **Run Docker build** to confirm 0 sorries, 0 axioms.

**Estimated effort for full completion**: 2-3 more sessions (~280 lines of Lean).

## Session 2026-05-06 (Session 7) — Adjacency formula audit: bug found, correct formula derived

**Mode**: REVISIT (continuing axiom elimination work)
**Outcome**: critical bug found — face-0 adj formula in companion file is WRONG; correct formula derived for n=2

### What I Did

- Audited SpernerFreudenthalSimplex.lean's adjacency definition against the actual Freudenthal triangulation
- Identified that face-0 adjacency formula (`leftRotPerm`, `face0Adj`) is incorrect
- Derived the CORRECT face-0 adjacency via concrete n=2, N=3 example
- Identified that face-n adjacency and middle-face adjacency ARE correct
- Identified SpernerSimplicialInstance.lean as having proved adj axioms for AbstractSimplicialData
- Proved pseudomanifold property holds for the chain-based triangulation (SpernerFreudenthal.lean)

### Key Mathematical Findings

**CRITICAL BUG**: In SpernerFreudenthalSimplex.lean, `face0Adj` is wrong. My condition `adj(s,0)=none iff base[miss]≤n` is incorrect. For n=2, face-0 is ALWAYS interior (adj ≠ none), but my formula says adj=none when base[miss]=n.

**Correct face-0 adjacency (derived by concrete verification)**:
- For cell (base,σ): the adjacent cell at face 0 is (b, τ) where:
  - **τ = σ ∘ swap(n-1, n)** [swap last two positions in σ's domain, NOT leftRotPerm]
  - **new miss' = σ(n-1)** [old second-to-last step becomes new miss]
  - **b = base + 2·e_{σ(n-1)} + Σ_{k=1}^{n-2} e_{σ(k)} - n·e_{miss}** [complex formula, n≥2]
  - **k' = 0** [face 0 of adjacent cell contains the shared vertices]
  - **Validity**: b[miss'] = base[σ(n-1)] + 2 ≥ n, i.e., base[σ(n-1)] ≥ n-2
- For n=2: condition base[σ(1)] ≥ 0 is always true → face-0 NEVER has adj=none ✓
- For n≥3: adj(s,0)=none iff base[σ(n-1)] < n-2 (may occur for interior face, meaning formula fails for n≥3)

**Verified example** (n=2, N=3):
- Cell ((0,1,2), id): σ=id, miss=2, base[σ(1)=1]=1≥0 ✓
- face-0 adj: b = (0,1,2) + 2·e_1 - 2·e_2 = (0,3,0), τ = id∘swap(1,2) = swap(1,2)
- Cell ((0,3,0), (1↔2)): miss'=τ(2)=1, base'[1]=3≥2 ✓, vertices {(0,3,0),(1,2,0),(1,1,1)}
- Shared face {(1,1,1),(1,2,0)} = face 0 of original and face 0 of adjacent. ✓ adj_symm ✓

**Face-n adjacency IS correct**: adj(s,n)=none iff base[σ(n-1)]=0. When none, kept vertices
{v_0,...,v_{n-1}} all have σ(n-1)-th coordinate = 0, so face is on F_{σ(n-1)} ⊂ ∂Δⁿ. ✓

**Middle-face adjacency IS correct**: (base, σ∘swap(k-1,k)) for 0<k<n. ✓

**Pseudomanifold property for SpernerFreudenthal.lean's chain-based triangulation**:
- Cells = chains ∅ ⊂ {σ(0)} ⊂ {σ(0),σ(1)} ⊂ ... ⊂ Fin(n) for σ ∈ Perm(Fin n)
- Each codim-1 face (chain with one set removed at position k):
  - k=0 or k=n: exactly 1 chain contains it (boundary) → on ∂Δⁿ ✓
  - 0<k<n: exactly 2 chains contain it (insert either of 2 choices for P_k) → interior ✓
- Pseudomanifold ≤ 2 for all faces ✓ — **this is provable in ~50 lines**

### Files Modified

- `research/problems/sperner-ndim-mathlib-oq-02/knowledge.md` (this file)

### Path Forward

**Option A — Fix FreudCell** (scaled triangulation with real diameter n/N):
1. Rewrite `face0Adj` with correct formula: τ=σ∘swap(n-1,n), b=base+2e_{σ(n-1)}+Σe_{σ(k)}-ne_{miss}
2. Fix condition for adj(s,0)=none: base[σ(n-1)] < n-2 (for n≥3); never for n=2
3. For n≥3: the formula above still needs derivation/verification
4. Prove adj_symm and adj_vertex for the corrected formulas
5. Prove boundary_doors_odd by induction

**Option B — Use SpernerFreudenthal.lean** (chain-based, scale=1):
1. Prove pseudomanifold for `topSimplices n` (~50 lines) — now known to be correct
2. Use SpernerSimplicialInstance.lean's proved toTriangulation (adj axioms already proved)
3. Define the Sperner coloring on Finset(Fin n) vertices → Fin(n+1) based on f
4. Prove boundary_doors_odd for the chain-based triangulation
5. Connect diameter bound: chain-based triangulation gives diameter O(1), NOT n/N
   — PROBLEM: diameter bound needs scaling, chain-based triangulation does NOT give n/N

**Assessment**: Option A requires fixing the adjacency formula (complex for n≥3) but gives the needed diameter bound. Option B avoids adjacency issues but the diameter bound connection is unclear.

**Recommended next step**: For Option A, verify the face-0 formula for n=3 by hand (concrete example), then implement the corrected `face0Adj`. Estimated: 1 more session for correct adj + 1 for boundary_doors_odd.

**Alternative next step**: Submit boundary_doors_odd to Aristotle with the current (wrong) adj setup for async exploration while fixing adj manually.

**Note on SpernerGrid.lean**: boundary_doors_odd there is also sorry'd and marked FALSE for d=1 due to double-counting. FreudCell avoids double-counting (18 cells = N²·n! for n=2,N=3 ✓) but has wrong adj formulas. The fix is purely in the adjacency, not the cell count.

## Session 2026-05-06 (Session 8) — Fundamental n≥3 failure diagnosed; perm_preimage_lt_card fixed

**Mode**: REVISIT (continuing axiom elimination work)
**Outcome**: 1 sorry eliminated; fundamental blocker for n≥3 identified and rigorously proven

### What I Did

- Fixed `perm_preimage_lt_card` sorry in companion file (1 of 11 sorries eliminated)
- Rigorously verified the FreudCell constant-miss triangulation is fundamentally broken for n≥3
- Analyzed the cell count: FreudCell gives C(N,n)×(n+1)! simplices total (correct for n=2, wrong for n=3)
- Computed concrete counter-example showing face-0 adj=none for geometrically-interior face in n=3

### Key Mathematical Findings

**FUNDAMENTAL FAILURE FOR n≥3**: The constant-miss FreudCell triangulation is not a valid
pseudomanifold for n≥3. Concretely:
- Cell (base=(0,0,0,4), σ=id, n=3, N=4): face-0 = {v_1,v_2,v_3} = {(1,0,0,3),(1,1,0,2),(1,1,1,1)}
- The face is geometrically INTERIOR (v_3=(1,1,1,1) has all positive coordinates)
- But no other constant-miss FreudCell can share this face (only valid ordering of {v_1,v_2,v_3}
  with constant miss direction leads back to the same cell with b=v_0)
- Session 7 formula also gives adj=none here (base[σ(2)=2]=0 < n-2=1)
- Therefore FreudCell claims an interior face is a boundary face: the Sperner parity argument FAILS

**Why it works for n=2**: For n=2, face-0 adjacent cell has same miss direction (proved by session 7
concrete verification). The n=2 case is well-defined. But face-0 adjacency for n≥3 requires
variable-miss adjacent cells, which constant-miss FreudCell cannot represent.

**Cell count analysis** (using formula Σ_{k=n}^{N} C(k+n-1,n-1)):
- Per permutation: C(N,n) cells. Total: C(N,n)×(n+1)!
- n=2, N=3: C(3,2)×6=18 ✓ (Euler's formula verified: 6 vertices, 12 edges, 6 triangles for N=2)
- n=3, N=4: C(4,3)×24=96. But valid Freudenthal triangulation needs more (face-0 adjacencies missing)

**perm_preimage_lt_card fix**: 
Proved `|{j<k}|=k.val` via:
```lean
have heq : ... filter = univ.image (Fin.castLE k.isLt) := ...
rw [heq, card_image_of_injective _ (fun a b h => Fin.ext (congrArg Fin.val h))]
exact Fintype.card_fin k.val
```

**n=1 case is directly provable**: sperner_panchromatic for n=1 follows from discrete IVT (~60 lines):
- c(0) = 1 (supp={(1)}, f(v)_1 ≤ 1 always), c(N) = 0 (supp={(0)}, f(v)_0 ≤ 1 always)
- Last k with c(k)=1: c(k+1)=0, giving adjacent pair with all colors, diameter 1/N ≤ 1/N ✓

### Files Modified

- `proofs/Proofs/SpernerFreudenthalSimplex.lean` (perm_preimage_lt_card sorry fixed)
- `research/problems/sperner-ndim-mathlib-oq-02/state.md` (updated with n≥3 failure analysis)

### Next Steps

→ Session 9 implemented n=0 and n=1 concrete proofs (see below).


## Session 2026-05-06 (Session 9) — FreudCell annulus failure; n=0,1 proved

**Mode**: REVISIT (continuing axiom elimination work)
**Outcome**: Major structural insight; n=0 and n=1 cases proved (companion file rewritten)

### What I Did

- Proved definitively that FreudCell triangulates an ANNULUS (not Δ²) for n=2, N=2
- Rewrote companion file SpernerFreudenthalSimplex.lean with:
  - `sperner_panchromatic_zero` (n=0): trivial, 0 sorries
  - `sperner_panchromatic_one` (n=1): discrete IVT, 0 sorries
- Removed all broken FreudCell code

### Key Mathematical Findings

**DEFINITIVE FAILURE**: For n=2, N=2, the 6 FreudCell cells triangulate an ANNULUS:
- All 6 cells have pattern {corner, midpoint, midpoint}: ADF, AEF, BDE, BFE, CED, CFD
- Centroid (2/3,2/3,2/3) lies in BOTH triangle ADF AND triangle BDE (overlapping)
- Center triangle DEF = {(1,1,0),(1,0,1),(0,1,1)} is entirely MISSING
- Euler characteristic: V(6)-E(12)+F(6) = 0 = annulus ≠ 1 = disk
- Session 8's "18 cells for n=2, N=3" count was WRONG (overcounting by 2×)

**n=0 proved**: Δ⁰ is a single point; trivial. 0 sorries.

**n=1 proved via discrete IVT**: 
- Grid: g(k) = (k/N, (N-k)/N) for k=0,...,N
- c(0) = 1 (g(0)₀ = 0, spernerColor ≠ 0)
- c(N) = 0 (g(N)₁ = 0, spernerColor ≠ 1)
- K = max{k : c(k)=1} exists, K < N
- c(K) = 1 → f(g(K))₁ ≤ g(K)₁
- c(K+1) = 0 → f(g(K+1))₀ ≤ g(K+1)₀
- Diameter: |g(K+1) l - g(K) l| = 1/N for l=0,1 ✓

### Files Modified

- `proofs/Proofs/SpernerFreudenthalSimplex.lean` (complete rewrite: n=0,1 proved)

### Next Steps

1. **For n≥2**: Use `AbstractSimplicialData` from `SpernerSimplicialInstance.lean` (0 sorries)
   - Define `topSimplices` as the correct standard Sperner triangulation (NOT FreudCell)
   - Prove `pseudomanifold` condition (~100 lines)
   - `toTriangulation` gives full CellComplex automatically
   - Prove `boundary_doors_odd` by induction (boundary = (n-1)-dim case)
2. **Gallery status**: main file stays at 1 axiom (correct); n=0,1 proved independently
3. **Estimated remaining**: 300-400 lines for n≥2 general case

