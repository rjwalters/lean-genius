# Problem: Verify the standard 2-simplex triangulation (triangulated triangle) as a conc...

**Slug**: `sperner-simplicial-instance-oq-01`
**Created**: 2026-05-12
**Status**: Available
**Source**: gallery-gap (parent: `sperner-simplicial-instance`)
**Category**: extension
**Tractability**: challenging
**Tags**: combinatorics, sperner-lemma, simplicial-complex, triangulation, pseudomanifold, cell-complex, bridge-construction, topology

## Problem Statement

Verify the standard 2-simplex triangulation (triangulated triangle) as a concrete Triangulation instance

## Source Gallery Proof

- Parent: `sperner-simplicial-instance` — Sperner's Lemma: SimplicialComplex to CellComplex Bridge
- Related: sperner-simplicial-instance

## Goal for This Workspace

This is a research workspace for a single open question extracted from the gallery. The researcher should:

1. **OBSERVE**: Read the parent proof's `meta.json` and source files to understand the existing context (what is already proven, the conventions used, the API surface).
2. **ORIENT**: Survey Mathlib and the literature for relevant results. Look for adjacent formalizations, near-misses, and the standard proof techniques that apply.
3. **DECIDE**: Pick a concrete sub-question or first-step lemma that is plausibly within reach. Prefer a small, build-verifiable statement over an ambitious one.
4. **ACT**: Either ship a Lean scaffold (with stated targets and `sorry` placeholders for the remaining gaps) or, for moonshot-flavored questions, an S1 OBSERVE doc-only PR mapping the landscape and pointing to viable S2 follow-ups.

The Seeker has done the candidate-pool plumbing; the Researcher owns the OODA loop from here. See the role spec at `.lean/roles/researcher.md` for the standard cadence.

## Suggested First Steps

1. `gh pr list --search "sperner-simplicial-instance-oq-01"` — confirm no parallel session is already in flight (race-safety re-check at session start).
2. Inspect `src/data/proofs/sperner-simplicial-instance/meta.json` — `openQuestions` array — for adjacent OQs that may share infrastructure.
3. Search Mathlib for the central object referenced in the problem statement; the API surface usually dictates the cleanest decomposition.

## Must prove exactly / does not count

**Target**: a concrete instance of the parent's `Triangulation V 2` structure
(`proofs/Proofs/SpernerSimplicialInstance.lean:81`) for the standard
triangulated 2-simplex, with all four obligations (`vertex_injective`,
`adj_symm`, `adj_vertex`, `adj_ne`) machine-checked, 0 sorries, 0 axioms.

- **Counts**: the resolution-2 concrete instance (`standardTriangle2 :
  Triangulation (Fin 6) 2`) and/or the general-resolution family
  (`standardTriangleTriangulation m : Triangulation (LatticePoint m) 2`).
- **Does not count**: the single-cell `trivialTriangle` smoke test (no real
  subdivision — no interior edge); an instance with `adj ≡ none` everywhere
  (pseudomanifold fields vacuous); a claim of *geometric* triangulation of
  |Δ²| ⊂ ℝ² (the structure is combinatorial; no embedding is stated).

## Adversarial checklist (SOLVED claim, 2026-07-24)

1. **Trivial-instance trap** — `Triangulation V 2` is inhabited by the
   single-cell `trivialTriangle`; confirm the claim rests on
   `standardTriangleTriangulation m` (`m²` cells via `TriCell m`) and
   `standardTriangle2` (4 cells), each with genuine interior adjacency.
2. **All-boundary adjacency cheat** — `adj_symm`/`adj_vertex`/`adj_ne` are
   vacuous under `adj ≡ none`. Confirm `triAdj` has `some` rows: all three
   edges of every `down`-cell, and every `up`-cell edge not on the geometric
   boundary. Cross-check: the m=2 specialization reproduces the
   independently `decide`-verified `tadj` table (3 interior edges).
3. **Adjacency-completeness gap (disclosed, structural)** — the structure
   never requires that geometrically shared faces be recorded as `some`;
   no theorem here certifies "`triAdj = none` ⟹ geometric boundary". Our
   table marks all interior edges by construction, but the completeness
   statement is oq-03 territory (boundary-door parity), not part of this
   instance claim.
4. **Vertex-map faithfulness** — a wrong `triVtx` could still satisfy the
   four obligations. Mitigations actually proved: `vertex_injective_triVtx`
   (distinct corners) and `triAdj_vertex` (adjacent cells share exactly the
   2-element edge set in identical lattice coordinates).
5. **Carrier near-miss** — the claim is the combinatorial instance over
   `LatticePoint m` (subtype of `Fin (m+1) × Fin (m+1)`), matching the
   parent's combinatorial structure; it is NOT a geometric realization.
6. **`decide` scope** — kernel `decide` only on closed `Fin`-indexed goals
   (m=2 instance; `Finset (Fin 3)` erase equations in `triAdj_vertex`).
   All general-`m` obligations are parametric proofs. No `native_decide`.
7. **m = 0 degeneracy** — `TriCell 0` is empty, so the m=0 member of the
   family is the empty triangulation (structurally legal, not part of the
   subdivision claim; m ≥ 1 gives real subdivisions, m ≥ 2 interior edges).
