# Current State

**Phase**: OBSERVE (S1 complete)
**Since**: 2026-05-12T17:55:00Z
**Iteration**: 1

## Current Focus

S1 OBSERVE delivered: weakening the parent file's pure pseudomanifold
hypothesis to a stratified ("mixed") pseudomanifold version of
Sperner's lemma. The S1 survey reveals the OQ-01 reduces to a clean
"apply parent on each dimension-stratum" pattern, with all
non-trivial work happening at the *predicate* level (`topCellsOfDim`,
`MixedPseudomanifold`) rather than at the proof level.

## What S1 Delivers

This iteration is **doc-only** (no Lean changes, no build needed).

Four files produced:
- `research/problems/sperner-simplicial-bridge-oq-01/problem.md`
- `research/problems/sperner-simplicial-bridge-oq-01/state.md` (this file)
- `research/problems/sperner-simplicial-bridge-oq-01/knowledge.md`
- `src/data/research/problems/sperner-simplicial-bridge-oq-01.json`

Counts:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

## S1 Survey Highlights

1. **Door dimensions are pure even in mixed complexes.** A codim-1
   face of a $d$-simplex has cardinality $d$; a codim-1 face of a
   $(d-1)$-simplex has cardinality $d-1$. So even in a mixed-dim
   complex, doors are *graded by dimension*, and the door-counting
   argument runs independently per stratum.

2. **`MixedPseudomanifold` is stratum-wise.** The predicate
   `∀ d, ∀ f, f.card = d → ((topCellsOfDim K d).filter (· ⊆ ·)).card ≤ 2`
   captures the pseudomanifold property on each stratum independently.

3. **`exists_panchromatic` applies stratum-by-stratum.** No new proof
   is required for the *theorem itself*; the work is in setting up
   the right framework predicates and showing the door-count carries
   through.

4. **The parent's `verified` status is preserved.** Adding the
   `MixedPseudomanifold` predicate and the OQ-01 theorem does *not*
   touch the parent file's existing definitions or theorems; it adds
   a strict generalization that subsumes (not replaces) the parent's
   `exists_panchromatic`.

5. **Mathlib `Finset.filter` is the only API exercised.** No new
   imports needed; the whole development sits on top of
   `Proofs.SpernerSimplicialBridge`.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Problem statement + stratification analysis + Mathlib API map | 0 Lean | **this session** |
| S2 | SCAFFOLD | `topCellsOfDim` + `MixedPseudomanifold` + `exists_panchromatic_of_pure` | ~80 | pending |
| S3 | ACT | `sperner_mixed_panchromatic` + boundary-door translation | ~50-80 | pending |
| S4 | GALLERY | `sperner-simplicial-bridge-oq-01` gallery entry | ~30 + meta.json | pending |

## Next Action

**S2 (any researcher)**: SCAFFOLD. Create new companion file
`proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (~80 LOC) with:

1. Import the parent: `import Proofs.SpernerSimplicialBridge`.

2. Define:
   ```lean
   namespace Sperner.SimplicialComplex

   /-- The dimension-d stratum of a mixed simplicial complex. -/
   noncomputable def topCellsOfDim {E : Type} [DecidableEq E]
       (K : Finset (Finset E)) (d : Nat) : Finset (Finset E) :=
     K.filter (fun s => s.card = d + 1)

   /-- Mixed pseudomanifold: each dimension's stratum is a
       pseudomanifold (no codim-1 face is in > 2 cells of that
       dimension). -/
   def MixedPseudomanifold {E : Type} [DecidableEq E]
       (K : Finset (Finset E)) : Prop :=
     ∀ d : Nat, ∀ f : Finset E, f.card = d →
       ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2
   ```

3. Prove the sanity-check (pure → mixed pseudomanifold):
   ```lean
   /-- Pure pseudomanifold data lifts to MixedPseudomanifold. -/
   theorem MixedPseudomanifold.of_pure
       {E : Type} [DecidableEq E] {d : Nat}
       (topCells : Finset (Finset E))
       (hcard : ∀ s ∈ topCells, s.card = d + 1)
       (hpseudo : ∀ f : Finset E, f.card = d →
         (topCells.filter (fun s => f ⊆ s)).card ≤ 2) :
       MixedPseudomanifold topCells := by
     intro d' f hf
     -- For d' = d: topCellsOfDim topCells d = topCells (by hcard); use hpseudo.
     -- For d' ≠ d: topCellsOfDim topCells d' = ∅ (no cells of that
     --             dimension); filter empty = empty; card ≤ 2 trivially.
     ...
   ```

4. Smoke-test build via `./proofs/scripts/docker-build.sh
   Proofs.SpernerSimplicialBridgeOQ01`. Expected ~10 min (parent file
   already cached).

Register in `proofs/Proofs.lean` (add `import Proofs.
SpernerSimplicialBridgeOQ01`).

## Open Files

- `problem.md` — Formal + plain statement, 5-step approach, Mathlib
  API map.
- `knowledge.md` — Mathematical derivation, stratification analysis,
  edge cases, S2 risk register.

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE)
- Current approach attempts: 1
- Approaches considered:
  - **A (stratification, primary)**: define `topCellsOfDim` and
    `MixedPseudomanifold`, apply parent stratum-by-stratum. ~150-200
    total LOC. Pursued.
  - **B (CW-pair / simplicial-set lifting)**: would adapt the
    Sperner-via-simplicial-set route; depends on Mathlib's
    `AlgebraicTopology.SimplicialSet` infrastructure (cf. parent
    OQ-04). Not pursued for OQ-01; defer to OQ-04.
  - **C (rebuild adjFn for mixed dims)**: would adapt the parent's
    `adjFn` definition to handle adjacency between cells of different
    sizes. Mathematically more general but architecturally invasive.
    Rejected.
