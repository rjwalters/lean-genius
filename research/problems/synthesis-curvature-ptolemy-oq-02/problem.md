# Formalize the hyperbolic Ptolemy theorem (K = −1)

**Slug**: `synthesis-curvature-ptolemy-oq-02`
**Created**: 2026-07-02T00:00:00Z
**Source**: gallery openQuestion (seeker batch)

## Problem Statement

Formalize the hyperbolic (constant curvature K = −1) analogue of Ptolemy's
theorem. For a cyclic quadrilateral in the hyperbolic plane, the sides and
diagonals satisfy a relation obtained from the Euclidean identity by replacing
each length ℓ with `sinh(ℓ/2)` (the K = −1 specialization of the parent proof's
`curvatureSin` parametrization). The goal is to prove this hyperbolic Ptolemy
relation in the Poincaré disk model, unifying it with the Euclidean and
spherical cases already treated in the parent `synthesis-curvature-ptolemy`.

## Parent Proof

- **ID**: `synthesis-curvature-ptolemy`
- **Title**: Synthesis: Curvature-Parametrized Ptolemy via curvatureSin
- **Gallery page**: `src/data/proofs/synthesis-curvature-ptolemy/`

## Classification

- **Category**: extension
- **Tractability**: challenging
- **Tier**: B (research-track, seeker-selected)
- **Tags**: geometry, hyperbolic-geometry, ptolemy, curvature, poincare-disk, trigonometry

## Suggested First Steps (OODA)

1. **OBSERVE**: Read the parent proof at `src/data/proofs/synthesis-curvature-ptolemy/meta.json` and its Lean file. Understand how `curvatureSin` unifies the Euclidean (K = 0) and spherical (K > 0) cases, and where the K < 0 branch is currently left open. Survey Mathlib for hyperbolic-distance / Poincaré-disk / `Real.sinh` infrastructure.

2. **ORIENT**: Identify 2-3 concrete S2 target lemmas. Likely decomposition: (a) a hyperbolic law-of-cosines or distance formula in the chosen model, (b) the `sinh(ℓ/2)` substitution making the curvature-parametrized identity specialize correctly at K = −1, (c) assembling these into the hyperbolic Ptolemy relation. Record any Mathlib-coverage gaps (the Poincaré-disk metric may be the binding constraint) before Lean edits.

3. **DECIDE**: Choose one S2 target as the first ACT goal. Sketch the outline (no Lean yet). Decide between (a) a doc-only OBSERVE note, (b) a Lean stub `theorem … := sorry` fixing the target's signature, or (c) a full ACT attempt with `./proofs/scripts/docker-build.sh Proofs.YourFile`.

4. **ACT**: Execute the chosen step. If a build fails or Mathlib lacks the hyperbolic-metric API, capture the failure in `knowledge.md` and pivot back to ORIENT. Never run `lake build` directly — always use the Docker wrapper.

## Anti-targets

- Do **not** attempt the full theorem in a single PR — decompose first.
- Do **not** re-derive machinery the parent `curvatureSin` proof already provides; specialize it.
- Do **not** introduce `axiom` declarations to paper over missing Poincaré-disk infrastructure — use `theorem … := sorry` and discharge them, or record the gap honestly.
- Do **not** duplicate sibling coverage (check `synthesis-curvature-ptolemy-oq-01` first).

## Honesty Standard

State explicitly whether the eventual proof will be `verified` (all sorries
discharged, no axioms, no structure-encoded assumptions) or `axiomatized` (some
assumptions remain, e.g. an unformalized Poincaré-disk metric fact). Default to
`axiomatized` when in doubt.
