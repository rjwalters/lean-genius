# Could dependent types better capture TLP 2

**Slug**: `tractatus-ontology-oq-01`
**Created**: 2026-05-12T23:37:36Z
**Source**: gallery openQuestion (seeker batch)

## Problem Statement

Could dependent types better capture TLP 2.0141 — that an object's form IS its combinatorial possibility?

## Parent Proof

- **ID**: `tractatus-ontology`
- **Title**: Wittgenstein's Tractarian Ontology
- **Gallery page**: `src/data/proofs/tractatus-ontology/`

## Classification

- **Category**: extension
- **Tractability**: challenging
- **Tier**: B (research-track, seeker-selected)
- **Tags**: philosophy, logic, ontology, model-theory, truth-functions

## Suggested First Steps (OODA)

1. **OBSERVE**: Read the parent proof at `src/data/proofs/tractatus-ontology/meta.json` and the corresponding Lean file in `proofs/Proofs/`. Survey the gallery's existing infrastructure: what definitions, lemmas, and notations already cover adjacent territory? Cross-reference Mathlib for related theorems and APIs.

2. **ORIENT**: Identify 2-3 concrete S2 target lemmas (Σ-type signatures with no `sorry` placeholders yet) that decompose the question into bite-sized provable steps. Prefer angles where Mathlib already has the heavy machinery — searches via `gh api -X GET search/code` are cheap. Document any duplicate-detection findings (sibling slugs, parent coverage, etc.) before any Lean edits.

3. **DECIDE**: Choose one S2 target as the first ACT goal. Sketch the proof outline (no Lean yet). Decide between (a) doc-only S1b OBSERVE / S2 PREP session note, (b) Lean stub `theorem … := sorry` introducing the target's signature, or (c) full ACT attempt with `./proofs/scripts/docker-build.sh Proofs.YourFile`.

4. **ACT**: Execute the chosen step. If a build fails or a Mathlib lemma is missing, capture the failure mode in `knowledge.md` and pivot back to ORIENT. Never run `lake build` directly — always use the Docker wrapper.

## Anti-targets

- Do **not** attempt to discharge the full open question in a single PR — decompose first.
- Do **not** duplicate existing gallery coverage; check the parent proof's annotations + sibling OQ-NN slugs first.
- Do **not** introduce `axiom` declarations to "axiomatize" the question — use `theorem … := sorry` and discharge them.

## Honesty Standard

When reporting progress, state explicitly whether the eventual proof will be `verified` (all sorries discharged, no axioms, no structure-encoded assumptions) or `axiomatized` (some assumptions remain). Default to `axiomatized` when in doubt.
