# Problem: Complete Erdős #79 — K₄ is minimally non-linear

**Slug**: erdos-79-incomplete-01
**Status**: Active
**Source**: gallery-gap (completion of `proofs/Proofs/Erdos79Problem.lean`)
**Parent proof**: erdos-79

## Problem Statement

### Formal Statement

Discharge the single `sorry` in `proofs/Proofs/Erdos79Problem.lean` (line ~216),
the lemma

```lean
theorem K4_unique_known :
    ∀ G ∈ knownExamples, isMinimallyNonLinear G
```

where `knownExamples = {completeGraph 4}`. Concretely, prove that the complete
graph K₄ (as `SimpleGraph (Fin 4)`) satisfies the `isMinimallyNonLinear`
predicate defined in the file.

### Plain Language

Erdős Problem #79 concerns *minimally non-linear* graphs — graphs that are not
"linear" in the relevant extremal sense but every proper subgraph is. K₄ is the
only explicitly known example. The gallery file already states the problem and
Wigderson's existence theorem; the remaining gap is the concrete verification
that K₄ itself has the property.

### Why This Matters

Closing this `sorry` turns a scaffolded gallery entry into a genuinely verified
statement about the one explicit example, and exercises the definitions in the
file (`isMinimallyNonLinear`) against a concrete finite graph.

## Known Results

### What's Already Proven

- `erdos_79_solved := wigderson_theorem` — existence of infinitely many such graphs (in file).
- The definition `knownExamples := {completeGraph 4}` (in file).

### What's Still Open (this task)

- `K4_unique_known`: verify `isMinimallyNonLinear (completeGraph 4)`.

### Our Goal

Fill the one theorem `sorry`. This is a concrete finite check over `Fin 4`;
`decide`/`Finset` enumeration or an explicit case argument should apply once the
`simp [knownExamples]` reduction fixing `G = completeGraph 4` is handled (the
existing comment notes a "type mismatch" to resolve).

## Suggested First Steps (OODA)

1. **OBSERVE**: Read `isMinimallyNonLinear` and surrounding definitions in
   `proofs/Proofs/Erdos79Problem.lean`. Determine what must be verified for K₄.
2. **ORIENT**: Decide whether the predicate is `Decidable` (enabling `decide`)
   or needs a manual argument; check Mathlib graph API for `completeGraph`.
3. **DECIDE**: Pick `decide`/`Fintype`-enumeration vs explicit proof.
4. **ACT**: Fill the sorry; build with
   `./proofs/scripts/docker-build.sh Proofs.Erdos79Problem`.

## Honesty Standard

Do not introduce new `axiom` declarations. The file already carries scaffolding
axioms; this task only discharges the `K4_unique_known` theorem `sorry` and must
not add assumptions.
