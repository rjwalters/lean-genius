# Problem: Can we formalize the self-duality property of the theorem explicitly

**Slug**: desargues-theorem-oq-02-oq-02
**Created**: 2026-06-10
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
Can we formalize the self-duality property of the theorem explicitly?
$$

### Plain Language

This open question arises from the gallery proof `desargues-theorem-oq-02` (Non-Desarguesian Planes: The Moulton Plane Counterexample). The Seeker selected it as a extension suitable for the autonomous research pipeline.

The specific question: Can we formalize the self-duality property of the theorem explicitly?

### Why This Matters

Significance score 5/10 — the problem extends a verified gallery proof in a concrete direction. Closing it would add a extension-style follow-up to the gallery corpus and exercise machinery from the parent entry.

## Known Results

### What's Already Proven

- Parent proof `desargues-theorem-oq-02` — provides the base theorem and its Mathlib infrastructure
- Sibling open questions on the same gallery entry — see `src/data/proofs/desargues-theorem/meta.json` `conclusion.openQuestions`

### What's Still Open

- The question stated above, as a extension of the parent result
- Quantitative / constructive refinements that the Researcher may identify during OBSERVE

### Our Goal

Formulate the question as a Lean 4 theorem aligned with the parent entry's namespace, identify the Mathlib lemmas that close the gap, and either prove it or carve out a precise sub-claim that is tractable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| desargues-theorem | Gallery root containing the open question | Parent definitions, Mathlib infrastructure used by the proof |
| desargues-theorem-oq-02 | Immediate source of this open question | Source proof techniques carried over |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib search**: Survey Mathlib for definitions and lemmas matching the question's keywords; many gallery open questions reduce to wiring an existing Mathlib API.
   - Why it might work: Mathlib has broad coverage of classical results adjacent to the gallery proofs
   - Risk: The question may require a definition Mathlib lacks (e.g. a specialized object), in which case the work shifts to defining it

2. **Sibling reuse**: Lift the parent proof's strategy and adapt it to the new statement.
   - Why it might work: The original proof author already structured the gallery entry to make this kind of extension feasible
   - Risk: The sibling lemmas may not generalize cleanly; bookkeeping can dominate

### Key Difficulties

- Need to identify the precise Lean 4 statement; the natural-language description leaves room for interpretation
- Mathlib coverage may be partial — the OBSERVE phase must check which pieces exist

### What Would a Proof Need?

- Key lemma 1: a Lean 4 formal statement of the open question above
- Key lemma 2: connecting Mathlib infrastructure to the parent entry's definitions
- Technical requirements: see the parent proof file for relevant `import Mathlib.*` statements

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Seeker-assigned tractability score 6/10 reflects a likely-tractable direct extension
- Parent entry is verified, so the surrounding Lean infrastructure is in place
- Mathlib coverage of adjacent material is non-trivial; survey by the Scout in ORIENT is advisable

**Estimated Effort**:
- Exploration: 4-8 hours during OBSERVE/ORIENT
- If tractable: 1-3 days for a clean theorem statement plus proof
- If hard: weeks; consider carving a narrower sub-question

## References

### Papers
- See the parent gallery entry's `references` array for citations to the originating literature

### Online Resources
- https://github.com/rjwalters/lean-genius — the gallery repository hosting the parent proof
- Mathlib4 docs at https://leanprover-community.github.io/mathlib4_docs/ — for searching Mathlib namespaces relevant to the keywords below

### Mathlib
- Relevant Mathlib modules will surface during ORIENT; start from the parent proof's existing imports

## Metadata

```yaml
tags:
  - projective-geometry
  - non-desarguesian
  - moulton-plane
  - counterexample
  - incidence-geometry
  - affine-plane
  - research
  - seeker-selected
related_proofs:
  - desargues-theorem-oq-02
  - desargues-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-10
significance: 5
tractability: 6
tier: B
category: extension
```

## Adversarial Checklist (added 2026-07-24, researcher-2 — audit guide for the SOLVED claim)

The claim: self-duality of Desargues's theorem is formalized explicitly in
`proofs/Proofs/DesarguesTheoremOQ02OQ02.lean` — finitely (`polarity_reverses`
on the 10₃ configuration) and at class level (`isDesarguesian_dual_iff`).
Ways THIS claim could be wrong, and what to check:

- **Wrong carrier (the parent's affine trap).** The parent Moulton model is
  affine and affine planes are NOT self-dual. Check: nothing in the file
  touches `MPoint`/`MLine`/`onLine`; Layer 2 lives on `[Membership P L]` +
  `Configuration.Dual`, and the `example` pins Mathlib's
  `ProjectivePlane (Dual L) (Dual P)` instance for context.
- **Type-order swap.** The dual plane is `(Dual L, Dual P)` — dual points ARE
  original lines. A silent `(Dual P, Dual L)` would make the statements
  vacuous or ill-typed-but-fixable-by-unification into something else. Check
  every `Dual` occurrence keeps the `(Dual L) (Dual P)` order.
- **"Self-duality" could be smuggled as a tautology.** If
  `IsConverseDesarguesian` were DEFINED as `IsDesarguesian (Dual L) (Dual P)`,
  the headline would be `Iff.rfl` and content-free. Check both predicates are
  defined independently, each by its own 39-hypothesis universal incidence
  form in `P, L`, and that the proof genuinely transposes the hypothesis list
  (the polarity dictionary), not `Iff.rfl`.
- **Degenerate-configuration hypotheses.** The nondegeneracy schema (12
  inequalities) was chosen polarity-CLOSED; dropping any of them silently
  would still let the duality proof go through (fewer hypotheses to
  transpose) but would change which planes count as Desarguesian. The
  specific check: the schema in both definitions is exactly
  {A≠A', B≠B', C≠C', p≠q, p≠r, q≠r, la≠lb, la≠lc, lb≠lc, ab≠ab', bc≠bc',
  ca≠ca'} — the polarity image of itself.
- **The finite layer could fail to be THE Desargues configuration.** A wrong
  incidence table would still be "some" self-dual structure. Check
  `desargues_roles_central/sides/axis` certify all 30 role incidences of a
  labelled Desargues configuration, and `inc_*_card_three` certify 10₃
  regularity (both by kernel `decide`, no `native_decide`).
- **Conflation of duality-transfer with the intra-plane theorem.** The file
  proves "dual plane Desarguesian ⟺ plane converse-Desarguesian". It does
  NOT prove "a projective plane satisfying (D) satisfies (D*)" — that is
  real geometry, explicitly left open in the header. Any prose claiming the
  latter is an overclaim.
- **Circularity.** No axioms, no sorries; Layer 2 uses only hypothesis
  shuffling; Layer 1 only kernel `decide` on `Fin 10`/`Fin 5` data.
