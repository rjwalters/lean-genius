# Problem: What is the complexity of finding the actual monotonic subsequence

**Slug**: erdos-szekeres-oq-02
**Created**: 2026-06-10
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
What is the complexity of finding the actual monotonic subsequence?
$$

### Plain Language

This open question arises from the gallery proof `erdos-szekeres` (Erdős–Szekeres Theorem). The Seeker selected it as a extension suitable for the autonomous research pipeline.

The specific question: What is the complexity of finding the actual monotonic subsequence?

### Why This Matters

Significance score 5/10 — the problem extends a verified gallery proof in a concrete direction. Closing it would add a extension-style follow-up to the gallery corpus and exercise machinery from the parent entry.

## Known Results

### What's Already Proven

- Parent proof `erdos-szekeres` — provides the base theorem and its Mathlib infrastructure
- Sibling open questions on the same gallery entry — see `src/data/proofs/erdos-szekeres/meta.json` `conclusion.openQuestions`

### What's Still Open

- The question stated above, as a extension of the parent result
- Quantitative / constructive refinements that the Researcher may identify during OBSERVE

### Our Goal

Formulate the question as a Lean 4 theorem aligned with the parent entry's namespace, identify the Mathlib lemmas that close the gap, and either prove it or carve out a precise sub-claim that is tractable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-szekeres | Gallery root containing the open question | Parent definitions, Mathlib infrastructure used by the proof |
| erdos-szekeres | Immediate source of this open question | Source proof techniques carried over |

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
- Seeker-assigned tractability score 5/10 reflects a likely-tractable direct extension
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
  - erdos
  - combinatorics
  - ramsey-theory
  - sequences
  - pigeonhole
  - wiedijk-100
  - seeker-selected
related_proofs:
  - erdos-szekeres
  - erdos-szekeres
difficulty: medium
source: gallery-gap
created: 2026-06-10
significance: 5
tractability: 5
tier: B
category: extension
```

## Must prove exactly / does not count

Added 2026-07-24 (researcher-1) per the statement-pinning rule. The OQ "what is
the complexity of finding the actual monotonic subsequence?" resolves into a
formalizable core (see knowledge.md). The pinned Lean targets:

### Must prove exactly

1. **Computable algorithm.** A `def incDP : Sequence α n → Fin n → ℕ` that is
   NOT marked `noncomputable`, computing the longest-increasing-subsequence
   length ending at each position, with a proved recurrence equation
   (`incDP f i = 1 + sup over {j < i, f j < f i} of incDP f j`).
2. **The witness is realizable.** `HasIncreasingEndingAt f i (incDP f i)` —
   the DP value is achieved by an actual increasing subsequence ending at `i`
   (the parent's own ending-at predicate, not a restatement), and consequently
   `incDP f i ≤ maxIncLen f i` against the parent's noncomputable spec.
3. **Exact comparison count.** A cost function counting exactly the scanned
   candidate pairs `(j, i), j < i` of the DP, with the proved closed form
   `n * (n - 1) / 2` (and a division-free form `* 2 = n * (n - 1)`).
4. **Full correctness (milestone 2, later session).**
   `incDP f i = maxIncLen f i` — the `≥` half (optimal substructure /
   stripping) is the remaining open piece; the `≤` half is item 2.
5. **Actual data (milestone 3, later session).** An executable
   `incWitness f i : IncreasingSubseq f (incDP f i)` (computable, i.e. via
   `List.argmax`-style selection, not `Classical.choice`).

### Does not count

- **Θ(n log n) patience sorting or Fredman's Ω(n log n) lower bound** — no
  comparison-cost model exists in Mathlib; these remain the literature answer
  and are out of Lean scope (documented, not attempted).
- **Big-O statements** — no cost monad; only exact operation counts count.
- **A noncomputable witness function** (Classical choice wrapped in a `def`)
  presented as "finding" the subsequence — the point of the OQ is executable
  data; `noncomputable` extraction is a near-miss for milestone 3.
- **Re-proving existence** (`HasIncreasingEndingAt f i 1` etc. or the parent
  pigeonhole) without the DP — that is sibling oq-01's territory.
- **`incDP ≤ maxIncLen` alone** presented as full correctness (item 4 needs
  both directions).
