# Problem: Undecidability of the Totality Problem (Rice's Theorem Instance)

**Slug**: halting-problem-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: halting-problem

## Problem Statement

### Formal Statement

$$
\neg\,\mathrm{ComputablePred}\big(\lambda c.\ c\in\mathrm{TotalCodes}\big),\qquad \mathrm{TotalCodes}=\{c:\forall n,\ (\mathrm{eval}\ c\ n).\mathrm{Dom}\}
$$

### Plain Language

The parent flags Rice's theorem as the universal generalization of halting undecidability. Instantiate it on a fresh, non-halting-set property: is the totality set — codes whose partial function is defined on every input — decidable? Prove it is not, by showing this class is extensional but neither empty nor everything.

### Why This Matters

A named classic — 'does a program halt on all inputs' — genuinely distinct from the parent's fixed-input halting question, sibling oq-01 (sound computable approximators + arithmetical hierarchy), and sibling oq-03 (relativized/oracle halting). Direct application of Mathlib's ComputablePred.rice₂ to a concrete extensional code-class.

## Known Results

### What's Already Proven

- Parent entry `halting-problem` is verified (0-axiom) in the gallery and supplies the base result this question extends.
- All Mathlib lemmas listed under References below were grep-confirmed to exist in the pinned Mathlib.

### What's Still Open

- The specific target theorems sketched below (currently `sorry`).

### Our Goal

Prove the target sketch below as a self-contained, verified (0-axiom) child of `halting-problem`. Category: **extension**.

## Target Lean Sketch

```lean
open Nat.Partrec Nat.Partrec.Code ComputablePred

def TotalCodes : Set Code := {c | ∀ n, (eval c n).Dom}

theorem totalCodes_extensional (cf cg : Code) (h : eval cf = eval cg) :
    cf ∈ TotalCodes ↔ cg ∈ TotalCodes := by
  simp only [TotalCodes, Set.mem_setOf_eq, h]

theorem totalCodes_ne_empty : TotalCodes ≠ ∅ := by sorry   -- witness: Code.const 0
theorem totalCodes_ne_univ  : TotalCodes ≠ Set.univ := by sorry -- witness: exists_code of Nat.Partrec.none

theorem totality_undecidable : ¬ ComputablePred (fun c : Code => c ∈ TotalCodes) := by
  intro h
  rcases (rice₂ TotalCodes totalCodes_extensional).1 h with he | hu
  · exact totalCodes_ne_empty he
  · exact totalCodes_ne_univ hu
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `halting-problem` | Parent: undecidability of the halting problem via diagonalization | diagonalization, ComputablePred |
| `halting-problem-oq-01` | Sibling: sound computable approximators + arithmetical hierarchy | Nat.Partrec |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 7/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The required Mathlib primitives exist and the proof mirrors the parent's style; the sketch reduces to assembling named lemmas.

### Suggested First Steps

1. totalCodes_ne_empty: Code.const 0 ∈ TotalCodes since eval_const makes every (eval (const 0) n).Dom hold → Set.nonempty_iff_ne_empty.
2. totalCodes_ne_univ: get c from exists_code.mp Nat.Partrec.none; eval c 0 = Part.none is not Dom, so c ∉ TotalCodes, contradicting Set.univ.
3. Assemble totality_undecidable via rice₂ + rcases; run #print axioms totality_undecidable to confirm 0-axiom.

## References

### Mathlib

- `ComputablePred.rice₂` — Computability/Halting.lean (ComputablePred (·∈C) ↔ C = ∅ ∨ C = Set.univ for extensional C)
- `Nat.Partrec.Code.eval_const` — PartrecCode.lean (total witness: eval (Code.const n) m = Part.some n)
- `Nat.Partrec.Code.exists_code` + `Nat.Partrec.none` — PartrecCode.lean / Partrec.lean (nowhere-defined witness)
- `Nat.Partrec.Code.instDenumerable` — PartrecCode.lean (Primcodable Code, so ComputablePred over Code typechecks)

## Metadata

```yaml
tags:
  - computability
  - undecidability
  - rice-theorem
  - partial-recursive
  - diagonalization
related_proofs:
  - halting-problem
  - halting-problem-oq-01
difficulty: low
source: proof-suggestion
created: 2026-06-30
```
