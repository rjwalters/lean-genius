# borsuk-ulam-oq-03: Constructive (Intuitionistic) Borsuk-Ulam

## Problem Summary

**Open Question**: Can the 1D Borsuk-Ulam theorem be proved constructively
(without full classical logic)? What is the constructive status of
higher-dimensional Borsuk-Ulam?

**Status**: SURVEYED - 13 proved theorems, 1 axiom (general BU for n≥2), 0 sorries.

**Answer**:
- 1D: YES, proved via IVT on antisymmetric difference
- n≥2: Requires algebraic topology (axiomized); no known constructive proof

## Session 2026-02-25 (Session 1) - Initial Formalization

**Mode**: FRESH (problem had EMPTY knowledge)
**Outcome**: surveyed/progress

### What I Did

- Created `proofs/Proofs/BorsukUlamOQ03.lean` with full 1D formalization
- Proved 13 theorems covering:
  - 1D interval BU via IVT
  - Odd function zero lemma
  - BU ↔ odd-zero equivalence
  - S¹ parametric version via IVT on [0,π]
  - Circle point on unit circle
  - No odd map to {±1}
  - 5 structural lemmas
  - NSphere def + antipodal def
  - Consequence of general BU axiom
- Fixed key Lean 4 issue: `f (--x)` is INVALID because `--` starts a line comment;
  must write `f (-(-x))` or restructure to avoid double negative
- Fixed `ring` issue: after `simp only [hg_def]`, `ring` fails on `f (-(-x))` atoms;
  add `neg_neg` to simp first
- `Continuous.prod_mk` may not be directly accessible as a field; use `fun_prop` instead
- Created PR #3246

### Key Findings

- `f (--x)` is a SYNTAX BUG: `--` starts a line comment in Lean 4!
  Workaround: Write `f (-(-x))` or avoid double-negated function args
- `fun_prop` tactic handles complex continuity goals automatically with `hf : Continuous f`
- IVT API: `intermediate_value_Icc hab hg_cont ⟨ha, hb⟩` where `ha : f a ≤ 0` and `hb : 0 ≤ f b`
- `le_or_gt` is the non-deprecated name for case split (not `le_or_lt`)
- Constructive content: IVT uses Classical.em internally, but Bishop-style IVT holds

### Files Created

- `proofs/Proofs/BorsukUlamOQ03.lean` (324 lines, 13 theorems, 1 axiom, 0 sorries)

### Next Steps

- The higher-dimensional BU (n≥2) could potentially be proved using Tucker's lemma (combinatorial BU)
- Tucker's lemma is more constructive than degree-theoretic approaches
- Would require: triangulation, labeling, Tucker path → antipodal pair
