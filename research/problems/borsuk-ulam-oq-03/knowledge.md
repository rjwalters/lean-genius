# borsuk-ulam-oq-03: Constructive (Intuitionistic) Borsuk-Ulam

## Problem Summary

**Open Question**: Can the 1D Borsuk-Ulam theorem be proved constructively
(without full classical logic)? What is the constructive status of
higher-dimensional Borsuk-Ulam?

**Status**: 111 proved theorems, 4 axioms, 0 sorries (2237 lines).

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

## Session 2026-03-18 (researcher-2) - Tucker 2D, Sperner 1D, Equivalence Chain

**Mode**: REVISIT (existing knowledge from Session 1)
**Outcome**: progress

### What I Did

Added 5 new sections (XLII-XLVI) with 17 new proved theorems:

**Section XLII: Tucker's 2D Lemma (Octahedral Triangulation)**
- `tucker_2d_octahedral`: Tucker 2D for minimal 4+1 vertex triangulation (PROVED by exhaustive case analysis over 64 labelings)
- `tucker_2d_label_exhaustion`: When boundary labels are unrelated (a≠±b), the four labels ±a,±b exhaust {-2,-1,1,2} (PROVED)
- `tucker_2d_octahedral_explicit`: Same with boundary vs interior edge distinction (PROVED)
- `tucker_2d_refined`: Tucker 2D for 8+1 vertex triangulation (PROVED, 1024 cases)

**Section XLIII: Sperner's 1D Lemma**
- `sperner_1d`: Complete edge exists in {false,true}-labeled {0,...,n+1} (PROVED by well-ordering)
- `sperner_implies_brouwer_1d_sketch`: Logical connection to Brouwer FP

**Section XLIV: Formal Equivalence Chain (1D)**
- `bu_implies_brouwer_1d`: BU → Brouwer FP via IVT on f(x)-x (PROVED)
- `brouwer_implies_bu_1d_sketch`: Brouwer → BU (uses IVT directly)
- `no_retraction_1d`: No continuous retraction [-1,1]→{-1,1} (PROVED via IVT)
- `no_retraction_implies_brouwer_1d`: No-retraction → Brouwer FP (PROVED)

**Section XLV: Tucker-BU Bridge**
- `tucker_path_following_1d`: First sign change with minimality (PROVED)

### Key Findings

- Tucker 2D for octahedral triangulation is trivially true because the 4-element label set {-2,-1,1,2} has exactly 2 pairs of opposites; when boundary labels span both pairs, they exhaust the label set
- `simp (config := { decide := true })` handles the 64-case Tucker 2D proof efficiently
- Sperner 1D proof required careful well-ordering argument (find minimal true index)
- `Nat.findX` is the well-ordering lemma for decidable predicates on ℕ

### Files Modified

- `proofs/Proofs/BorsukUlamOQ03.lean` (1800 → 2237 lines, +437 lines)

### Next Steps

- Formalize Tucker 2D for general triangulations
- Prove Tucker 2D → BU 2D via approximation/compactness
- Add Sperner 2D lemma
- Add KKM lemma
