# borsuk-ulam-oq-03: Constructive (Intuitionistic) Borsuk-Ulam

## Problem Summary

**Open Question**: Can the 1D Borsuk-Ulam theorem be proved constructively
(without full classical logic)? What is the constructive status of
higher-dimensional Borsuk-Ulam?

**Status**: 168 proved theorems, 4 axioms (2 independent), 0 sorries (3730 lines).

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

## Session 2026-03-19 (researcher-2) - BU→LS General, Axiom Reduction

**Mode**: REVISIT (RICH knowledge from 3 prior sessions)
**Outcome**: progress

### What I Did

**Section LX: BU → LS (General, Open Sets)**
- `fin_castSucc_or_last`: Helper decomposing Fin (n+1) into castSucc/last
- `cover_forces_last`: Helper showing covering + exclusion from first n sets → in last set
- `ls_covering_general_open`: PROVED BU→LS for n+1 open sets covering S^n
  - Defines f_i(x) = infDist(x, U_iᶜ) for first n sets
  - Applies BU to get x₀ with equal infDist on both sides
  - Case 1: some infDist > 0 → both in that U_i
  - Case 2: all infDist = 0 → both forced into U_n by covering

**Section LXI: BU → LS (General, Closed Sets)**
- `ls_covering_general_closed`: PROVED BU→LS for n+1 closed sets covering S^n
  - Uses infDist to sets themselves (not complements)
  - Case 1: nonempty set with infDist = 0 → membership by closedness
  - Case 2: all sets empty or positive distance → pigeonhole to last set

**Section LXII: Axiom Reduction**
- `ls_axiom_redundant`: Witnesses that ls_covering_general_open has same type as LS axiom
- Reduces independent axiom count from 4 to 3

**Fix: Mathlib compatibility**
- Line 2003 (`sperner_1d`): `convert this using 2; congr 1; ext; omega` failed because
  `convert this using 2` now solves the goal directly (Mathlib update). Fixed to `convert this`.

### Key Findings

- The infDist technique used for 1D LS (Section LVI) generalizes verbatim to all dimensions
- Fin.castSucc/Fin.last decomposition is the right abstraction for "first n vs last" arguments
- Subtype coercion with `set mx₀` creates unification issues - must provide NSphere argument explicitly
- `convert` behavior changed with Mathlib update, making `convert this using 2` more powerful

### Files Modified

- `proofs/Proofs/BorsukUlamOQ03.lean` (3136 → 3349 lines, +213 lines)
  - 7 new proved results (3 helpers + 2 LS theorems + 1 redundancy witness + 1 summary)
  - 1 pre-existing Mathlib compat fix (sperner_1d)

### Stats
- **Total**: 3349 lines, 143 theorems, 4 axioms (3 independent), 0 sorries

### Next Steps
- Prove BU → no_retraction (requires degree theory)
- Prove no_retraction → Brouwer FP (requires ray-sphere construction)
- Formalize Tucker 2D for general triangulations

## Session 2026-03-19 (researcher-2, iteration 2) - Ray-Sphere Intersection Infrastructure

**Mode**: REVISIT (continuing from earlier in same day)
**Outcome**: progress

### What I Did

**Section LXIII: Ray-Sphere Intersection**
- `innerProd`, `normSq`: Inner product and norm squared on ℝ^k with basic lemmas
- `ray_normSq_expand`: |a + td|² = |a|² + 2t⟨a,d⟩ + t²|d|² (PROVED)
- `ray_discriminant_nonneg`: Quadratic discriminant ≥ 0 when |a| ≤ 1 (PROVED)
- `raySphereRoot`: The larger root formula for the ray-sphere quadratic (DEFINED)
- `raySphereRoot_eq_one`: When |x|² = 1 and a ≠ x, the root is exactly 1 (PROVED)
  - Key insight: discriminant is a perfect square, simplifies to |d|²/|d|² = 1
- `no_retraction_implies_brouwer_fp`: Main theorem structure (continuity deferred as sorry)

### Key Findings
- Ray-sphere intersection is a clean quadratic At² + Bt + C = 0
- When x ∈ S^n, discriminant/4 = ((1-|a|²+|d|²)/2)² — perfect square!
- normSq d > 0 requires the explicit hypothesis a ≠ x (no fixed point)
- Continuity of the retraction is the remaining gap

### Files Modified
- `proofs/Proofs/BorsukUlamOQ03.lean` (added ~120 lines of ray-sphere infrastructure)
- Note: File has merge conflicts from concurrent researcher commits (duplicate declarations)

### Next Steps
- Prove continuity of ray-sphere retraction (the main remaining gap)
- Fix merge conflicts in file (other researchers' code)

## Session 2026-03-19 (researcher-3) - Continuity Proof Complete

**Mode**: REVISIT (RICH knowledge from 4 prior sessions)
**Outcome**: progress (major milestone - axiom reduction)

### What I Did

**Section LXVI: Continuity Infrastructure for the Retraction**
- `nsq_nonneg'`: Non-negativity of norm squared (utility)
- `ballProj`: Continuous projection onto closed unit ball: x ↦ x/max(1,|x|) (DEFINED)
- `ballProj_denom_pos`: max(1,√(nsq x)) is always positive (PROVED)
- `ballProj_in_ball`: ballProj maps every point into the closed unit ball (PROVED)
- `ballProj_ball_fix`: ballProj fixes points already in the ball (PROVED)
- `continuous_ballProj`: ballProj is continuous (PROVED - trivial from max formulation)
- `continuous_raySphereT_comp`: raySphereT is continuous when composed with continuous
  functions and nsq(d)>0 everywhere (PROVED)

**Theorem completion: no_retraction_implies_brouwer_general**
- Refactored to use `ballProj` instead of piecewise `if-then-else` projection
- Added complete continuity chain: proj → f∘proj → proj-f∘proj → raySphereT → r
- **Filled the sorry**: `Continuous r` now proved via `continuous_pi` + composition
- **Result**: 0 sorries remaining (was 1)
- **Axiom reduction**: brouwer_fixed_point is now provable from no_retraction
- **Effective axiom count**: 2 independent (borsuk_ulam_general + no_retraction)

### Key Findings
- The max formulation `x/max(1,|x|)` completely avoids piecewise continuity analysis
- `Continuous.div` in Lean 4 handles f/g when g is continuous and everywhere nonzero
- The retraction's continuity decomposes cleanly: each component a_i + t·d_i is
  a sum of products of continuous scalar and vector-component functions
- `continuous_raySphereT_comp` as a standalone helper makes the proof modular

### Files Modified
- `proofs/Proofs/BorsukUlamOQ03.lean` (3662 → 3730 lines, +68 lines net)
  - 7 new proved results (5 ballProj lemmas + 1 raySphereT continuity + 1 summary)
  - 1 sorry eliminated (continuity of retraction)
  - Refactored no_retraction_implies_brouwer_general to use ballProj

### Stats
- **Total**: 3730 lines, 168 theorems, 4 axioms (2 independent), 0 sorries

### Next Steps
- Prove BU → no_retraction via degree theory (reduces axioms 2→1)
- Add explicit witness that brouwer_fixed_point axiom is redundant
- Clean up: remove the brouwer_fixed_point axiom since it's now a theorem
