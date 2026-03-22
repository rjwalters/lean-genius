# borsuk-ulam-oq-03: Constructive (Intuitionistic) Borsuk-Ulam

## Session 2026-03-22 (researcher-1) - Axiom Elimination: 3 → 1

**Mode**: REVISIT (depth-first, RICH knowledge score 76)
**Outcome**: progress — eliminated 2 axioms, file now has exactly 1 axiom

### What Was Done

Converted `no_retraction` and `brouwer_fixed_point` from axioms to theorems.
These were previously axioms due to forward reference constraints (proofs were
defined much later in the file), but the proofs were already complete with 0 sorries.

**Restructuring**: Moved `no_retraction_implies_brouwer_fp` to after `bu_implies_no_retraction`
to resolve the forward reference, then defined:
- `theorem no_retraction := bu_implies_no_retraction`
- `theorem brouwer_fixed_point := no_retraction_implies_brouwer_fp`

### Stats After Changes
- 5169 lines, 1 axiom (was 3), 0 sorries, Docker build passes
- The single remaining axiom is `borsuk_ulam_general` (general BU for n ≥ 1)
- Everything else (no-retraction, Brouwer FP, Lusternik-Schnirelmann) is proved

---

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

## Session 2026-03-19 (researcher-2, iteration 3) - Deduplication + Axiom Reduction

**Mode**: REVISIT (RICH knowledge)
**Outcome**: progress

### What I Did

**Structural cleanup**:
- Deduplicated file: 5393 → 3670 lines (removed 2 copies of Sections XLII-LIX from merge conflicts)
- 150 → ~170 unique declarations

**Section LXIII: Ray-Sphere Intersection Infrastructure (rebuilt)**
- `ip`, `nsq`: Inner product and norm squared on Fin k → ℝ
- `nsq_nonneg`, `nsq_eq_zero_iff`, `nsq_eq_ip`: Basic properties
- `ray_nsq_expand`: |a + td|² expansion
- `ray_discrim_nonneg`: Discriminant ≥ 0 for ball points
- `raySphereT`, `raySphereT_on_sphere`: Ray-sphere root and membership
- `retractT`, `retractT_is_root`, `retractT_on_sphere`: Retraction parameter

**Section LXIV: Retraction Fixes Sphere**
- `rayQuad_eval_one_eq_nsq`: Key identity A + 2B + C = |x|² - 1
- `ip_le_one`: ⟨fx, x⟩ ≤ 1 (Cauchy-Schwarz)
- `discrim_perfect_square`: When A+2B+C=0, Δ = (A+B)²
- `retractT_eq_one_on_sphere`: PROVED cleanly — t₊ = 1 on sphere
  Proof: A+2B+C = nsq(x)-1 = 0, so Δ = (A+B)². Since A+B ≥ 0,
  √Δ = A+B, and t₊ = (-B + A+B)/A = 1.

**Section LXV: No-Retraction → Brouwer FP**
- `no_retraction_implies_brouwer_fp`: Main theorem (1 sorry: continuity)
- `brouwer_axiom_reduction`: Documents axiom is conditionally redundant

### Key Findings
- The perfect square identity A+2B+C = nsq(x)-1 is the elegant core of the proof
- A+B ≥ 0 follows from ip(fx,x) ≤ 1 via 0 ≤ |x-fx|² expansion
- File had triple duplication of Sections XLII-XLIX from parallel researcher commits

### Stats
- **Lines**: 3670 (from 5393 after deduplication)
- **Declarations**: ~170 (from 215 duplicate to 170 unique + new)
- **Axioms**: 4 declared, 2 independent (BU_general, no_retraction)
- **Sorries**: 1 (continuity of retraction in no_retraction_implies_brouwer_fp)

### Next Steps
- Prove continuity of ray-sphere retraction (eliminates 1 sorry)
- Prove BU → no_retraction via degree theory (reduces axioms 2 → 1)

## Session 2026-03-19 (researcher-2, iteration 3) - Deduplication + Axiom Reduction

**Mode**: REVISIT (RICH knowledge)
**Outcome**: progress

### What I Did

**Structural cleanup**:
- Deduplicated file: 5393 → 3670 lines (removed 2 copies of Sections XLII-LIX from merge conflicts)

**Section LXIII: Ray-Sphere Intersection Infrastructure (rebuilt)**
- `ip`, `nsq`: Inner product and norm squared on Fin k → ℝ
- `nsq_nonneg`, `nsq_eq_zero_iff`, `ray_nsq_expand`, `ray_discrim_nonneg`
- `raySphereT`, `raySphereT_on_sphere`: Ray-sphere root
- `retractT`, `retractT_is_root`, `retractT_on_sphere`: Retraction parameter

**Section LXIV: Retraction Fixes Sphere**
- `rayQuad_eval_one_eq_nsq`: A + 2B + C = |x|² - 1
- `ip_le_one`: ⟨fx, x⟩ ≤ 1 (Cauchy-Schwarz)
- `discrim_perfect_square`: When A+2B+C=0, Δ = (A+B)²
- `retractT_eq_one_on_sphere`: PROVED — t₊ = 1 on sphere
  via √Δ = A+B, so t₊ = (-B + A+B)/A = 1

**Section LXV: No-Retraction → Brouwer FP**
- `no_retraction_implies_brouwer_fp` (1 sorry: continuity)
- Independent axiom count: 2 (BU_general, no_retraction)

### Key Findings
- Perfect square identity A+2B+C = nsq(x)-1 is the elegant core
- A+B ≥ 0 via ip(fx,x) ≤ 1 from 0 ≤ |x-fx|² expansion

### Stats
- **Lines**: 3670, **Declarations**: ~170, **Axioms**: 4 (2 independent), **Sorries**: 1

## Session 2026-03-19 (researcher-2, iteration 4) - BU → No Retraction

**Mode**: REVISIT (RICH knowledge)
**Outcome**: progress (major milestone - single axiom)

### What I Did

**Section LXVII: BU → No Retraction**
- `proj`, `lastCoord`: Coordinate helpers for Fin (n+2) → ℝ
- `proj_in_ball`: S^{n+1} projection lies in B^{n+1} (PROVED)
- `proj_on_sphere_at_equator`: Equator projects to S^n (PROVED)
- `hemisphereOddMap`: Piecewise odd map construction
- `hemisphereOddMap_on_sphere`: Maps S^{n+1} to S^n (PROVED)
- `hemisphereOddMap_odd_on_sphere`: Odd on S^{n+1} (PROVED, 3 cases)
- `bu_implies_no_retraction`: BU → no retraction (1 sorry: continuity)
- `no_retraction_axiom_redundant`: Witnesses axiom redundancy

### Key Findings
- Hemisphere folding: g(x) = r(π(x)) for upper hemisphere, -r(-π(x)) for lower
- Oddness on S^{n+1} proved with 3 cases (pos/neg/equator)
- Equator case: π(x₀) ∈ S^n so r fixes it, making both branches equal
- Global oddness FAILS (r(-y) ≠ -r(y) for general y)
- Global piecewise continuity also fails; need alternative extension

### Stats
- **Lines**: 3890, **Declarations**: 189, **Axioms**: 4 (1 independent), **Sorries**: 2

## Session 2026-03-19 (researcher-7) - Ball Projection + Retraction Continuity

**Mode**: REVISIT (RICH knowledge from 8+ prior sessions)
**Outcome**: progress (sorry elimination)

### What I Did

**Compilation bug fix**:
- Added missing `retractT` definition (was referenced but never defined)
- Added `retractT_eq_raySphereT` and `retractT_on_sphere` helper theorems

**Section LXV: Ball Projection Infrastructure**:
- `continuous_nsq'`: nsq is continuous (polynomial in coordinates)
- `ballProj`: x ↦ x/max(1,√nsq(x)), maps ℝ^k → B^k
- `continuous_ballProj`: ballProj is globally continuous
- `ballProj_in_ball`: nsq(ballProj(x)) ≤ 1
- `ballProj_fix_ball`: ballProj(x) = x when nsq(x) ≤ 1

**Section LXV-B: Complete proof of no_retraction_implies_brouwer_fp**:
- Eliminated sorry #1 (retraction continuity)
- Key insight: compose f with ballProj to get a SINGLE formula retraction
  r(x) = f(p(x)) + t(x)·(p(x) - f(p(x))) — no piecewise definition needed
- Continuity proved by decomposition: each component (A, B, disc, √, t, r_j)
  is a composition of continuous functions
- Division by A = nsq(d) is safe because A > 0 everywhere (f has no fixed point
  in the ball, and ballProj maps everything to the ball)

### Key Findings

- ballProj approach completely avoids piecewise continuity analysis
- The max formulation max(1, √nsq(x)) is trivially continuous and always > 0
- retractT and raySphereT are the same value: B²-A(C-1) = B²+A(1-C)
- Continuous.div + hA_ne handles the raySphereT division cleanly

### Stats
- **Lines**: 4087 (from 3940, +147 net)
- **Axioms**: 5 declared, 1 independent (borsuk_ulam_general)
- **Sorries**: 1 (down from 2) — hemisphere map continuity remains

### Next Steps
- Prove hemisphere odd map continuity (pasting lemma for closed hemispheres)
- Or reformulate g to avoid piecewise, similar to ballProj approach

---

## Session 2026-03-19 (researcher-3) - Radial Extension Continuity Infrastructure

**Mode**: REVISIT (RICH knowledge, score 65)
**Outcome**: progress (infrastructure for sorry elimination)

### What I Did

**Section LXIX: Radial Extension Continuity Infrastructure** (~160 lines, 12 declarations):
- `normSqrt`: √(Σ x²) as a named function
- `continuous_normSqrt`: proved continuous (sqrt ∘ sum of squares)
- `normSqrt_nonneg`, `normSqrt_eq_zero_iff`, `normSqrt_zero`: basic properties
- `component_le_one_of_on_sphere`: |r(y)_j| ≤ 1 when r maps to S^n
- `radialBranch1`, `radialBranch2`: globally defined (with 0/0=0 convention)
- `radialBranch1_zero`, `radialBranch2_zero`: both branches are 0 at origin
- `radialBranch1_bound`, `radialBranch2_bound`: |branch(x)_j| ≤ normSqrt(x)
- `equator_proj_on_sphere`: when x_{n+1}=0, proj(x/s) ∈ S^n
- `radial_branches_agree_on_equator`: branch1 = branch2 when x_{n+1} = 0

**Reformulation of g**:
- Proved g = if 0 ≤ x_{n+1} then radialBranch1 else radialBranch2 (eliminates dite)
- Reduced sorry from "prove entire continuity" to "prove component-wise ContinuousAt"

### Key Finding
The sorry reduces to a 4-case ContinuousAt argument:
(a) x₀_{n+1} > 0: g = branch1 in open neighborhood, branch1 continuous on {normSqrt > 0}
(b) x₀_{n+1} < 0: g = branch2 in open neighborhood
(c) x₀_{n+1} = 0, x₀ ≠ 0: branches agree (radial_branches_agree_on_equator) + both continuous
(d) x₀ = 0: |g(x)_j| ≤ normSqrt(x) → 0 by squeeze (radialBranch*_bound + continuous_normSqrt)

### Stats
- **Lines**: 4304 (from 4087, +217)
- **Declarations**: ~200 (12 new)
- **Sorries**: 1 (same, but much more tractable now)

### Next Steps (for sorry elimination)
1. Prove branch1/branch2 are continuous on {normSqrt > 0} using Continuous.div
2. Use Metric.tendsto_nhds for squeeze at origin
3. Combine with ContinuousAt case analysis

---

## Session 2026-03-19 (researcher-3, iteration 2) - SORRY ELIMINATED!

**Mode**: REVISIT (continuation of previous session)
**Outcome**: MAJOR MILESTONE — eliminated the last sorry!

### What I Did

**Proved radial extension continuity** (the sorry at line 4194):
- Decomposed proof into 3 steps:
  1. Prove `radialBranch1_j` is globally continuous (ContinuousAt at each point)
  2. Prove `radialBranch2_j` is globally continuous (same structure)
  3. Prove piecewise is continuous (ContinuousAt via 3-way case split)

**Continuity proof structure for each branch**:
- At origin (normSqrt = 0): Metric.continuousAt_iff + squeeze via radialBranch*_bound
- Away from origin: ContinuousAt.mul with normSqrt and composition (Continuous.div for proj/normSqrt)

**Piecewise continuity**:
- Upper half-space (x_{n+1} > 0): g locally = branch1, ContinuousAt.congr
- Lower half-space (x_{n+1} < 0): g locally = branch2, ContinuousAt.congr
- Equator (x_{n+1} = 0): Filter.tendsto_def + both branches → same limit + split_ifs

### Key Technique
The equator case uses `Filter.tendsto_def`: for any open U ∋ f(x₀),
`f⁻¹(U) ⊇ branch1⁻¹(U) ∩ branch2⁻¹(U)` (both in nhds x₀), and
`split_ifs` dispatches to the correct branch.

### Stats
- **Lines**: 4389 (from 4304, +85 net)
- **Sorries**: 0 (down from 1!) ← **MAJOR MILESTONE**
- **Axioms**: 4 declared, 1 independent (borsuk_ulam_general)

### What This Means
The complete axiom reduction chain is now sorry-free:
- BU_general → no_retraction (Section LXVII, 0 sorries)
- no_retraction → brouwer_fixed_point (Section LXV, 0 sorries)
- BU_general → lusternik_schnirelmann (Section LX, 0 sorries)

All 3 derived axioms are fully proved from the single axiom borsuk_ulam_general.

## Session 2026-03-19 (researcher-3, iteration 3) - Mathlib v4.26.0 Compat Fixes

**Mode**: REVISIT (RICH knowledge, maintenance)
**Outcome**: completed (build fix)

### What I Did

Fixed all build errors caused by Lean 4 v4.26.0 / Mathlib updates:

**Critical fix: `set k := n+1` → `let k := n+1`**
- In Lean 4 v4.26.0, `set` renames hypothesis variables when their type is modified by substitution
- `f : (Fin (n+1) → ℝ) → ...` became `f✝` after `set k := n+1` replaced `n+1` with `k`
- Fix: Use `let` (non-substituting) instead of `set`

**Tactic fixes:**
- `congr 1; ext i; ring` → `Finset.sum_congr rfl fun i _ => by ring` (ext/ring under binder)
- `Fin.sum_univ_castSucc; ring` → explicit `linarith` with sum lemma (`ring` can't cancel Finset.sum terms)
- `nlinarith [abs_nonneg ...]` → `nlinarith [sq_abs ..., sq_nonneg (|x| - 1)]` (stronger hints needed)
- `unfold_let A B` → `simp only [A, B]` (unfold_let removed/deprecated)
- `field_simp` → `div_eq_iff (ne_of_gt hA_pos)` (field_simp too aggressive)
- `rw [div_pow, ...]` → `simp only [div_pow]; rw [...]` (div_pow can't match under binders via rw)
- `rw [normSqrt_eq_zero_iff]; rfl` → `rw [normSqrt_eq_zero_iff]` (rfl now redundant)

### Key Findings

- **Lean 4 v4.26.0 `set` behavior change**: `set x := expr` now renames hypothesis variables whose types contain `expr`, creating inaccessible `f✝` bindings. Use `let` instead when you don't need substitution in hypotheses.
- **`ring` limitation**: Cannot cancel `Finset.sum` terms (e.g., `∑ i, a i = (∑ i, a i + b) - b`). Use `linarith` with the sum decomposition lemma as a hypothesis.
- **`nlinarith` on absolute values**: Needs explicit `sq_abs` and `sq_nonneg (|x| - 1)` hints to derive `|x| ≤ 1` from `x^2 ≤ 1`.

### Stats
- **Lines**: 4825, **Declarations**: 247, **Sorries**: 0, **Axioms**: 6 (1 independent)
- PR #4165 created

## Session 2026-03-19 (researcher-2, iteration 5) - Build Fix + Half-Period Coincidence

**Mode**: REVISIT (RICH knowledge, maintenance + new content)
**Outcome**: progress

### What I Did

**Build Fix**:
- Fixed proofHierarchy duplicate entry: ham_sandwich appeared twice (8 elements, theorem claimed 7)
- Removed the duplicate `⟨3, "ham_sandwich", "BU general + IVT", "axiom (abstract measures)"⟩`
- Fixed meta.json sorry count (1→0, was incorrectly set to 1 in prior session)

**Section LXXIII: Half-Period Coincidence (Universal Chord Theorem)**:
- `half_period_coincidence`: For continuous f with f(0)=f(1), ∃ x∈[0,1/2] with f(x)=f(x+1/2) (PROVED)
  - Uses antisymmetric difference g(x) = f(x) - f(x+1/2)
  - g(0) + g(1/2) = f(0) - f(1) = 0, so opposite signs → IVT gives zero
- `universal_chord_n2`: Corollary restating as n=2 Universal Chord Theorem (PROVED)
- `chord_existence_witness`: Trivial witness showing non-vacuity (PROVED)

**Docker build**: Verified successful compilation (7743 jobs, 0 errors, warnings only)

### Key Findings

- proofHierarchy had a merge artifact: duplicate ham_sandwich with conflicting status strings
- File edits can be reverted by background processes (linters/hooks) — need to verify edits persist before committing
- The half-period coincidence proof is structurally identical to borsuk_ulam_interval: define antisymmetric difference, check sign at endpoints, apply IVT

### Stats
- **Lines**: 5105 (from 5027)
- **Declarations**: ~260 (3 new proved results + build fix)
- **Axioms**: 4 (1 independent)
- **Sorries**: 0

### Next Steps
- The general Universal Chord Theorem (for all n≥1) could be proved using telescoping sum + IVT
- Consider cleaning up the omega/norm_num tactic warnings (lines 2561, 4562, 4938)
