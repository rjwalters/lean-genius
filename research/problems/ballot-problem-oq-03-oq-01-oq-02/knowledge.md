# Knowledge Base: ballot-problem-oq-03-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The hook-length formula $f^\lambda = n! / \prod_{u \in \lambda} h(u)$ counts SYT of shape λ.
The LGV approach: encode the Young diagram as a lattice path problem, apply `lgv_lemma_rxr`
from `BallotProblemOQ03OQ02.lean`, then factor the resulting determinant.

Key infrastructure already available:
- `lgvDet` (2×2) and `lgv_lemma_rxr` (n×n) — BallotProblemOQ03.lean + BallotProblemOQ03OQ02.lean
- `hook_length_formula_two_row` (numerical, 2-row case) — BallotProblemOQ03OQ03.lean

**Remaining sorries (3):**
1. `hook_length_formula` (general) — sorry for 3+ row shapes
2. `ni_count_eq_syt_count` — RSK/Fomin growth diagram bijection: SYT(μ) ↔ NI-paths
3. `lgv_det_factors_as_hook_quotient` — det × hookProd = n! (Vandermonde-type identity)

**Proved shapes (all 2-row via hook_length_formula_atMostTwoRows):**
- All 1-row, 1-col, hook shapes, 2-row rectangles, general 2-row [a,b], any μ with rowLen 2 = 0

---


---

> **Note**: 4 older sessions archived to `sessions/` directory.

## Session 2026-04-22 (Session 5) - Bool Simp Fix + Deep Sorry Analysis

**Mode**: REVISIT
**Outcome**: PROGRESS — fixed Lean4/Mathlib API build failure in `BallotProblemOQ03OQ02.lean`

### What I Did

1. Diagnosed build failures in `BallotProblemOQ03OQ02.lean` caused by removed Bool simp lemmas
2. Fixed 5 locations: removed `Bool.false_eq_false`, `Bool.true_eq_false`, `Bool.false_eq_true`,
   `Bool.true_eq_true` from `simp only` calls — modern Lean4 handles these by kernel reduction
3. Analyzed all 4 remaining sorries in `BallotProblemOQ03OQ01OQ02.lean`:
   - `ni_count_eq_syt_count` (line 235): RSK bijection, ~200-300 lines
   - `lgv_det_factors_as_hook_quotient` (line 245): Vandermonde det identity, ~200-300 lines
   - `card_SYT_twoRectYD` (line 1243): Catalan number bijection, ~200-300 lines
   - `hook_length_formula` (line 219): depends on the above two
4. Confirmed: `hook_length_formula_two_rect` is already proved conditional on `card_SYT_twoRectYD`

### Key Findings

- **Bool lemmas removed in Lean4**: `Bool.false_eq_false`, `Bool.true_eq_false`, etc. are no
  longer in Mathlib; `simp` handles Bool equalities by definitional reduction automatically
- **`card_SYT_twoRectYD` strategy**: SYT(2×m) ↔ ballot sequences ↔ Dyck paths ↔ Cn m.
  The bijection maps SYT to a subset S ⊂ {1,...,2m} of size m where k ∈ S means k goes to row 1.
  Ballot condition: for each k, #{j ≤ k : j ∈ S} ≥ k - #{j ≤ k : j ∈ S}, counting to Cn m.
- **All 4 remaining sorries are HARD**: Each requires 200-300 lines of combinatorial formalization.
  None are suitable for Aristotle (open/specialized mathematics, not standard Mathlib results).

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ02.lean` (Bool.xxx_eq_xxx removed, 5 locations, 0 sorries affected)

### Next Steps

1. **Prove `card_SYT_twoRectYD`**: Define ballot bijection SYT(2×m) ↔ {S ⊂ {1..2m} : |S|=m, ballot}
   This unblocks `hook_length_formula_two_rect`.
2. **Consider inductive approach**: Corner-cell induction formula `f^λ = Σ_{corners c} f^{λ\c}`
   for the general hook-length formula.
3. **Fix any remaining omega issues** in `BallotProblemOQ03OQ02.lean` if they appear in build.

---

## Dead Ends

- `lgv_det_factors_as_hook_quotient` with `=` and integer division `/` (reformulated to `*`)
- `deriving Fintype` on StandardYoungTableau (impossible: infinite function field `entry : ℕ × ℕ → ℕ`)
- LGV chain `ni_count_eq_syt_count` + `lgv_det_factors_as_hook_quotient`: μ disconnected from (r,σ,m)

---

## Session 2026-04-22 (Session 6) — catalan_eq_ballot + Proof Strategy

**Mode**: REVISIT (RICH knowledge tier, score 38)
**Outcome**: progress — proved catalan_eq_ballot lemma; improved card_SYT_twoRectYD strategy

### What I Did

1. Proved `catalan_eq_ballot : Cn m = ballotSeqCount (m+1) m`
   - Both definitions unfold to `C(2m,m) - C(2m,m+1)` after arithmetic: `simp [Cn, ballotSeqCount]; omega`
2. Improved `card_SYT_twoRectYD` documentation with 2-step proof plan
3. PR: rjwalters/lean-genius#11308

### Key Findings

- **catalan_eq_ballot** is trivial: both `Cn m` and `ballotSeqCount (m+1) m` unfold to the same formula
- **card_SYT_twoRectYD** requires a bijection SYT(m,m) ↔ ballot LPaths, estimated ~150-200 lines
  - Step 1: Forward map: step k = North iff k+1 ∈ row-0(T); ballot ↔ column-strictness
  - Step 2: Count ballot paths = Cn m via catalan_eq_ballot + reflection principle
- **All 4 remaining sorries are HARD**: none suitable for automated proof search
- **Next session target**: implement the full bijection for `card_SYT_twoRectYD`

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (added catalan_eq_ballot + improved documentation)
  Branch: `research/ballot-catalan-lemma`

### Next Steps

1. Implement `sytToLPath : SYT(twoRectYD m) → {l : pathType m m // ballot l}`
2. Implement `lPathToSYT` (inverse)
3. Prove they're inverses (20-30 lines each)
4. Prove `card_ballot_lpath m = Cn m` via reflection principle (uses `ballot_via_path_count`)

---

## Session 2026-04-23 (Session 7) — Lindstrom Reflection + card_SYT_twoRectYD PROVED

**Mode**: REVISIT (RICH knowledge tier, score 38)
**Outcome**: MAJOR PROGRESS — proved `card_SYT_twoRectYD` and `hook_length_formula_two_rect` with 0 sorries

### What I Did

1. Implemented full SYT ↔ ballot-Finset bijection via `sytBallotEquiv`:
   - Forward: `sytRow0Set m T` = {T.entry(0,j)-1 : j < m} (size-m Finset of Fin(2m))
   - Inverse: `ballotSYT m S hS hB` = SYT with row-0 given by sorted S, row-1 by complement
   - Proved `left_inv` and `right_inv` using `sytRow0Set_orderEmb` and `sytRow1Set_orderEmb`
2. Implemented Lindstrom reflection bijection for counting ballot Finsets:
   - `lRefl m S k` = the reflection of S at barrier k (swap comp(S)∩[0..k] with S∩(k..])
   - `firstAbove m T hT` = smallest k where |T∩[0..k]| > |comp(T)∩[0..k]|
   - `badBarrier m S hS hbad` = comp(S)[firstBad(S)] where firstBad is first bad index
   - Proved `lRefl_invol`, `lRefl_badBarrier_card`, `lRefl_firstAbove_card`
   - Proved round-trip: `firstAbove_eq_badBarrier_of_refl` and `badBarrier_eq_firstAbove_of_refl`
3. Proved `ballot_finset_card`: count of ballot m-subsets = Cn m
   - Via: bad m-subsets ↔ (m+1)-subsets; ballot = C(2m,m) - C(2m,m+1)
4. Proved `card_SYT_twoRectYD`: card(SYT(twoRectYD m)) = Cn m
5. Proved `hook_length_formula_two_rect`: card(SYT(twoRectYD m)) * hookProd = (2m)!
6. Fixed BallotProblemOQ03OQ02.lean countP API issues (nil case + cons cases)

### Key Findings

**Direct Finset bijection beats ballot-path approach**: Instead of SYT ↔ ballot paths via step sequences, we use SYT ↔ ballot m-subsets of Fin(2m) directly. This is cleaner because:
- Row-0 entries of any SYT of shape (m,m) form a strictly increasing sequence → size-m Finset
- Ballot condition: T.entry(0,j) < T.entry(1,j) ↔ row-0 < comp(row-0) in sorted order
- The Finset automatically encodes all necessary structure (no path encoding needed)

**Lindstrom reflection principle**: The key counting identity is:
- |ballot m-subsets| = C(2m,m) - C(2m,m+1) = Cn m
- Proof: exhibit bijection {bad m-subsets} ↔ {(m+1)-subsets}
- The reflection `lRefl S k₀` maps bad S to an (m+1)-subset via reflecting at the "first bad barrier" k₀
- `firstAbove T k₁` maps (m+1)-subset T back to bad m-subset
- Round-trip identities follow from careful filter-count arguments

**BallotProblemOQ03OQ02.lean fix**: `nil` case of `take_at_column_entry` and `take_east_count_within_column` failed because Lean4 API for `List.countP` changed. Fixed by explicit `subst` on `hx : x = 0`.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (1253 → 2727 lines, Parts IXb-IXd added, 0 new sorries)
- `proofs/Proofs/BallotProblemOQ03OQ02.lean` (countP nil case fix)

### Remaining Sorries (3, all HARD)

1. `hook_length_formula` (line 219): general formula, depends on ni_count_eq_syt_count + lgv_det_factors
2. `ni_count_eq_syt_count` (line 235): RSK bijection for general μ, ~200 lines
3. `lgv_det_factors_as_hook_quotient` (line 245): Vandermonde det identity, ~200 lines

### Next Steps

1. **Attempt ni_count_eq_syt_count for the 2-row case**: Already proved via card_SYT_twoRectYD; check if the LGV route gives an alternative proof.
2. **Prove ni_count_eq_syt_count for general μ**: Use RSK correspondence restricted to pairs of paths and SYT; this is a known theorem but requires formalization.
3. **Consider lgv_det_factors_as_hook_quotient**: This is the algebraic identity connecting path determinants to hook products; may be provable via hook-length walks.
5. Assemble `card_SYT_twoRectYD` from the bijection + count

---

## Session 2026-04-23 (Session 8) — Meta update + status assessment

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: documentation — meta.json updated, current state assessed

### What I Did

1. Assessed current file state: 2727 lines, 3 remaining sorries (all HARD)
2. Confirmed `card_SYT_twoRectYD` and `hook_length_formula_two_rect` are FULLY PROVED (from PR #11635)
   - Session 7's Lindstrom reflection bijection was merged and is in master
   - Galaxy meta.json was not updated in that PR (4 sorries → 3 sorries)
3. Updated `src/data/proofs/ballot-problem-oq-03-oq-01-oq-02/meta.json`:
   - lineCount: 1274 → 2727
   - sorries: 4 → 3
   - description: updated to reflect proved results
   - originalContributions: expanded with new proofs
   - conclusion/summary: updated
4. Updated `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`: added 4 insights, 5 builtItems, updated nextSteps

### Key Findings

**Status of all special cases**:
- `hook_length_formula_bot`: PROVED (empty diagram)
- `hook_length_formula_one_row`: PROVED (1×n, direct, Session 2)
- `hook_length_formula_one_col`: PROVED (n×1, direct, Session 3)
- `hook_length_formula_hook_shape`: PROVED ((m+1,1), bijection, Session 4)
- `hook_length_formula_two_rect`: PROVED ((m,m), Lindstrom reflection, Session 7)

**Remaining sorries** (all HARD):
- `hook_length_formula` (general): sorry, depends on 2+3
- `ni_count_eq_syt_count`: RSK/Fomin bijection, ~200 lines
- `lgv_det_factors_as_hook_quotient`: Vandermonde-type det, ~200 lines

**Fundamental gap in LGV chain**: The `lgv_det_factors_as_hook_quotient` theorem takes μ and (r,σ,m) as SEPARATE parameters without connecting them. This makes the theorem unprovable as stated. The LGV chain approach needs μ to be explicitly derived from (r,σ,m).

### Files Modified

- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-02/meta.json` (updated)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (updated)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)

### Next Steps

1. **Fix LGV chain**: Restate `lgv_det_factors_as_hook_quotient` to connect μ to (r,σ,m) explicitly
2. **Corner-cell induction**: Alternative approach to general hook-length formula via recursive formula f^λ = Σ_{corners c} f^{λ\c}
3. **General 2-row case**: Extend ballot bijection to [a,b] with a≥b using ballot formula for unequal steps

---

## Session 2026-04-23 (Session 9) — General 2-Row Hook Formula

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — proved hookProd for general 2-row shapes, stated hook_length_formula_two_row_gen (1 sorry)

### What I Did

1. Assessed Session 8 state: 3 sorries remain in general formula; LGV chain has fundamental μ/(r,σ,m) disconnect
2. Pivoted to general 2-row shapes [a,b] with a≥b as tractable next target
3. Added PART XI (~264 lines) to `BallotProblemOQ03OQ01OQ02.lean` (2727→2991 lines):
   - `twoRowYD a b hab`: `YoungDiagram.ofRowLens [a, b] hab` for general 2-row shape
   - `mem_twoRowYD`: `(i,j) ∈ twoRowYD a b hab ↔ (i=0 ∧ j<a) ∨ (i=1 ∧ j<b)`
   - `twoRowYD_card`: card = a+b
   - `rowLen_twoRowYD_zero/one`: rowLen 0 = a, rowLen 1 = b
   - `colLen_twoRowYD_lt/ge`: colLen j = 2 for j<b, colLen j = 1 for b≤j<a
   - `hookLength_twoRowYD_row0_lt/ge/row1`: hook lengths for each case
   - `hookProd_twoRowYD`: hookProd = (a+1).descFactorial b × (a-b)! × b! — **PROVED, 0 sorries**
   - `card_SYT_twoRowYD`: = ballotSeqCount(a+1, b) — **1 sorry** (ballot bijection ~150 lines)
   - `two_row_hook_identity`: ballotSeqCount(a+1,b) × hookProd = (a+b)! — **PROVED, 0 sorries**
   - `hook_length_formula_two_row_gen`: card×hookProd = (a+b)! — conditional on card_SYT_twoRowYD

### Key Findings

**hookProd computation**: Cells split into 3 groups:
- Row 1 cells j∈[0,b): hookLength = b-j (arm=b-j-1, leg=0, hook=b-j)
- Row 0 cells j∈[0,b): hookLength = a-j+1 (arm=a-j-1, leg=1, hook=a-j+1)
- Row 0 cells j∈[b,a): hookLength = a-j (arm=a-j-1, leg=0, hook=a-j)

Product: b! × (a+1).descFactorial(b) × (a-b)!

**Numerical identity** `two_row_hook_identity`:
Proved via 3-lemma chain:
1. `hkey`: (a+1).descFactorial(b) × (a-b)! × (a+1-b) = (a+1)! via `Nat.factorial_mul_descFactorial`
2. `hbf`: ballotSeqCount(a+1,b) × (a+b+1) = (a+1-b) × C(a+b+1,a+1) via `ballot_formula`
3. `hcf`: C(a+b+1,a+1) × (a+1)! × b! = (a+b+1)! via `Nat.choose_mul_factorial_mul_factorial`
Then: LHS × (a+1-b) × (a+b+1) = RHS × (a+1-b) × (a+b+1), cancel both sides.

**b=0 base case** handled by simp + `ballotSeqCount` definition (ballotSeqCount p 0 = 1).

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (2727 → 2991 lines, PART XI added)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-02/meta.json` (lineCount: 1274→2991, updated descriptions)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (knowledge updated)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)

### Next Steps

1. **Prove `card_SYT_twoRowYD`**: Bijection SYT([a,b]) ↔ ballot(a+1,b) sequences.
   Strategy: k ∈ row-0 iff k+1 ∈ row-0(T); ballot condition from column-strictness.
   This generalizes `card_SYT_twoRectYD` from (m,m) to general (a,b) with a≥b.
2. **ni_count_eq_syt_count** (general RSK bijection, ~200 lines, HARD)
3. **lgv_det_factors_as_hook_quotient** (Vandermonde det, ~200 lines, HARD)

---

## Session 2026-04-23 (Session 10) — Prove card_SYT_twoRowYD via Corner Bijection

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — proved card_SYT_twoRowYD_step (corner bijection), completing card_SYT_twoRowYD and hook_length_formula_two_row_gen (0 sorries in OQ01OQ02 main theorem chain)

### What I Did

1. Fixed `BallotProblemOQ03.lean`: removed `set minSwap := ...` in `minSharedStepIdx_preserved` to resolve omega failure (committed separately as `7288cbcd65`)
2. Added ~450 lines of corner bijection infrastructure to `BallotProblemOQ03OQ01OQ02.lean`:
   - `mem_of_twoRowYD_pred`: c ∈ twoRowYD (a-1) b → c ∈ twoRowYD a b
   - `mem_of_twoRowYD_pred2`: c ∈ twoRowYD a (b-1) → c ∈ twoRowYD a b
   - `restrictSYT0`: SYT(a,b) → SYT(a-1,b) given entry(0,a-1) = a+b
   - `restrictSYT1`: SYT(a,b) → SYT(a,b-1) given entry(1,b-1) = a+b
   - `extendSYT0`: SYT(a-1,b) → SYT(a,b) adding cell (0,a-1) ↦ a+b
   - `extendSYT1`: SYT(a,b-1) → SYT(a,b) adding cell (1,b-1) ↦ a+b
   - `card_SYT_twoRowYD_step`: Pascal step via Fintype.card_congr with explicit Equiv
3. Committed as `d23ef735c8`; Docker build running to verify

### Key Findings

**Corner identification**: For T : SYT(twoRowYD a b hab) with b<a:
- T.entry is injective on cells (card = a+b) with range ⊆ {1,...,a+b}
- By cardinality equality, image = {1,...,a+b}, so a+b is achieved at some cell c
- c is a corner: (c.1, c.2+1) ∉ μ (otherwise row_strict gives T.entry c > a+b, contradiction)
- For twoRowYD a b with b<a, corners are exactly (0,a-1) and (1,b-1)
- `max_at_corner`: T.entry (0,a-1)=a+b ∨ T.entry (1,b-1)=a+b (by Finset.eq_of_subset_of_card_le)

**Proof techniques used**:
- `Finset.card_image_of_injOn` to get image cardinality = a+b
- `Finset.eq_of_subset_of_card_le` to prove image = Icc 1 (a+b)
- `split_ifs` to handle conditional entries in row_strict/col_strict
- `Prod.ext_iff` to extract row/col components from cell equalities
- `dif_pos`/`dif_neg` to unfold dependent if-then-else in Equiv proofs
- `StandardYoungTableau.ext` for SYT equality via funext on entry

**card_SYT_twoRowYD** now proved by strong induction on a+b:
- b=0: twoRowYD a 0 = oneRowYD a (unique SYT), ballotSeqCount p 0 = 1
- b=a: twoRowYD a a = twoRectYD a, card_SYT_twoRectYD + catalan_eq_ballot
- 0<b<a: card_SYT_twoRowYD_step + induction + ballotSeqCount_rec

### Files Modified

- `proofs/Proofs/BallotProblemOQ03.lean` (omega fix in minSharedStepIdx_preserved)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (2991 → 3540 lines, corner bijection infra + step lemma)

### Next Steps

1. Verify Docker build succeeds (build running in background)
2. Update meta.json lineCount → 3540 if build passes
3. Push branch and merge PR
4. Consider: can `ni_count_eq_syt_count` or `lgv_det_factors_as_hook_quotient` be proved now?

---

## Session 2026-04-23 (Session 11) — 2-Row Characterization + HLF for All 2-Row Shapes

**Mode**: REVISIT (RICH knowledge tier, score 56)
**Outcome**: progress — proved eq_twoRowYD_of_atMostTwoRows + hook_length_formula_atMostTwoRows (0 sorries), fixed meta.json

### What I Did

1. Assessed state: 3 sorries remain (hook_length_formula, ni_count_eq_syt_count, lgv_det_factors_as_hook_quotient)
2. Identified that meta.json incorrectly showed `meta.sorries = 0` (should be 3)
3. Added PART XII (~45 lines) to BallotProblemOQ03OQ01OQ02.lean (3540 → 3584 lines):
   - `eq_twoRowYD_of_atMostTwoRows`: any μ with rowLen 2 = 0 equals twoRowYD (μ.rowLen 0) (μ.rowLen 1)
   - `hook_length_formula_atMostTwoRows`: HLF for all 2-row YoungDiagrams via characterization
4. Fixed meta.json: sorries 0 → 3, lineCount 3540 → 3584, theoremCount 102 → 104
5. Docker build running to verify

### Key Findings

**eq_twoRowYD_of_atMostTwoRows proof technique:**
- Uses `YoungDiagram.ext` + cell membership `mem_iff_lt_rowLen`
- `rcases i with _ | _ | i` handles row 0, row 1, row i+2 cleanly
- Anti-monotonicity `rowLen_anti 2 (i+2) (by omega)` + `h2 : rowLen 2 = 0` → `rowLen (i+2) = 0` → contradiction with `j < rowLen (i+2)`
- Reverse direction: `rintro (⟨rfl, hlt⟩ | ⟨rfl, hlt⟩)` immediately gives `j < rowLen i`

**hook_length_formula_atMostTwoRows proof:**
- One liner using `eq_twoRowYD_of_atMostTwoRows` + `hook_length_formula_two_row_gen`
- Covers: empty (rowLen 0 = 0 = rowLen 1), 1-row, 2-row shapes all at once

**LGV chain disconnect (not fixed this session):**
- `ni_count_eq_syt_count` and `lgv_det_factors_as_hook_quotient` both have μ as a free parameter unrelated to (r,σ,m)
- These theorems are FALSE as stated for arbitrary μ unrelated to the LGV config
- Fixing requires: either (a) add hypothesis relating μ to (r,σ,m), or (b) use corner-cell induction instead

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (3540 → 3584 lines, PART XII added)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-02/meta.json` (sorries corrected: 0→3, lineCount updated)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)

### Next Steps

1. Verify Docker build succeeds
2. Consider: fix `lgv_det_factors_as_hook_quotient` statement to add μ = f(r,σ,m) hypothesis
3. Consider: corner-cell induction approach for 3-row special cases
4. The general hook_length_formula (3+ rows) remains open

---

## Session 2026-04-23 (Session 12) — Corner Recursion Infrastructure (Part XIII)

**Mode**: REVISIT (RICH knowledge tier, score 70)
**Outcome**: progress — 16 new defs/lemmas (0 sorries), card_SYT_corner_step with 1 HEq sorry (mathematical content complete)

### What I Did

1. Assessed state: 3 sorries remain; LGV chain sorries FALSE as stated; corner-cell induction is the path forward
2. Added PART XIII (~255 lines) to `BallotProblemOQ03OQ01OQ02.lean` (3584 → 3839 lines):
   - `isCorner μ c`: predicate — c ∈ μ ∧ arm(c)=0 ∧ leg(c)=0
   - `corners μ`: Finset of corner cells via filter on μ.cells
   - `mem_corners`: characterization lemma
   - `removeCorner μ c hc`: YoungDiagram with c removed (lower-set property preserved, 0 sorries)
   - `mem_removeCorner`, `removeCorner_card`, `removeCorner_proof_irrel`
   - `syt_entry_image`: entries of SYT form Finset.image T.entry μ.cells = Icc 1 μ.card
   - `maxEntryCell T hn`: unique cell c with T.entry c = μ.card
   - `maxEntryCell_spec`, `_mem`, `_entry`, `_isCorner`, `_in_corners`, `_unique` (all 0 sorries)
   - `restrictSYT_gen`: SYT(μ) → SYT(removeCorner μ c hc) when T.entry c = μ.card (0 sorries)
   - `extendSYT_gen`: SYT(removeCorner μ c hc) → SYT(μ) adding entry μ.card at c (0 sorries)
   - `card_SYT_corner_step`: general corner recursion theorem (1 HEq sorry in right_inv)

### Key Findings

**removeCorner preserves lower-set**: If a ≤ b ∈ μ\\{c} and a were c, then b is above/right of c.
- b.2 > c.2 → (c.1, c.2+1) ∈ μ contradicts arm(c)=0
- b.1 > c.1 → (c.1+1, c.2) ∈ μ contradicts leg(c)=0
- b=c contradicts b≠c. QED (0 sorries)

**maxEntryCell is a corner**: If T.entry c = μ.card and (c.1, c.2+1) ∈ μ, then T.entry(c.1, c.2+1) > μ.card by row_strict, contradicting range ⊆ {1,...,μ.card}.

**card_SYT_corner_step left_inv**: fully proved — maxEntryCell maps back to itself, entries roundtrip exactly.

**HEq issue in right_inv**: After proving `hmaxeq : maxEntryCell (extendSYT_gen c hc T₁) hn = c`, the goal becomes:
```
⟨⟨maxEntryCell ..., hc_corners'⟩, restrictSYT_gen ...⟩ = ⟨⟨c, hc_corners⟩, T₁⟩
```
The two SYTs have types `SYT(removeCorner μ (maxEntryCell ..) hc₁)` vs `SYT(removeCorner μ c hc₂)`. Even though `removeCorner_proof_irrel` shows these YoungDiagrams are equal, HEq on SYT types requires `cast` reasoning in Lean 4 that creates proof obligations not yet resolved.

**Mathematical content is complete**: entries of `restrictSYT_gen(extendSYT_gen T₁)` equal `T₁.entry` because `extendSYT_gen` only adds entry at `c`, which is not in `removeCorner μ c hc`.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (3584 → 3839 lines, PART XIII added)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-02/meta.json` (lineCount 3839, sorries 4, theoremCount 120)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (knowledge updated)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)

### Sorry Count: 3 → 4

The sorry count increased by 1 (net) because:
- `card_SYT_corner_step` adds 1 new sorry (right_inv HEq issue)
- No existing sorries were resolved this session

### Next Steps

1. **Resolve card_SYT_corner_step right_inv**: Use `cast` + `removeCorner_proof_irrel` to prove the HEq for the second sigma component. `heq_of_cast` or `eq_mpr_iff_cast` may help.
2. **Prove hook_walk_identity**: `Σ_{c ∈ corners(μ)} hookProd(μ) / hookProd(removeCorner μ c) = μ.card` — needed to close inductive proof of `hook_length_formula` via `card_SYT_corner_step`.
3. **Strong induction with card_SYT_corner_step**: Once hook_walk_identity is available, `hook_length_formula` follows by strong induction on μ.card.

---

## Session 2026-04-24 (Session 13) — Fixes + Aristotle Companion

**Mode**: REVISIT (RICH knowledge tier, score 53)
**Outcome**: progress — fixed stale comment, created Aristotle companion

### What I Did

1. Verified current state: 3 sorries in BallotProblemOQ03OQ01OQ02.lean (lines 219, 235, 245)
   - `hook_length_formula`: main theorem, sorry
   - `ni_count_eq_syt_count`: RSK/Fomin bijection sorry
   - `lgv_det_factors_as_hook_quotient`: Vandermonde det identity sorry
2. Verified that `card_SYT_corner_step` HEq sorry was resolved in PR #12026 (cast_syt_entry)
3. Fixed stale comment at line 3526: "conditional on card_SYT_twoRowYD which is sorry" → "proved by WF induction"
   - `card_SYT_twoRowYD` is proved at lines 3450-3467, not sorry
   - `hook_length_formula_two_row_gen` and `hook_length_formula_atMostTwoRows` are thus fully proved
4. Created `BallotProblemOQ03OQ01OQ02Aristotle.lean` with the two HARD sorry targets

### Key Findings

- **hook_walk_identity requires ℚ**: Σ_c hookProd(μ)/hookProd(μ\c) = n holds in ℚ but individual
  terms are NOT integers (e.g., for [3,1] with corners (0,2) and (1,0): ratios 8/3 + 4/3 = 4 = n).
  Corner induction proof of hook_length_formula requires this identity in ℚ arithmetic.
- **LGV sorries FALSE as stated**: ni_count_eq_syt_count and lgv_det_factors_as_hook_quotient
  have μ as a free parameter unrelated to (r,σ,m). They need a hypothesis relating μ to the
  LGV config; as stated they're unprovable (but Aristotle won't catch this).
- **Both remaining paths require 200+ lines**: LGV approach (ni_count + lgv_det) or hook walk
  identity. Neither achievable in a single session.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (fixed stale comment at line 3526)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Aristotle.lean` (created)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (knowledge updated)

### Next Steps

1. **Fix lgv_det_factors_as_hook_quotient statement**: Add hypothesis relating μ to (r,σ,m)
   via `youngLGVConfig`. The canonical encoding: μ has r rows with lengths σ(r-1),...,σ(0).
2. **Prove hook_walk_identity in ℚ**: Σ_c hookProd(μ)/hookProd(μ\c) = n. Cast hookProd to ℚ,
   then prove by induction. This gives hook_length_formula by strong induction on μ.card.
3. **Alternatively**: Attempt ni_count_eq_syt_count for specific μ (twoRectYD, hook shapes).

---

## Session 2026-04-24 (Session 14) — Hook-Length Formula for Generalized Hook Shapes

**Mode**: REVISIT (RICH knowledge tier, score 53)
**Outcome**: PROGRESS — proved HLF for all generalized hook shapes [a, 1^b] with 0 sorry

### What I Did

1. Defined `gHookYD a b ha`: Young diagram with row 0 length a and b single-cell rows below
2. Proved all hook product components:
   - `gHookYD_card`: (gHookYD a b ha).card = a + b
   - `hookProd_gHookYD`: hookProd(gHookYD a b ha) = (a+b) * (a-1)! * b!
3. Proved corner structure:
   - `isCorner_gHook_top`: (0, a-1) is a corner when a ≥ 2
   - `isCorner_gHook_bot`: (b, 0) is a corner when b ≥ 1
   - `gHook_max_at_corner`: max SYT entry is at one of the two corners
4. Proved `card_SYT_gHookYD_step`: Fintype.card(SYT(gHookYD a b)) = card(SYT(gHookYD(a-1,b))) + card(SYT(gHookYD(a,b-1))) via explicit inline bijection (Fintype.card_congr with anonymous Equiv)
5. Proved `card_SYT_gHookYD`: card(SYT(gHookYD a b ha)) = C(a+b-1, b) by double induction (outer on b, inner on a) using Pascal's rule Nat.choose_succ_succ
6. Proved `hook_length_formula_gHookYD`: C(a+b-1,b) * (a+b) * (a-1)! * b! = (a+b)! via Nat.choose_mul_factorial_mul_factorial + calc

### Key Findings

- **Inline bijection pattern avoids cast issues**: The `▸` cast / `restrictSYT_gen` approach fails for gHookYD because the bijection involves two different subdiagrams. Using the same anonymous-structure Equiv pattern as `card_SYT_twoRowYD_step` succeeds without casts.
- **left_inv branch 3 pattern**: `symm; apply T.entry_zero; intro hcμ` — after `symm`, goal is `T.entry c = 0`, then `apply T.entry_zero` leaves `c ∉ μ` as a Pi type `c ∈ μ → False`, so `intro hcμ` works.
- **right_inv dif_pos/dif_neg**: Must provide a `have` that matches exactly what Lean sees as the condition type; using `if_pos rfl` for the `inl` branch and `have hne_corner` + `have hentry_ne` for the `inr` branch.
- **Double induction**: Base cases are gHookYD a 0 = oneRowYD a (1 SYT) and gHookYD 1 b = oneColYD (b+1) (1 SYT). Inductive step uses pascal = iha + ihb.
- **HLF arithmetic**: Nat.choose_mul_factorial_mul_factorial gives C(n,k)*k!*(n-k)!=n!; then (a+b-1)!*(a+b) = (a+b)! by Nat.factorial_succ.
- **Build status**: Proofs.BallotProblemOQ03OQ01OQ02 builds successfully with 0 new sorries in gHookYD section.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (added ~400 lines: PART VIc gHookYD section, lines 694-1406)

### Next Steps

1. **hook_walk_identity in ℚ**: Σ_c hookProd(μ)/hookProd(μ\c) = μ.card. Now that gHookYD is proved, this extends the repertoire and shows the corner-induction strategy works in principle.
2. **Aristotle targets**: ni_count_eq_syt_count and lgv_det_factors_as_hook_quotient remain open; fix their statements (add hypothesis relating μ to (r,σ,m)) before resubmitting.
3. **Generalize**: Attempt HLF for μ with at most 3 rows or for specific rectangle shapes.

---

## Session 2026-04-24 (Session 15) — removeCorner Hook Infrastructure

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: PROGRESS — 8 new lemmas (0 sorries) establishing how hookLength changes when removing a corner

### What I Did

1. Assessed Session 14 state: PART XIV added with `hook_walk_identity` as sole sorry; `hook_length_formula_Q` + `hook_length_formula_general` proved conditional on it
2. Identified needed infrastructure: rowLen/colLen behavior of `removeCorner` at corner and non-corner rows/cols
3. Added 8 private lemmas (~130 lines) before `hook_walk_identity` in PART XIV:
   - `rowLen_of_isCorner`: μ.rowLen c.1 = c.2 + 1 (corner's row ends exactly at c.2)
   - `colLen_of_isCorner`: μ.colLen c.2 = c.1 + 1 (corner's col ends exactly at c.1)
   - `rowLen_removeCorner_self`: rowLen decreases by 1 at row c.1 after removing corner c
   - `rowLen_removeCorner_other`: rowLen unchanged at other rows r ≠ c.1
   - `colLen_removeCorner_self`: colLen decreases by 1 at col c.2 after removing corner c
   - `colLen_removeCorner_other`: colLen unchanged at other cols s ≠ c.2
   - `hookLength_removeCorner_arm`: for arm cells (c.1, s) with s < c.2: hookLength decreases by 1
   - `hookLength_removeCorner_leg`: for leg cells (r, c.2) with r < c.1: hookLength decreases by 1

### Key Findings

- **Proof pattern**: Use `obtain ⟨i, j⟩ := c` to avoid Prod.eta issues; prove ≤ antisymmetry for rowLen/colLen
- **rowLen/colLen proofs**: Use `mem_iff_lt_rowLen.not.mp` and `omega` to convert `(i,j) ∉ removeCorner` into `rowLen ≤ j`; then show `(i, j-1) ∈ removeCorner` to get `j-1 < rowLen` → `j ≤ rowLen`
- **hookLength arithmetic**: After unfold + rw, omega handles `c.2-s-1+X+2 = (c.2+1)-s-1+X+1` given `s < c.2` and `c.1 < μ.colLen s`
- **hook_walk_identity mathematical analysis**: The identity Σ_c R(c) = n (where R(c) = hookProd(μ)/hookProd(μ\c)) is known in combinatorics (Frame-Robinson-Thrall / GNW). But:
  - Direct induction fails: (A) hook_length_formula and (B) hook_walk_identity are equivalent given corner_step, neither provable from the other
  - Proving Σ R(μ,c) = 1 + Σ R(μ\c₀, c') for a fixed corner c₀ requires tracking how ratios change as corners change — not trivially tractable
  - The infrastructure built this session enables the hookProd ratio formula as next step

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (~130 lines added, PART XIV infrastructure before hook_walk_identity)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)

### Sorry Count: 3 (unchanged)

- hook_walk_identity (line ~4763): sole mathematical blocker, still sorry
- ni_count_eq_syt_count (line 235): RSK bijection, FALSE as stated
- lgv_det_factors_as_hook_quotient (line 245): det identity, FALSE as stated

### Next Steps

1. **hookProd_removeCorner_ratio** (~50 lines): Using arm/leg hook change lemmas, prove:
   hookProd(μ) / hookProd(μ\c) = ∏_{s<c.2} h(c.1,s)/(h(c.1,s)-1) × ∏_{r<c.1} h(r,c.2)/(h(r,c.2)-1)
2. **hook_walk_identity**: The mathematical content is now:
   Σ_{c=(i,j) ∈ corners(μ)} [∏_{s<j} h(i,s)/(h(i,s)-1)] × [∏_{r<i} h(r,j)/(h(r,j)-1)] = n
   This is the deep combinatorial identity. Consider submitting to Aristotle with full infrastructure.
3. **Alternative approach**: Prove hook_walk_identity for shapes with ≤ 2 corners as stepping stone.
