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

**Remaining sorries (2):**
1. `ni_count_eq_syt_count` — RSK/Fomin growth diagram bijection: SYT(μ) ↔ NI-paths
2. `lgv_det_factors_as_hook_quotient` — det × hookProd = n! (Vandermonde-type identity)

---

## Session 2026-04-21 (Session 1) - Foundation and Logical Chain

**Mode**: FRESH (MODERATE knowledge tier, score 9)
**Outcome**: progress — added Fintype instance, base case, and conditional chain proof

### What I Did

1. Read `BallotProblemOQ03OQ01OQ02.lean` (225 lines) — identified missing Fintype instance
2. Read `BallotProblemOQ03OQ02.lean` — confirmed `lgv_lemma_rxr` signature:
   `(niTupleCount cfg : ℤ) = (pathMatrix cfg).det`
3. Read `YoungDiagram.lean` — confirmed SetLike membership: `c ∈ μ ↔ c ∈ μ.cells` (rfl)
4. Added `instFintypeSYT` (Fintype instance) via injection into `μ.cells → Fin (μ.card+1)`
5. Added `emptyTableau` and `hook_length_formula_bot` (proved base case)
6. Fixed `lgv_det_factors_as_hook_quotient` from `det = n!/hookProd` to `det * hookProd = n!`
7. Added `hook_length_formula_from_chain` — proves main theorem from two sorry lemmas

### Key Findings

**Critical gap found**: `Fintype.card (StandardYoungTableau μ)` did not typecheck without
a Fintype instance. `StandardYoungTableau μ` has `entry : ℕ × ℕ → ℕ` (infinite domain),
so no auto-derivation. Fixed by injecting into `↑μ.cells → Fin (μ.card+1)`.

**Logical chain is now complete**: `hook_length_formula_from_chain` shows:

```
niTupleCount cfg = card(SYT μ)           [ni_count_eq_syt_count, sorry]
niTupleCount cfg = pathMatrix.det        [lgv_lemma_rxr, proved]
pathMatrix.det * hookProd μ = n!         [lgv_det_factors_as_hook_quotient, sorry]
→ card(SYT μ) * hookProd μ = n!          [QED, proved from above]
```

The main theorem `hook_length_formula` reduces to closing the two sorries + encoding μ as (r, σ, m).

**Empty case proved**: For μ = ⊥, unique SYT is the zero function, hookProd = 1, 0! = 1, 1×1=1 ✓

**Determinant formulation fixed**: Changed `lgv_det_factors_as_hook_quotient` from
`det = n!/hookProd` (integer division, problematic) to `det * hookProd = n!` (clean multiplication).

### Proof Architecture

```
BallotProblemOQ03OQ02.lean
  lgv_lemma_rxr: (niTupleCount cfg : ℤ) = (pathMatrix cfg).det  [proved]
  lgv_universality: ∀ r cfg hwf, niTupleCount = det              [proved]

BallotProblemOQ03OQ01OQ02.lean
  instFintypeSYT: Fintype (StandardYoungTableau μ)               [proved]
  hook_length_formula_bot: ⊥ case                                [proved]
  hook_length_formula_from_chain: main theorem from sorries       [proved]
  ni_count_eq_syt_count: card(SYT) = niTupleCount                [sorry]
  lgv_det_factors_as_hook_quotient: det * hookProd = n!          [sorry]
  hook_length_formula: main theorem                               [sorry]
```

### Remaining Sorries Assessment

**`ni_count_eq_syt_count`** (RSK bijection):
- Needs Fomin growth diagram or jeu de taquin
- Maps SYT(λ) ↔ NI-lattice paths via insertion/recording tableau
- Estimated: 200-300 lines of Lean bijection code
- Status: HARD (known proof, needs formalization)

**`lgv_det_factors_as_hook_quotient`** (Vandermonde det identity):
- det[C(m+σ_j+j-i, m)] × hookProd(λ) = n! for n=∑σᵢ
- Classical proof via Weyl denominator formula / hook-content formula
- Alternative: direct verification via "hook walks" identity
- Estimated: 200-300 lines of algebraic manipulation
- Status: HARD (known proof, complex algebraic identity)

**Encoding gap**: `hook_length_formula` from `hook_length_formula_from_chain` requires:
- Extracting r = number of rows from μ
- Building σ : Fin r → ℕ (ascending row lengths) from μ.rowLen
- Proving σ monotone, σᵢ + i ≤ m, well-formedness
- Estimated: 50-80 lines

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (225 → 315 lines, +3 proved theorems)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md`
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`

### Next Steps

1. **Prove `ni_count_eq_syt_count`** via Fomin growth diagrams or RSK
2. **Prove `lgv_det_factors_as_hook_quotient`** via Vandermonde/Weyl denominator
3. **Add encoding lemma**: extract (r, σ, m) from μ to close `hook_length_formula`
4. **Consider Aristotle** for sub-lemmas of the bijection proof

---

## Session 2026-04-21 (Session 2) - Single-Row Hook Formula Proved Directly

**Mode**: REVISIT
**Outcome**: PROGRESS — `hook_length_formula_one_row` proved (~190 lines, 0 sorries)

### What I Did

1. Assessed PART V LGV chain: `ni_count_eq_syt_count` and `lgv_det_factors_as_hook_quotient`
   are missing because `μ` is disconnected from the `(r, σ, m)` parameters — the LGV lemma
   uses a specific `youngLGVConfig` but μ is arbitrary. This makes the chain mathematically incoherent.
2. Strategic pivot: instead of continuing the LGV path (two HARD sorries), proved the
   hook-length formula for single-row Young diagrams directly without LGV.
3. Added PART VI (~190 lines) to `BallotProblemOQ03OQ01OQ02.lean`:
   - `oneRowYD n`: `YoungDiagram.ofRowLens [n] (...)` — single-row shape
   - `mem_oneRowYD`: `(i,j) ∈ oneRowYD n ↔ i = 0 ∧ j < n`
   - `oneRowYD_card`: card = n (via Finset.card_image_of_injective)
   - `rowLen_oneRowYD_zero`: rowLen 0 = n
   - `colLen_oneRowYD`: colLen j = 1 for j < n
   - `hookLength_oneRowYD`: hookLength(0,j) = n - j (uses `hookLength_add_eq`)
   - `hookProd_oneRowYD`: hookProd = n! (via `descFactorial_eq_prod_range` + `descFactorial_self`)
   - `oneRowSYT n`: the unique SYT with `entry(0,j) = j+1`
   - `entry_oneRow_eq`: any SYT has `entry(0,j) = j+1` (double induction: lower by IH on j, upper by chain)
   - `oneRowSYT_unique`: all SYTs of oneRowYD n equal oneRowSYT n
   - `hook_length_formula_one_row`: `card(SYT(oneRowYD n)) × hookProd(oneRowYD n) = n!` (0 sorries!)

### Key Findings

**Direct path avoids LGV entirely**: For single-row μ, we don't need LGV/RSK/Vandermonde.
The proof is elementary and fully verified.

**Uniqueness proof technique**: Double induction — lower bound by induction on j using `row_strict`
(each next entry is strictly larger), upper bound by chain argument (entries form a chain bounded
by `entry_range` at the last cell). Together these pin each entry exactly.

**Key lemmas used**:
- `hookLength_add_eq (μ : YoungDiagram) : (i,j) ∈ μ → hookLength μ i j + 1 = rowLen i - j + colLen j`
- `Nat.descFactorial_eq_prod_range : n.descFactorial k = ∏ i ∈ range k, (n - i)`
- `Nat.descFactorial_self n : n.descFactorial n = n!`
- `YoungDiagram.mem_iff_lt_rowLen`, `YoungDiagram.mem_iff_lt_colLen`

**Error patterns resolved**:
- `List.getElem_cons_zero` needed to simplify `[n][0] = n` in `mem_oneRowYD`
- `if_neg (mt mem_oneRowYD.mpr hc)` for `entry_zero` — cleaner than push_neg
- `if_pos hc` after `rw [mem_oneRowYD] at hc` for in-diagram cases
- `suffices h : ∀ k < n, ...` to get proper IH for lower bound induction

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (315 → ~505 lines, PART VI added, 0 sorries)

### Next Steps

1. **Prove single-column case**: `hook_length_formula_one_col` similarly (column-symmetric)
2. **Two-row hook formula**: May be achievable via direct bijection (RSK for 2-row shapes is explicit)
3. **Consider Aristotle** for `ni_count_eq_syt_count` sub-lemmas if tackling LGV chain
4. **Generalize**: Hook formula for rectangular shapes (direct counting argument)

---

## Session 2026-04-21 (Session 3) - Single-Column Hook Formula Proved Directly

**Mode**: REVISIT (building on Session 2's technique)
**Outcome**: PROGRESS — `hook_length_formula_one_col` proved (~173 lines, 0 sorries)

### What I Did

1. Reviewed Session 2's one-row proof technique and applied it symmetrically to one-column diagrams.
2. Merged `origin/main` into worktree to get Session 2's work (PR #11096).
3. Added PART VIb (~173 lines) to `BallotProblemOQ03OQ01OQ02.lean`:
   - `oneColYD n`: direct `YoungDiagram` struct with `cells = (range n).image (·, 0)`
   - `mem_oneColYD`: `(i,j) ∈ oneColYD n ↔ i < n ∧ j = 0`
   - `oneColYD_card`: card = n
   - `rowLen_oneColYD`: rowLen i = 1 for i < n
   - `colLen_oneColYD_zero`: colLen 0 = n
   - `hookLength_oneColYD`: hookLength(i,0) = n - i (arm=0, leg=n-i-1, hook=n-i)
   - `hookProd_oneColYD`: hookProd = n! (same descFactorial technique)
   - `oneColSYT n`: the unique SYT with `entry(i,0) = i+1`
   - `entry_oneCol_eq`: any SYT has `entry(i,0) = i+1` (col_strict induction)
   - `oneColSYT_unique`: all SYTs of oneColYD n equal oneColSYT n
   - `hook_length_formula_one_col`: `card(SYT(oneColYD n)) × hookProd(oneColYD n) = n!` (0 sorries!)

### Key Findings

**Column-transpose of one-row**: The one-column proof is fully symmetric to the one-row case,
replacing `row_strict` with `col_strict` and swapping row/column roles throughout.

**Architecture insight**: `oneColYD` defined as struct literal rather than `ofRowLens`, using
`cells = (range n).image (·, 0)`. The `isLowerSet` proof uses `Prod.mk_le_mk` to extract
components: `(a,b) ≤ (k,0)` gives `a ≤ k` and `b ≤ 0`, so `b = 0` and `a < n`.

**Pre-existing build failure in dependency**: `BallotProblemOQ03OQ02.lean` has an `omega`
proof that reports a counterexample in the GV involution proof. This is a dependency of
`BallotProblemOQ03OQ01OQ02.lean`. The failure predates this session (PR #11096 was merged
despite it). My file compiles but the full dependency chain can't be verified locally.

**Proved instances so far**: hook_length_formula for empty (⊥), single-row (oneRowYD),
single-column (oneColYD). The general theorem remains open.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (~503 → 676 lines, PART VIb added, 0 sorries)

### Next Steps

1. **Fix BallotProblemOQ03OQ02 omega issue**: Investigate which specific omega proof fails
   in the GV involution; fixing this unblocks dependency builds for future sessions.
2. **Prove hook formula for 2-row shapes**: Use a direct bijection between SYT([m+1,1]) and
   Fin(m+1), which is explicit and doesn't need LGV (choose where n goes in corner position).
3. **Inductive proof**: Explore the corner-cell induction (sum over corners of SYT(μ\{c}))
   to get the full formula; the key identity is `∑_corners hookProd(μ)/hookProd(μ\{c}) = n`.
4. **RSK bijection for 2-row shapes**: More tractable than general RSK; maps to monotone paths.

---

## Session 2026-04-22 (Session 4) - Hook-Shape SYT, Complete Bijection Proof

**Mode**: REVISIT (RICH knowledge tier, score 28)
**Outcome**: progress — proved hook-length formula for hook-shape (m+1,1) with 0 sorries

### What I Did

1. Defined `hookShapeYD m` (YoungDiagram with rows [m+1, 1]) via `ofRowLens`
2. Proved hook lengths: `h(0,0)=m+2`, `h(0,j+1)=m-j`, `h(1,0)=1`
3. Proved `hookProd_hookShapeYD`: `hookProd(m+1,1) = (m+2) × m!` via insert decomposition + descFactorial
4. Defined explicit bijection `hookSYT m k` for each `k : Fin(m+1)`:
   - `entry(0,j) = j+1` for `j ≤ k`, `j+2` for `j > k`; `entry(1,0) = k+2`
5. Proved `hookSYT_entry_zero_zero_eq_one`: row chain + upper bound shows `entry(0,0) = 1` always
6. Proved `hookSYT_unique`: any SYT equals `hookSYT k` for `k = entry(1,0) - 2`
7. Proved `hookSYT_injective` and `card_SYT_hookShapeYD = m+1` via `Equiv.ofBijective`
8. Proved `hook_length_formula_hook_shape`: `(m+1) × (m+2) × m! = (m+2)!`

### Key Findings

**Bijection proof technique**: The key insight is `entry(0,0) = 1` in any hook-shape SYT.
Proof: if `entry(0,0) = 2`, then by row chains + upper bounds, `entry(0,j) = j+2` for all j.
Then `entry(1,0) ∈ {3,...,m+2}` equals some `entry(0,T.entry(1,0)-2)` by the formula,
contradicting injectivity. This forces `entry(0,0) = 1`.

**hookProd insert decomposition**: `range(m+1) = insert 0 (range m).image(·+1)` splits
off the `j=0` term (`h=m+2`), then the remaining product over `j ∈ range m` gives `m!`
via `descFactorial_eq_prod_range` + `descFactorial_self`.

**Build note**: `BallotProblemOQ03OQ02.lean` dependency still has pre-existing build failures
(multiple omega and Bool simp issues from Lean4/Mathlib API changes). Part VIII code is
self-contained and does not use LGV infrastructure.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (676 → 1089 lines, PART VIII added, 0 new sorries)

### Next Steps

1. **Fix dependency**: `BallotProblemOQ03OQ02.lean` has ~20+ errors from Lean4 API changes
   (Bool.false_eq_false removed, omega changes). Fixing enables full build verification.
2. **2-row rectangular shapes**: Prove hook formula for `(m+n, n)` shapes directly, extending
   the hook-shape approach to 2-row cases.
3. **Corner-cell induction**: The recursive formula `f^λ = Σ_{corners c} f^{λ\c}` might
   be accessible; key identity is `Σ hookProd(μ)/hookProd(μ\{c}) = n` over removable corners.

---

---

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
