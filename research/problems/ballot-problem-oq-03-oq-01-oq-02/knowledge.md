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
1. `ni_count_eq_syt_count` — RSK/Fomin growth diagram bijection: SYT(μ) ↔ NI-paths
2. `lgv_det_factors_as_hook_quotient` — det × hookProd = n! (Vandermonde-type identity)
3. `hook_length_formula` — general case (reduces to above two)

---

## Session 2026-04-21 (Session 2) - Fintype Instance + Single-Row Cases

**Mode**: FRESH
**Outcome**: progress — built full infrastructure, proved formula for empty and single-row shapes

### What I Did

1. Read `BallotProblemOQ03OQ02.lean` — confirmed `lgv_lemma_rxr` signature:
   `(niTupleCount cfg : ℤ) = (pathMatrix cfg).det`
2. Defined `hookLength`, `hookProd`, `StandardYoungTableau` structure in full
3. Added `instFintypeSYT` (Fintype instance) via injection into `({c ∈ μ} → Fin (|μ|+1))`
4. Proved `hook_length_formula_bot` (empty case: 1 × 1 = 0!)
5. Proved `hookProd_singleRow`: for single-row μ, hookProd = μ.card!
6. Proved `card_syt_singleRow`: unique SYT of any single-row shape
7. Proved `hook_length_formula_singleRow`: formula holds for all single-row shapes
8. Defined `youngLGVConfig`: encodes partition σ (weakly increasing) as LGV problem
9. Added corrected auxiliary theorem statements with explicit μ-σ connection hypotheses
10. Added 8 numerical norm_num verifications for specific shapes

### Key Findings

**Critical gap found and fixed**: `Fintype.card (StandardYoungTableau μ)` did not typecheck
without a `Fintype` instance. `StandardYoungTableau μ` has `entry : ℕ × ℕ → ℕ` (infinite domain),
so no auto-derivation. Fixed by injecting into `{c ∈ μ} → Fin (|μ|+1)`.

**Injection key insight**: Entries outside μ are forced to 0 (entry_zero); entries inside μ
are in {1,...,|μ|} (entry_range). So entries inside μ land in Fin(|μ|+1). Since μ.cells is
a Finset, the function type `{c ∈ μ} → Fin(|μ|+1)` is finite by `Pi.fintype`.

**Single-row uniqueness**: In any SYT of a single-row shape, `entry(0,j) = j+1` is forced:
- Lower bound: entry(0,j) ≥ j+1 by induction + row_strict
- Upper bound: iterated row_strict gives `entry(0,j) + k < entry(0,j+k+1)`, combined with
  entry_range bound `entry(0,last) ≤ n` forces entry(0,j) ≤ j+1.

**Descending product identity** (proved): `∏ j ∈ range n, (n-j) = n!`
Proof uses `Finset.prod_range_succ'` (line 541 of Mathlib's Basic.lean) to peel off j=0 factor.

**Statement bug found**: `ni_count_eq_syt_count` and `lgv_det_factors_as_hook_quotient` had
μ and σ as independent parameters (no connection). Fixed with `_correct` variants adding:
  - `hrows : ∀ i : Fin r, μ.rowLen i.val = σ ⟨r - 1 - i.val, ...⟩`
  - `hextra : ∀ i : ℕ, r ≤ i → μ.rowLen i = 0`

**colLen 0 ≤ 1 as single-row predicate**: `colLen 0` = number of non-empty rows.
When ≤ 1, all cells have row index 0 (proved via colLen_anti: colLen j ≤ colLen 0 ≤ 1).

### Proof Architecture

```
BallotProblemOQ03OQ01OQ02.lean (535 lines, 3 sorries)

PART I: Hook Length
  hookLength μ i j = armLen μ i j + legLen μ i j + 1    [def]
  hookLength_pos, hookLength_add_eq                       [proved]

PART II: Hook Product
  hookProd μ = ∏ c ∈ μ.cells, hookLength μ c.1 c.2      [def]
  hookProd_pos, hookProd_empty                            [proved]

PART IIIb: Fintype Instance
  instFintypeSYT: Fintype (StandardYoungTableau μ)       [proved]

PART IIIc: Empty Case
  hook_length_formula_bot: ⊥ case                        [proved]

IIId-g: Single-Row Cases
  hookProd_singleRow (h : colLen 0 ≤ 1)                  [proved]
  card_syt_singleRow (h : colLen 0 ≤ 1)                  [proved]
  hook_length_formula_singleRow                           [proved]

PART IV: LGV Configuration
  youngLGVConfig r σ hσ m hm                             [def, proved]
  youngLGVConfig_wellFormed                               [proved]

PART V: Main Theorem
  hook_length_formula (general)                           [sorry]
  ni_count_eq_syt_count_correct                          [sorry, OPEN]
  lgv_det_eq_syt_times_hookProd_correct                  [sorry, OPEN]

PART VI: Numerical Verifications
  8 norm_num examples for specific shapes                 [proved]
```

### Remaining Sorries Assessment

**`ni_count_eq_syt_count_correct`** (RSK bijection):
- Needs Fomin growth diagram or jeu de taquin
- Maps SYT(λ) ↔ NI-lattice paths via insertion/recording tableau
- Estimated: 200-300 lines of Lean bijection code
- Status: OPEN (requires new formalization)

**`lgv_det_eq_syt_times_hookProd_correct`** (det factorization):
- hookProd(μ) × det[C(m+σⱼ+j-i, m)] = n! where n = ∑σᵢ
- Classical proof via Weyl denominator formula / hook-content formula
- Estimated: 200-300 lines of algebraic manipulation
- Status: OPEN (requires new formalization)

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (new, 535 lines, 3 sorries)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md`
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`

### Next Steps

1. **Submit `ni_count_eq_syt_count_correct` to Aristotle** — OPEN, manual work needed
2. **Prove `lgv_det_eq_syt_times_hookProd_correct`** — may start with 2-column case
3. **Add encoding lemma**: extract (r, σ, m) from μ to close `hook_length_formula`
4. **Consider induction on r** (number of rows) as an intermediate strategy

---

## Session 2026-04-21 (Session 1) - Foundation and Logical Chain

**Mode**: FRESH (MODERATE knowledge tier, score 9)
**Outcome**: progress — added Fintype instance, base case, and conditional chain proof

### Key Findings

- `Fintype.card (StandardYoungTableau μ)` required a Fintype instance not in Mathlib
- Fixed `lgv_det_factors_as_hook_quotient` from `det = n!/hookProd` to `det * hookProd = n!`
- Added `hook_length_formula_from_chain` — proves main theorem from two sorry lemmas

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean`
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md`
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`

---

## Dead Ends

- `lgv_det_factors_as_hook_quotient` with `=` and integer division `/` (reformulated to `*`)
- `deriving Fintype` on StandardYoungTableau (impossible: infinite function field `entry : ℕ × ℕ → ℕ`)
- `induction c.2 with` on a fixed pair in card_syt_singleRow (Lean 4 needs universally quantified var)
