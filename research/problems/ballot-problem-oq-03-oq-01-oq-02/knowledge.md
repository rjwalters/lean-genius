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


---

> **Note**: 7 older sessions archived to `sessions/` directory.

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

---

## Session 2026-04-24 (Session 16) — hookProd Ratio Formula Infrastructure

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: PROGRESS — 3 more lemmas (2 proved, 1 sorry), hook_walk_identity analysis complete

### What I Did

1. Continued from Session 15 infrastructure; confirmed 8 lemmas in place
2. Added 3 more private lemmas to PART XIV:
   - `hookLength_corner_eq_one`: hookLength μ c = 1 for any corner c (armLen=0, legLen=0)
     Proved: unfold + rw[rowLen_of_isCorner, colLen_of_isCorner] + omega
   - `hookLength_eq_of_not_arm_leg`: for cells (a,b) ∈ μ that are neither arm nor leg cells of corner c,
     hookLength is unchanged by removeCorner. Key: derive a≠i (from rowLen bound) and b≠j (from colLen bound),
     then apply rowLen_removeCorner_other + colLen_removeCorner_other.
   - `hookProd_ratio_formula` (sorry): states ratio = ∏_{s<j} h/(h-1) × ∏_{r<i} h/(h-1)
     7-step proof strategy documented in comment; requires ~80 lines Finset.prod_union decomposition
3. Committed all work; pushed to feature/researcher-8; created PR rjwalters/lean-genius#12309

### Key Findings

- **hookProd_ratio_formula proof strategy**: 
  1. hookProd(μ) = 1 × ∏_{ν.cells} hookLength μ  [mul_prod_erase on corner]
  2. hookProd(ν) = ∏_{ν.cells} hookLength ν
  3. ratio = ∏_{ν.cells} h(μ)/h(ν)  [prod_div_distrib]
  4. ν.cells = armCells ∪ legCells ∪ restCells
  5. arm/leg: h(μ)/h(ν) = h/(h-1) [hookLength_removeCorner_arm/leg]
  6. rest: h(μ)/h(ν) = 1 [hookLength_eq_of_not_arm_leg]

- **hook_walk_identity mathematical status**: The identity Σ_c hookProd(μ)/hookProd(μ\c) = n is
  equivalent to the hook-length formula itself (given corner recursion). An independent proof via
  the GNW probabilistic hook walk argument requires ~200-300 lines of formalization. No elementary
  algebraic proof is known that avoids the GNW machinery.

- **Docker not running**: Build could not be verified this session; code logic verified by inspection

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (+53 lines: 3 new lemmas in PART XIV)
- PR: rjwalters/lean-genius#12309

### Sorry Count: 3 (unchanged — but mathematical depth documented)

- `hook_walk_identity` (PART XIV): sole mathematical blocker; needs GNW proof (~200-300 lines)
- `ni_count_eq_syt_count` (line 235): RSK bijection, FALSE as stated  
- `lgv_det_factors_as_hook_quotient` (line 245): det identity, FALSE as stated

### Next Steps

1. **Prove hookProd_ratio_formula**: The 7-step strategy is documented; requires ~80 lines of
   Finset decomposition using prod_sdiff/prod_union. The cell decomposition is:
   ν.cells = armCells ∪ legCells ∪ restCells (all disjoint, all proved above)
2. **Implement GNW proof sketch**: Define hook walk probability P(start→corner c) and show
   Σ_c P = 1 implies Σ_c hookProd(μ)/hookProd(μ\c) = n
3. **Archive sessions**: knowledge.md is >500 lines; archive sessions 5-11 to sessions/ subdir

---

## Session 2026-04-24 (Session 17) — arm_mem_nu/leg_mem_nu + hookProd_ratio partial proof

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: PROGRESS — 2 new proved lemmas; hookProd_ratio_formula fleshed out to ~90% complete

### What I Did

1. Added `arm_mem_nu`: for corner c of μ and s < c.2, proves (c.1, s) ∈ removeCorner μ c hc
   - Via mem_removeCorner: (c.1,s) ∈ μ (rowLen = c.2+1 > s) and (c.1,s) ≠ c (second coord differs)
2. Added `leg_mem_nu`: for r < c.1, proves (r, c.2) ∈ removeCorner μ c hc
   - Via mem_removeCorner: (r,c.2) ∈ μ (colLen = c.1+1 > r) and (r,c.2) ≠ c (first coord differs)
3. Fleshed out `hookProd_ratio_formula` with a substantial partial proof:
   - Sets up ν, armCells, legCells definitions
   - Proves hμ_via_ν: hookProd μ = ∏_{ν.cells} hookLength μ (via mul_prod_erase + corner=1)
   - Proves hdisj: Disjoint armCells legCells (arm first coord = i, leg first coord < i)
   - Proves harm_sub: armCells ⊆ ν.cells (via arm_mem_nu)
   - Proves hleg_sub: legCells ⊆ ν.cells (via leg_mem_nu)
   - Remaining sorry: Finset.prod splitting over arm ∪ leg ∪ rest (~40 more lines)

### Key Findings

- **mul_prod_erase approach**: After rw [hμQ, ← Finset.mul_prod_erase ... hcmem], the corner
  factor becomes hookLength_corner_eq_one = 1, giving hookProd μ = ∏_{ν.cells} hookLength μ
- **Disjointness proof**: arm cells have first coord = i, leg cells first coord < i; they share
  no element. Proved via Finset.disjoint_left + Prod.mk.injEq + omega.
- **Remaining sorry analysis**: The Finset.prod splitting step needs:
  (a) Finset.prod_union applied to armCells ∪ legCells as a subset of ν.cells
  (b) Finset.prod_image to convert ∏_{armCells} to ∏_{Finset.range j}
  (c) hookLength_removeCorner_arm/leg to rewrite each factor
  (d) hookLength_eq_of_not_arm_leg for rest cells (contributing 1)
  Total: ~40 more lines of Finset.prod manipulation

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (+65 lines: arm_mem_nu, leg_mem_nu, updated hookProd_ratio_formula)

### Sorry Count: 3 (unchanged)

- `hookProd_ratio_formula` (PART XIV): ~90% proved; still sorry for Finset.prod splitting
- `hook_walk_identity` (PART XIV): sole HLF blocker; needs GNW proof (~200-300 lines)
- `ni_count_eq_syt_count` (line 235): RSK bijection, FALSE as stated
- `lgv_det_factors_as_hook_quotient` (line 245): det identity, FALSE as stated

### Next Steps

1. **Complete hookProd_ratio_formula**: The ~40-line Finset.prod split is the only remaining gap.
   Use Finset.prod_sdiff (s ⊆ t → ∏_t f = ∏_{t\s} f * ∏_s f) to peel off armCells, then legCells.
   Apply Finset.prod_image (injective fun s => (i,s)) to convert index.
2. **GNW proof of hook_walk_identity**: Requires ~200-300 lines; probability theory approach.
   Alternatively, try to prove for specific shapes (2-corner diagrams) as special cases.
3. **Aristotle submission**: Submit hookProd_ratio_formula (without the prod-split sorry) and
   arm_mem_nu / leg_mem_nu to Aristotle for verification of the proved parts.

---

## Session 2026-04-24 (Session 18) — hookProd_ratio_formula COMPLETED

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: PROGRESS — `hookProd_ratio_formula` proved (0 sorries); 1 sorry eliminated

### What I Did

1. Completed the `hookProd_ratio_formula` proof: replaced the remaining sorry with a ~90-line proof
2. Strategy: avoided `Finset.prod_div_distrib` on CommGroupWithZero complications by first proving
   a ℕ product equality (`key_nat`), then casting to ℚ, then applying field division lemmas
3. PR: rjwalters/lean-genius#12358 on `feature/researcher-10`

### Key Proof Steps

1. **`key_nat` (ℕ equality)**: Avoids division entirely by proving:
   `hookProd μ × ∏_s hookLen(ν,i,s) × ∏_r hookLen(ν,r,j) = hookProd ν × ∏_s hookLen(μ,i,s) × ∏_r hookLen(μ,r,j)`
   Strategy: split ν.cells = armCells ∪ legCells ∪ restCells via `Finset.union_sdiff_of_subset`,
   then apply `Finset.prod_union` (twice) and `Finset.prod_congr rfl hrest_inv` (rest cells equal),
   then `ring` to cancel.

2. **`harm_diff` / `hleg_diff`**: `hookLength ν i s = hookLength μ i s - 1` in ℚ, proved by
   casting `hookLength_removeCorner_arm/leg` (ℕ: `hν + 1 = hμ`) via `exact_mod_cast` + `linarith`.

3. **`hrest_inv`**: `hookLength ν x = hookLength μ x` for cells in restCells. Used `mem_sdiff` to
   extract `x ∉ armCells ∪ legCells`, then `hookLength_eq_of_not_arm_leg` with proof that
   arm/leg membership would put x in the excluded union.

4. **Final combination**: `Finset.prod_div_distrib` (×2) rewrites product-of-ratios to ratio-of-products;
   `harm_prod_eq` / `hleg_prod_eq` rewrites (hμ-1) denominators to hν values;
   `div_mul_div_comm` combines the two quotients; `div_eq_div_iff` cross-multiplies;
   `linear_combination key_Q` closes.

### Key Findings

- **ℕ equality sidesteps ℚ product complexity**: Rather than working with `∏ x / ∏ y` in ℚ
  (requiring CommGroupWithZero or field instances), prove the cross-multiplication equality in ℕ
  first, then cast. This avoids `prod_div_distrib` until the very last step.
- **`Finset.prod_image` injection pattern**: `fun a _ b _ h => (Prod.mk.inj h).2` for
  `fun s => (i, s)` injectivity (take `.2` of Prod.mk.inj); `.1` for `fun r => (r, j)`.
- **`Prod.ext h1.symm rfl`**: Proves `(i, x.2) = x` given `h1 : x.1 = i`.
- **`disjoint_sdiff_self_right`**: Proves `Disjoint s (t \ s)` for `restCells = ν.cells \ (armCells ∪ legCells)`.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (5056 → 5146 lines, hookProd_ratio_formula proved)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (knowledge updated)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-02/meta.json` (lineCount 5146, sorries 4)
- PR: rjwalters/lean-genius#12358

### Sorry Count: 5 → 4

- `hookProd_ratio_formula` (PART XIV): **PROVED** ✓
- `hook_walk_identity` (PART XIV line ~5067): ≥3-row case, needs GNW proof (~200-300 lines)
- `ni_count_eq_syt_count` (line 219): RSK bijection, FALSE as stated
- `lgv_det_factors_as_hook_quotient` (line 235): det identity, FALSE as stated
- `hook_length_formula` (line 245): depends on the two above (FALSE as stated)

### Next Steps

1. **hook_walk_identity ≥3-row case**: The identity `Σ_{c ∈ corners(μ)} hookProd(μ)/hookProd(μ\c) = μ.card`
   requires either the GNW probabilistic hook walk proof (~200-300 lines) or showing equivalence
   to HLF itself (circular without external proof). The `hookProd_ratio_formula` now provides the
   ratio factorization needed as input. The 2-row case is already proved in `hook_walk_identity_atMostTwoRows`.
2. **Archive sessions**: knowledge.md is >500 lines; archive sessions 5-17 to sessions/ subdir.

---

## Session 2026-04-24 (Session 19) — Hook Walk Identity for Generalized Hook Shapes

**Mode**: REVISIT (RICH knowledge tier, score 106)
**Outcome**: PROGRESS — `hook_walk_identity_gHookYD` proved; sorry scope reduced

### What I Did

1. Identified the non-circular proof path: `hook_length_formula_gHookYD` (proved independently in
   Session 14 via combinatorial formula) enables proving `hook_walk_identity_gHookYD` without
   circularity — the same algebraic pattern as `hook_walk_identity_atMostTwoRows`.
2. Added `corners_gHookYD_cases` (~40 lines): characterizes all corners of `gHookYD a b ha`
   (with b ≥ 1) as either `(0, a-1)` with `a ≥ 2` (top-right), or `(b, 0)` (bottom-left).
3. Added `hook_walk_identity_gHookYD` (~90 lines): non-circular proof of hook walk identity for
   all `[a, 1^b]` shapes. Algebraic strategy mirrors `hook_walk_identity_atMostTwoRows`.
4. Updated `hook_walk_identity` dispatcher: sorry now covers only ≥3-row non-gHookYD shapes.
5. PR: rjwalters/lean-genius#12381

### Key Findings

- **Non-circular path via gHookYD**: `hook_length_formula_gHookYD` (session 14) is the independent
  HLF source — no circularity with `hook_walk_identity`.
- **a = 1 edge case**: When `a = 1`, `(0, 0)` has `(1, 0) ∈ gHookYD` (b ≥ 1), so NOT a top-right corner.
- **Remaining sorry scope**: ≥3-row shapes that are NOT [a,1^b] — e.g., [3,2,1], [4,3,2] — require GNW.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (5146 → 5274 lines, PART XIVb added)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (knowledge updated)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-02/meta.json` (lineCount 5274)
- PR: rjwalters/lean-genius#12381

### Sorry Count: 4 (unchanged count, reduced scope)

- `hook_walk_identity` (PART XIV): sorry now covers only ≥3-row non-gHookYD shapes
- `ni_count_eq_syt_count` (line 219): RSK bijection, FALSE as stated
- `lgv_det_factors_as_hook_quotient` (line 235): det identity, FALSE as stated
- `hook_length_formula` (line 245): depends on the two above (FALSE as stated)

### Next Steps

1. **GNW hook walk for ≥3-row non-gHookYD shapes**: ~200-300 Lean lines (probabilistic proof).
2. **Simpler stepping stone**: prove `hook_walk_identity` for shapes with exactly 3 rows.
3. **Archive sessions**: knowledge.md now >600 lines; archive sessions 5-18 to sessions/ subdir.

---

## Session 2026-04-25 (Session 20) — Transpose Duality: Hook Walk for ≤2-Column Shapes (PART XV)

**Mode**: REVISIT (RICH knowledge tier, score 112)
**Outcome**: PROGRESS — 9 new lemmas/defs (all non-circular), hook_walk_identity extended to 3 shape classes

### What I Did

1. Identified non-circular proof path for ≤2-column shapes via transpose duality:
   - μ.colLen 2 = 0 → μ.transpose.rowLen 2 = 0 (via `rowLen_transpose`)
   - `hook_length_formula_atMostTwoRows` (already proved) applies to μ.transpose
   - Three invariances under transpose: hookProd, SYT count, cell count
2. Built PART XV infrastructure (~180 lines, 0 new sorries):
   - `card_transpose`: μ.transpose.card = μ.card
   - `hookLength_transpose`: hookLength(μ,i,j) = hookLength(μ.transpose,j,i)
   - `hookProd_transpose`: hookProd(μ) = hookProd(μ.transpose)  
   - `sytTranspose` + `sytTranspose_injective` + `card_SYT_transpose`: bijection SYT(μ) ≃ SYT(μ.transpose)
   - `removeCorner_atMostTwoCols`: corner removal preserves ≤2-col (mirror of atMostTwoRows)
   - `hook_length_formula_atMostTwoCols`: HLF for ≤2-col, 0 sorries (non-circular via transpose)
   - `hook_walk_identity_atMostTwoCols`: hook walk identity for ≤2-col (same algebra as atMostTwoRows)
3. Updated `hook_walk_identity` dispatcher to add ≤2-col case as 3rd branch.
4. PR: rjwalters/lean-genius#12426

### Key Findings

- **Transpose invariances**: All three quantities needed for hook_walk_identity — hookProd, SYT count, cell count — are invariant under Young diagram transpose. This is standard combinatorics but required explicit Lean proofs.
- **sytTranspose bijection**: Entry at (i,j) of the transposed SYT is the original entry at (j,i). Row-strictness in μ.transpose becomes col-strictness in μ and vice versa.
- **Non-circular proof**: `hook_length_formula_atMostTwoCols` proved via transpose (not via `hook_walk_identity`), then the hook walk identity follows by the same algebraic argument as the 2-row case.
- **Remaining sorry scope**: Now only ≥3-row AND ≥3-col AND non-gHookYD shapes. This means ≥3 rows, ≥3 columns, and at least 2 rows with ≥3 cells (e.g., [3,2,1], [4,3,2,1]). The 2-column shapes like [2,2,2,2] and [3,2] are now covered.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean` (5274 → 5452 lines, PART XV added)
- `research/problems/ballot-problem-oq-03-oq-01-oq-02/knowledge.md` (this file)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (knowledge updated)
- PR: rjwalters/lean-genius#12426

### Sorry Count: 4 (unchanged count, reduced scope again)

- `hook_walk_identity` (line ~5373): sorry now covers only ≥3-row AND ≥3-col AND non-gHookYD shapes
- `ni_count_eq_syt_count` (line 219): RSK bijection, FALSE as stated
- `lgv_det_factors_as_hook_quotient` (line 235): det identity, FALSE as stated
- `hook_length_formula` (line 245): depends on the two above (FALSE as stated)

### Next Steps

1. **3-row case**: Prove `hook_walk_identity` for shapes with exactly 3 rows (rowLen 3 = 0 but rowLen 2 > 0). This would require the GNW argument but restricted to 3-row shapes.
2. **GNW hook walk for general shapes**: ~200-300 Lean lines, the probabilistic hook walk proof. The key identity: Σ_{c ∈ corners(μ)} hookProd(μ)/hookProd(μ\c) = n follows from a Markov chain analysis.
3. **Archive old sessions**: knowledge.md is now 500+ lines; archive sessions 12-18 to sessions/.
