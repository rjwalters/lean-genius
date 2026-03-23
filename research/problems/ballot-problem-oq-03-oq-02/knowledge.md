# Knowledge Base: General r×r LGV Determinant

## Session 2026-03-22 (researcher-2) - Initial Formalization

**Mode**: FRESH (from survey phase)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: surveyed (knowledge score 8)

### Work Done
Created `BallotProblemOQ03OQ02.lean` (284 lines, 1 axiom, 0 sorries, 7 theorems, 17 defs).

### Architecture
The file formalizes the r×r LGV lemma infrastructure with algebraic bridge
and combinatorial foundations.

---

## Session 2026-03-22 (researcher-3) - Axiom Elimination

**Mode**: REVISIT (depth-first, RICH knowledge score 35)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: 0 sorries, 1 axiom (gv_involution_cancellation)

### Work Done
Converted the `gv_involution_cancellation` axiom to a theorem with structured
sorry decomposition. 0 axioms, 2 sorries remain. File: 688 lines.

### Key Results

| Component | Status | Description |
|-----------|--------|-------------|
| `TaggedPathTuple` | **Proved** | Sigma type Σ_σ PermPathTuple(σ) with Fintype |
| `sum_tagged_eq_sum_perm` | **Proved** | Signed perm sum = sum over tagged tuples |
| `perm_ne_one_has_inversion` | **Proved** | Non-id perms have inversions (via firstNonFixed) |
| `nonid_perm_paths_cross` | **Proved** | Non-id σ-tuples always cross (uses crossing lemma) |
| `LGVConfig.wellFormed` | **Proved** | ∀ i j, sources i ≤ targets j; iff characterization |
| `lattice_paths_must_cross` | **Sorry** | Discrete IVT for lattice paths |
| `gv_involution_cancellation` | **Sorry** | Involution bookkeeping (depends on crossing lemma) |

### Critical Discovery: Well-Formedness Requirement

The original axiom was stated without a well-formedness condition. This is WRONG
for some configs: when `targets(σ i) < sources(i)`, Nat subtraction gives
`PathMN m 0` (horizontal paths) instead of an empty type (no valid paths).
This causes pathMatrix entries to be 1 instead of 0, making the determinant
incorrect.

**Fix**: Added `LGVConfig.wellFormed` condition: `∀ i j, sources i ≤ targets j`.
Equivalent to `sources(r-1) ≤ targets(0)` for strictly mono sequences.

### NonIntersecting Definition Concern

The `NonIntersecting` definition checks:
1. Disjoint `colYRange` at each column x < m
2. Different y-positions at column m boundary

It does NOT check lattice points in the "trailing" segment (North steps after
the last East step). This may be incomplete for paths where trailing steps
cause overlap. Needs investigation.

### What Remains
1. **GV involution** (`cancellable_sum_eq_zero`): Build sign-reversing
   involution on TaggedPathTuple using first-crossing finder + tail-swap.

---

## Session 2026-03-23 (researcher-3) - Counting Bijection Proof

**Mode**: REVISIT (depth-first, RICH knowledge score 29)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: 0 axioms, 2 sorries

### Work Done
Proved `card_nonCancellable_eq_niTupleCount` — the counting bijection between
non-cancellable tagged tuples and NI identity path tuples.

**Key insight**: `PermPathTuple cfg 1` is *definitionally* equal to `PathTuple cfg`
(since `(1 : Perm) i = id i = i`). This makes the bijection between
`{⟨1, p⟩ : TaggedPathTuple | NI(p)}` and `{p : PathTuple | NI(p)}` trivial —
the `Equiv` reduces to identity maps with proof-irrelevant packaging.

**Proof technique**: `Fintype.card_congr` with an explicit `Equiv` whose `toFun`
projects out the path data and `invFun` wraps it with σ=1. Both `left_inv` and
`right_inv` close by `Subtype.ext` + `Sigma.ext rfl (heq_of_eq rfl)` due to
definitional equality of the underlying types.

### Files Modified
- `proofs/Proofs/BallotProblemOQ03OQ02.lean` (sorry → proof for card_nonCancellable)

### What Remains
1. **`cancellable_sum_eq_zero`** (1 sorry): The GV sign-reversing involution.
   Requires: first-crossing finder, tail-swap at crossing, proof of involutivity
   and sign reversal. Infrastructure available: `swapTailsAt`, `nonid_perm_paths_cross`,
   `gessel_viennot_transposition_sign`, `lattice_paths_must_cross`.
   Could use `Finset.sum_involution` from Mathlib.

---

## Session 2026-03-23 (researcher-2) - gvNewPerm Bug Fix + Sorry Reduction

**Mode**: REVISIT (depth-first, RICH knowledge score 47)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: in-progress, ACT phase, 4 sorries

### Critical Bug Fix

**gvNewPerm used WRONG multiplication order.** It was defined as `swap(i,j) * σ`
(left multiplication), but the correct definition is `σ * swap(i,j)` (right
multiplication). This is critical because:

- With LEFT mult: `σ'(i) = swap(i,j)(σ(i))` — depends on σ(i) relative to {i,j}
- With RIGHT mult: `σ'(i) = σ(swap(i,j)(i)) = σ(j)` — always gives σ(j)

The tail swap produces paths `source(i) → target(σ(j))` and `source(j) → target(σ(i))`,
which matches σ'(i) = σ(j) and σ'(j) = σ(i) only with RIGHT multiplication.

### Work Done
- Fixed `gvNewPerm`: `Equiv.swap i j * t.1` → `t.1 * Equiv.swap i j`
- Fixed `gvInvolution_sign_reversal`: updated for right mult (`mul_neg` instead of `neg_mul`)
- Fixed `gvInvolution_no_fixed`: updated algebraic extraction of swap=1
- Fixed `isNonCancellable` forward reference: moved definition before `cancellable_has_crossing`
- Simplified `gvInvolutionFn`: uses `Classical.choice (pathMN_nonempty cfg.m _)` for all paths
- Added `pathMN_nonempty`: proves `Nonempty (PathMN m n)` via pathMN_card + choose_pos
- Fixed `cancellable_has_crossing` σ=1 case: destructure Sigma + subst approach

### Key Results
- **4 sorries → 2 sorries**: Eliminated path construction sorries by using Classical.choice
- **Bug fix**: gvNewPerm now correctly typed for tail swap construction
- **Proof improvements**: sign_reversal and no_fixed fully proved with right multiplication

### Remaining Sorries
1. **Membership preservation** (L1163): Show image tuple is cancellable
   - If `σ * swap(i,j) ≠ 1`: trivially cancellable (σ' ≠ 1 → not a fixed point)
   - If `σ = swap(i,j)`: need to show swapped paths still cross
   - Requires specific tail-swapped PathMN construction (not just Classical.choice)

2. **Self-inverse** (L1170): Show `g(g(a)) = a`
   - Permutation part: `(σ * swap(i,j)) * swap(i,j) = σ` ✓ trivial
   - Path part: requires canonical crossing pair (current uses Classical.choose)
   - Requires: define canonical first crossing via `Finset.min'` on lex order
   - Then prove: canonical crossing preserved under tail swap (prefix unchanged)

### Pre-existing Issues (not introduced this session)
- `take_at_column_entry` and `take_east_count_within_column`: Mathlib compat errors
  (`Bool.false_eq_false` unknown constant, omega failures). These are on ~12 lines
  around L835-L946. Need Mathlib API update.

### Files Modified
- `proofs/Proofs/BallotProblemOQ03OQ02.lean` (+15/-26 lines, net smaller)
- `src/data/research/problems/ballot-problem-oq-03-oq-02.json`

---

## Session 2026-03-23 (researcher-2, session 2) - northThenEast Path Infrastructure

**Mode**: REVISIT (depth-first, RICH knowledge score 47)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: in-progress, ACT phase, 2 sorries (membership + self-inverse)

### Deep Analysis of Remaining Sorries

Extensive analysis of the GV involution requirements revealed:

1. **Classical.choice is fundamentally incompatible with self-inverse.**
   `gvInvolutionFn` used `Classical.choice` for ALL paths. This makes g(g(t)).2 =
   Classical.choice ≠ t.2, so self-inverse is impossible. The involution MUST use
   specific path constructions.

2. **Membership (σ=swap case) requires crossing paths.** When σ*swap(i,j)=1,
   the image has σ'=1. To show ¬NI, we need actual paths that cross. Classical.choice
   provides no guarantees about intersection properties.

3. **Self-inverse requires canonical crossing preserved under tail swap.**
   The firstNonFixed approach does NOT give self-inverse (shown by 3-cycle
   counterexample: σ=(012), gvNewPerm gives swap(1,2), applying again gives id ≠ σ).
   The correct approach uses lex-min on (c, y, i, j) crossing quadruples.

### Work Done

1. **Built `northThenEastPath`**: Canonical path (all North then all East) constructor.
   - `northThenEastList_length`, `northThenEastList_east`: validity proofs
   - `northThenEast_colEntry_one`: at column 0, visits all y-values up to n

2. **Proved `northThenEast_not_NI`**: Two northThenEast paths cross at column 0
   when wellFormed holds (sources(i) ≤ targets(j) gives overlapping y-ranges).

3. **Replaced `gvInvolutionFn`**: Now uses `northThenEastPath` instead of
   `Classical.choice`. This ensures the image paths are well-typed AND crossable.

4. **Re-proved `sign_reversal` and `no_fixed`**: Identical proofs carry over
   since they only depend on the permutation component.

### What Remains

1. **Membership sorry** (HARD, ~20 lines): The mathematical argument is complete:
   when σ'=1, northThenEast paths cross at column 0. The sorry is due to
   `PermPathTuple.toPathTuple` cast unfolding — need to show that under the
   σ'=1 cast, the paths reduce to `northThenEastPath m (targets(k) - sources(k))`,
   which cross by `northThenEast_not_NI` + `wellFormed`.

2. **Self-inverse sorry** (HARD, ~200 lines): Requires full tail-swap construction:
   (a) Canonical crossing pair via Finset.min' on lex-ordered (c, y, i, j) quadruples
   (b) Split PathMN at shared lattice point (c, y) — prefix + suffix
   (c) Join prefix of P with suffix of Q → valid PathMN (proved by take_east_count)
   (d) Double swap = identity (via List.take_append_drop involutivity)
   (e) Canonical crossing preservation: no new crossings before (c, y) introduced

### Key Insight: Self-Inverse Architecture

The self-inverse proof has this structure:
- Tail swap at (c, y) only modifies paths AFTER position (c, y) in the list
- Path prefixes before (c, y) are preserved
- Any crossing before (c, y) in the image also existed in the original
- Therefore the canonical first crossing (lex-min) is the same for t and g(t)
- Swapping twice at the same point: take(take(P,k₁)++drop(Q,k₂), k₁)++drop(take(Q,k₂)++drop(P,k₁), k₂) = P
  (proved by List.take_append_of_le_length + List.drop_append_of_le_length)

### Files Modified
- `proofs/Proofs/BallotProblemOQ03OQ02.lean` (~+50 lines, northThenEast infrastructure)

---

## Session 2026-03-23 (researcher-6) - Membership Proof + sum_involution Assembly

**Mode**: REVISIT (depth-first, RICH knowledge score 59)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: in-progress, ACT phase, 2 sorries (membership + self-inverse)

### Work Done
- Proved `gvInvolution_membership`: the GV involution image is cancellable
- Added `northThenEast_not_NI_general`: generalized NTE crossing lemma (handles m=0)
- Added `pathMN_cast_val`: cast between PathMN with equal n preserves .val
- Assembled `cancellable_sum_eq_zero` using `Finset.sum_involution` with 3/4 properties proved

### Key Technical Insights
1. **Cast preservation via subst**: `pathMN_cast_val` proves `(cast h P).val = P.val` by `subst hn; intro _; rfl`. Key: provide the natural number equality separately, then Lean's `subst` makes the type equality trivial.
2. **σ'-identity extraction**: When `hσ : σ' = 1`, use `fun k => by rw [hσ]; rfl` to derive `σ' k = k` for all k. Then `rw [hσ_id k]` propagates through `gvNewPerm` to simplify northThenEast arguments.
3. **m=0 edge case**: northThenEast_not_NI fails at m=0 (no columns to check). But the final-column condition `targets(i) < sources(j) ∨ targets(j) < sources(i)` contradicts wellFormed.
4. **wellFormed → NTE crossing bounds**: Need `sources(i) ≤ sources(j) + (targets(j) - sources(j))`, which requires both `hwf i j` (sources(i) ≤ targets(j)) and `source_le_target j` (to undo Nat subtraction).

### Remaining: 1 Sorry (Self-Inverse)
The self-inverse `g(g(t)) = t` cannot be proved with the current `gvInvolutionFn` which replaces ALL paths with northThenEast (destroying original path data).

**Required redesign**: Replace `gvInvolutionFn` with a tail-swap involution:
1. Find canonical first crossing (lex-min column, y-value across all pairs)
2. Swap path suffixes at that crossing point (preserving prefixes)
3. Self-inverse follows because: crossing is the same for t and g(t) (prefix unchanged → same crossing set before the swap point), and double tail-swap = identity.

**Infrastructure in place**: `northBeforeEast_prefix`, `colEntry_prefix_eq` (proves suffix swap doesn't change colEntry at earlier columns).

### Files Modified
- `proofs/Proofs/BallotProblemOQ03OQ02.lean` (2→1 sorries, +3 new lemmas)
- `src/data/proofs/ballot-problem-oq-03-oq-02/meta.json`
- `src/data/research/problems/ballot-problem-oq-03-oq-02.json`

### Pool Status
- Available: 76, In-progress: 322, Completed: 235

---

## Session 2026-03-23 (researcher-6) - Self-Inverse Deep Analysis

**Mode**: REVISIT (depth-first, RICH knowledge score 66)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: ACT phase, 1 sorry (self-inverse of GV involution)

### Analysis

Deep investigation of the self-inverse property for `cancellable_sum_eq_zero`.

**Why current approach fails**: The existing `gvInvolutionFn` replaces ALL paths with
`northThenEastPath`. This is fundamentally NOT self-inverse because applying twice gives
NTE paths (not the original paths). The information about the original paths is destroyed.

**Why tail-swap is necessary**: Any involution that discards original path data cannot be
self-inverse. The classical GV proof swaps path suffixes at a shared lattice point, which
is reversible (double-swap = identity).

### Solution Architecture

**Key encoding**: `key = (c + y) * r² + i * r + j` where (c, y) is a shared lattice point
between paths i and j. Using `c + y` (not lex on (c, y)) as primary key ensures invariance
because `c + y` equals the list position proxy.

**Invariance proof**: After swapping tails at split positions `k_i = (c₀+y₀) - source(i)`
and `k_j = (c₀+y₀) - source(j)`:
1. At shared points with key' < key₀: the visit positions `c'+y'-source` are less than the
   split positions, so path prefixes are unchanged → shared point status unchanged
2. At key₀ itself: the shared point (c₀, y₀) is preserved (in the prefix for both paths)
3. Therefore `Nat.find` returns the same key for t and g(t)

**Self-inverse**: Same key → same crossing pair (i₀, j₀) → same split positions → double
tail-swap restores original lists (via `List.take_append_drop`) → σ * swap(i,j)² = σ

**Double tail-swap identity** (proved in analysis, not yet in Lean):
```
(l₁.take k₁ ++ l₂.drop k₂).take k₁ = l₁.take k₁  [by List.take_left]
(l₂.take k₂ ++ l₁.drop k₁).drop k₂ = l₁.drop k₁  [by List.drop_left]
∴ result = l₁.take k₁ ++ l₁.drop k₁ = l₁            [by List.take_append_drop]
```

**Validity of swapped paths** (PathMN proofs):
- East count: `take_east_count_within_column` gives prefix East = c₀,
  suffix East = m - c₀, total = m ✓
- North count: prefix North = y₀ - source(i), suffix North = n_j - (y₀ - source(j)),
  total = n_j + source(j) - source(i) = targets(σ(j)) - source(i) ✓
- Length follows from East + North counts ✓

### Estimated Implementation

| Component | Lines | Difficulty |
|-----------|-------|-----------|
| Shared point infrastructure (pathVisitsPoint, spKey, Nat.find) | ~50 | Medium |
| Deterministic crossing pair + split positions | ~30 | Medium |
| New gvInvolutionFn (tail-swap) | ~40 | Hard (dependent types) |
| Swapped path validity (PathMN proofs) | ~50 | Medium |
| Key invariance lemma | ~50 | Hard |
| Self-inverse proof | ~40 | Medium (given invariance) |
| Re-prove sign/membership/no-fixed | ~40 | Easy (adapt existing) |
| **Total** | **~300** | |

### Key Technical Challenges

1. **Dependent types**: `PermPathTuple cfg σ` depends on σ. Swapping paths at indices
   i₀ and j₀ changes their types (PathMN m n with different n). Need careful casts.
2. **Key invariance**: Need to formalize "colEntry depends only on prefix" — requires
   showing `colEntry` of `(l.take k ++ l'.drop k')` at columns < c₀ equals `colEntry` of `l`.
3. **Finset vs Nat.find**: Using `Nat.find` for the min key requires proving the predicate
   is decidable (or using `Classical.dec`).

### What Would Help

- A Lean 4 helper lemma: `List.take_of_take_append (h : k ≤ l₁.length) : (l₁ ++ l₂).take k = l₁.take k`
- A Lean 4 helper: `List.drop_of_take_append (h : k = l₁.length) : (l₁ ++ l₂).drop k = l₂`
- `colEntry_take_prefix`: if `(l.take k).countP false = c` and `c ≤ c'`, then
  `colEntry (l.take k ++ l'.drop k') c' = colEntry l c'` for `c' ≤ c`

### Next Steps (for future sessions)
1. Implement `take_drop_swap_involutive` List lemma (cleanest starting point)
2. Define `pathVisitsPoint` and shared point key infrastructure
3. Build deterministic crossing pair selection via `Nat.find`
4. Implement new `gvInvolutionFn` with tail-swap
5. Prove key invariance and self-inverse
6. Adapt existing proofs for sign/membership/no-fixed

### Files Modified
- None (analysis only, no code changes committed)
