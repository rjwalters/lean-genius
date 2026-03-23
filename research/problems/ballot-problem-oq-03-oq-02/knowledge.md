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
