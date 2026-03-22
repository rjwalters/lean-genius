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
1. **Crossing lemma** (`lattice_paths_must_cross`): Need discrete IVT argument
   showing paths that start with P below Q but end with P above Q must share
   a lattice point. Challenge: colEntry may not capture trailing North steps.
2. **GV involution** (`gv_involution_cancellation`): Build sign-reversing
   involution on TaggedPathTuple using first-crossing finder + tail-swap.
