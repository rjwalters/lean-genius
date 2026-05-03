# Knowledge Base: ballot-problem-oq-03-oq-01-oq-02-incomplete-01

Hook-Length Formula via GNW random walk proof (Greene-Nijenhuis-Wilf 1979).
Goal: complete the proof of `hook_length_formula_Q` for ALL Young diagrams,
currently blocked by the `gnwProb_key` sorry in Helpers.lean.

---

## Problem Summary

The Lean file `BallotProblemOQ03OQ01OQ02Helpers.lean` (13,800+ lines) contains
a complete proof of the hook-length formula for:
- ≤2 rows, ≤2 cols, hook shapes, 3-9 rows, ≤9 cols, rectangles

The final case (≥10 rows AND ≥10 cols AND non-rectangular) uses `hook_walk_identity_gnw`
which depends on `gnwProb_key` (GNW 1979).

---

## Session 2026-05-03

**Mode**: FRESH
**Outcome**: progress — 4 of 5 sorries proved, 1 hard sorry remains

### What I Did

- Discovered the Helpers file had 5 sorries (not 1 as previously thought)
- Proved all 4 supporting lemmas:
  - `strictHookCells_card`: card(H*(i,j)) = h(i,j) - 1 via disjointness + card_Ico
  - `strictHookCells_nonempty`: ¬isCorner → H*(i,j) nonempty via witness
  - `strictHookCells_hookLen_lt`: y ∈ H*(x) → h(y) < h(x) via anti-monotonicity
  - `gnwProb_sum_corners`: Σ_c P_c(x) = 1 via induction on K (HARD lemma)
- Committed to feature/researcher-8

### Key Findings

- **gnwProb_sum_corners** (PROVED): Induction on K. Corner case uses
  `sum_eq_single_of_mem`. Non-corner case: factor (1/|H*|) out, swap sums,
  apply IH using `strictHookCells_hookLen_lt` to ensure h(y) ≤ K.

- **gnwProb_key mathematical structure**: The identity
  `Σ_{x ∈ μ} P_c(x) = H_μ/H_{μ\c}` requires deep combinatorial argument.
  The harmonic identity `(h(x)-1) * P_c(x) = Σ_{y ∈ H*(x)} P_c(y)` holds
  (follows from stability: P_c(K, y) = P_c(h(y), y) for K ≥ h(y)).

- **Double-counting insight**: #{non-corner x : y ∈ H*(x)} = y.1 + y.2 for y=(a,b).
  This follows because arm x's for y are (a,j) for j<a (all in μ, none corners)
  and leg x's are (i,b) for i<b (same). Gives the identity
  `Σ_x h(x)*P_c(x) = S + Σ_x (x.1+x.2)*P_c(x)` where S = Σ_x P_c(x).
  This identity alone doesn't determine S.

- **Why gnwProb_key is hard**: The proof requires relating walks on μ to walks
  on a smaller diagram μ\c'. The walks use the full diagram structure (hook
  lengths change when removing a corner), so there's no direct inductive step
  that keeps the walk probabilities the same.

- **GNW 1979 proof strategy**: The original proof uses the RSK correspondence
  (SYT ↔ pairs of SSYT). Σ_x P_c(x) = H_μ/H_{μ\c} is equivalent to:
  if you start at a uniform random cell, the probability of ending at c is
  f(μ\c)/f(μ) where f(μ) = |SYT(μ)| = n!/H_μ.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean`: 4 sorries → 0 (committed)

### Next Steps

1. **gnwProb_key via stability + harmonic**: Write stability lemma (K ≥ h(x) →
   gnwProb K = gnwProb h(x)), then attempt inductive proof of gnwProb_key
   using a diagram-level argument.

2. **Alternative for gnwProb_key**: The Novelli-Pak-Stoyanovskii (1997) explicit
   bijection gives P_c(x) = Π_{cells in hook of x ∩ hook of c} h_ν(z)/h_μ(z).
   This explicit formula sums to H_μ/H_ν. Could be formalized but requires
   ~300+ lines.

3. **Aristotle submission**: Submit gnwProb_key to Aristotle as HARD sorry.
   Unlikely to succeed but worth trying.
