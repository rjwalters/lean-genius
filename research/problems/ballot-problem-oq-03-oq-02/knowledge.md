# Knowledge Base: General r×r LGV Determinant

## Session 2026-03-22 (researcher-2) - Initial Formalization

**Mode**: FRESH (from survey phase)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: surveyed (knowledge score 8)

### Work Done
Created `BallotProblemOQ03OQ02.lean` (284 lines, 1 axiom, 0 sorries, 7 theorems, 17 defs).

### Architecture
The file formalizes the r×r LGV lemma infrastructure:

| Component | Type | Status |
|-----------|------|--------|
| `LGVConfig` | structure | r sources, r targets, strict mono |
| `PathTuple` | def | Dependent r-tuple of PathMN |
| `PermPathTuple` | def | σ-path tuples for permutation σ |
| `pathMatrix` | def | r×r matrix M_{i,j} = C(m+(bⱼ-aᵢ),m) |
| `niTupleCount` | def | Cardinality of NI path tuples |
| `swapTailsAt` | def | Tail-swap operation for GV involution |
| `lgv_lemma_rxr` | axiom | Main theorem: niTupleCount = det(pathMatrix) |
| `gessel_viennot_transposition_sign` | theorem | PROVED: sign(swap∘σ) = -sign(σ) |
| `isNonIntersecting_of_r_one` | theorem | PROVED: every 1-tuple is vacuously NI |
| `pathMatrix_det_nonneg` | theorem | PROVED: 0 ≤ det(pathMatrix) |

### Key Technical Challenges
1. **Dependent Pi Fintype**: `(i : Fin r) → PathMN m (f i)` doesn't get automatic
   Fintype synthesis. Solution: `unfold PathTuple; infer_instance` after the definition
   has been unfolded to expose the Pi type structure.

2. **Involution formulation**: The GV involution works on individual tuples, not
   aggregate counts. A σ-tuple maps to a τ-tuple (not σ-cardinality = τ-cardinality).
   The correct approach expands det, maps each tuple to its sign-reversed partner,
   and shows the only unpaired contributions are NI id-tuples.

3. **Permutation sign**: `Equiv.Perm.sign_swap` needs `Ne.symm hi` (not `hi`) because
   the swap is `Equiv.swap i (σ i)` and the hypothesis is `σ i ≠ i`, but sign_swap
   expects `i ≠ σ i`.

### What Remains
The single axiom `lgv_lemma_rxr` requires formalizing the full GV involution:
- For each non-identity σ, find first non-fixed point i
- Show paths Pᵢ and P_{σ(i)} must intersect (crossing lemma)
- Build the tail-swap bijection at first intersection point
- Show it maps σ-tuples to (swap ∘ σ)-tuples (sign reversal)
- Show non-NI id-tuples also pair with some non-id σ-tuples

### Build
Docker build passes with `LEAN_MEMORY_LIMIT=16384`.

## Session 2026-03-22 (researcher-7) - GV Cancellation for Small r

**Mode**: REVISIT (depth-first, RICH knowledge score 35)
**Problem**: ballot-problem-oq-03-oq-02
**Prior Status**: 1 axiom (gv_involution_cancellation), 0 sorries, 504 lines

### Work Done
Added 6 proved theorems (67 new lines, total 571 lines):

| Theorem | Purpose | Status |
|---------|---------|--------|
| `permPathTuple_one_equiv` | PermPathTuple cfg 1 ≃ PathTuple cfg | PROVED |
| `permPathTuple_one_card` | Card equivalence for id perm | PROVED |
| `niTupleCount_eq_card_of_all_ni` | NI count = total when all NI | PROVED |
| `isNonIntersecting_of_r_zero` | Vacuous NI for r=0 | PROVED |
| `gv_cancellation_r_zero` | GV cancellation for r=0 | PROVED |
| `gv_cancellation_r_one` | GV cancellation for r=1 | PROVED |

### Key Insights
- For r ≤ 1, Perm(Fin r) has exactly one element (identity), so the signed sum is trivial
- The GV involution is only needed for r ≥ 2 where non-identity permutations exist
- `Equiv.subtypeUnivEquiv` from Mathlib handles the "all elements satisfy P" → subtype equiv
- `Fintype` for subtype `{p // IsNonIntersecting cfg p}` needs explicit `Classical.dec` provision

### What Remains
The axiom `gv_involution_cancellation` is now proved for r=0 and r=1. For r ≥ 2:
- Prove the crossing lemma (non-identity perm paths must intersect)
- Construct the GV involution (swap tails at first intersection point)
- Prove the involution is sign-reversing and its own inverse
- Replace the axiom with the proved theorem

### Build
Docker build passes with `LEAN_MEMORY_LIMIT=16384`.
