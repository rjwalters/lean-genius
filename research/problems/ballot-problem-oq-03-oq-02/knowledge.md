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
