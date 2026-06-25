# Current State

**Phase**: FORMALIZED (obstruction proved; fixed-dimension question remains open)
**Since**: 2026-06-25
**Iteration**: 1

## Current Focus

Formalized the orthogonality obstruction to a higher-dimensional reverse
Littlewood–Offord theorem: `proofs/Proofs/Erdos395OQ02.lean` (240 lines,
9 theorems, 7 defs, 0 sorries, 0 axioms; #print axioms reports only
propext / Classical.choice / Quot.sound — no native_decide).

## Active Approach

Single deterministic identity drives everything:

1. **Orthogonality identity** (`signedSum_norm_sq_of_orthonormal`) — for an
   orthonormal family z₁,…,zₙ in any real inner product space and any sign
   vector ε ∈ {±1}ⁿ, `‖Σ εᵢzᵢ‖² = n` exactly, independent of the signs. The
   cross terms ⟨zᵢ,zⱼ⟩ vanish; εᵢ² = 1 collapses the diagonal to n.

2. **Obstruction** (`orthonormal_smallSum_eq_empty`,
   `orthonormal_smallSumProb_eq_zero`) — comparing squared norms, the event
   `‖S‖ ≤ C` forces `n ≤ C²`, so for any fixed threshold C with `C² < n` the
   favourable set is empty and its probability is 0.

3. **Headline** (`dimensionFree_reverseLO_false`) — the dimension-free,
   fixed-threshold analogue of HJNS 2024 is FALSE: the standard orthonormal
   basis of ℝⁿ (dimension d = n) gives probability 0 for every n > C², while
   any claimed bound demands c/n > 0.

## Blockers

The genuine open question — the **fixed-dimension** reverse Littlewood–Offord
problem (`ReverseLO_fixedDim d` for d ≥ 3: does a c_d/n lower bound hold for
unit vectors in ℝ^d?) — is **not** resolved. It is recorded as an unproven
Prop. The obstruction shows the dimension must be bounded independently of n
(or the threshold must scale with d), but the fixed-d case is open.

## Next Action

Two natural directions:
- Determine the optimal threshold growth C(d): the identity ‖Σεᵢzᵢ‖² = n
  suggests C(d) ~ √d on orthonormal configurations; pin the dependence across
  all unit configurations.
- Attempt the fixed-d lower bound via a Paley–Zygmund / Fourier route using
  ‖Σεᵢzᵢ‖² = n as the second-moment input, paralleling HJNS.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
