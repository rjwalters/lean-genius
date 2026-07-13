# Problem: Apply LGV lemma to prove the hook-length formula for standard Young tableaux

**Slug**: ballot-problem-oq-03-oq-01-oq-02
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

The **hook-length formula** (Frame-Robinson-Thrall 1954) counts the number of
Standard Young Tableaux (SYT) of a given shape: for a partition λ of n with
Young diagram cells, the count is
$$f^\lambda = \frac{n!}{\prod_{u \in \lambda} h(u)}$$
where $h(u) = \lambda_i - i + \lambda'_j - j + 1$ is the **hook length** at cell
$u = (i,j)$ (arm length + leg length + 1).

The **Lindström-Gessel-Viennot (LGV) lemma** gives a determinantal formula for
non-intersecting lattice path systems. Applying LGV to appropriate source/target
configurations yields a determinant that factors into the hook-length product.

**Goal**: Using the existing n×n LGV infrastructure in `BallotProblemOQ03OQ02.lean`,
formalize the hook-length formula for standard Young tableaux of arbitrary shape.

### Formal Statement

```lean
-- Target: general hook-length formula
theorem hook_length_formula (λ : YoungDiagram) :
    Fintype.card (StandardYoungTableau λ) =
    λ.card.factorial / ∏ u : λ, hookLength λ u := by
  sorry

-- Intermediate: n×n LGV determinant factors into hook-length product
theorem lgv_det_equals_hook_product (λ : YoungDiagram) (r : ℕ) :
    lgvDet_nxn r (sources λ r) (targets λ r) =
    ∏ u : λ, hookLength λ u := by
  sorry
```

### Why This Matters

1. **Representation theory**: $f^\lambda$ counts the dimension of the Specht module
   $S^\lambda$ of $\mathfrak{S}_n$. A Lean formalization connects combinatorics to algebra.
2. **Gallery coherence**: The LGV lemma is fully proved in `BallotProblemOQ03OQ02.lean`
   (n×n case, 2315 lines, 0 sorries). Applying it to Young tableaux creates a natural
   extension closing the loop from ballot counting to representation theory.
3. **Mathlib advancement**: No complete Lean 4 proof of the hook-length formula exists.
   This would be a genuine contribution to Lean's combinatorics library.

## Known Results

### What's Already Proved (in Gallery)

- **2×2 LGV lemma**: `lgv_lemma_2x2` in `BallotProblemOQ03.lean` (2879 lines, 0 sorries)
  - `lgvDet m a₁ b₁ a₂ b₂ : ℤ` — 2×2 determinant formula
  - `lgvDet_nonneg`, `lgvDet_swap_sources`, `lgvDet_swap_targets`
  - Proof via Lindström involution on crossing path pairs
- **General n×n LGV lemma**: `lgv_lemma_rxr` / `lgv_universality` in `BallotProblemOQ03OQ02.lean`
  - Full n×n determinant equals non-intersecting path count
  - Proof via Gessel-Viennot sign-reversing involution
- **2-row hook-length**: `hook_length_formula_two_row` in `BallotProblemOQ03OQ03.lean`
  - For shape (m, m): $C_m \cdot (m+1)! \cdot m! = (2m)!$
  - Numerically verified for small cases via `native_decide`
- **Catalan/lattice path machinery**: extensive in `BallotProblemOQ03OQ02.lean`

### What's Still Open

- **`hookLength` function**: hook length at cell $(i,j)$ of YoungDiagram λ
- **Source/target encoding**: translate λ rows into LGV sources/targets
- **Determinant factorization**: show det[C(λᵢ - i + j, ...)] = ∏ h(u)
- **`StandardYoungTableau` count**: connect LGV NI-path count to `Fintype.card`
- **General formula**: `hook_length_formula` for arbitrary shape

### Our Goal

Formalize the hook-length formula for at least:
1. **Rectangular shapes**: λ = (m^r) — r rows of length m
2. **Staircase shapes**: λ = (r, r-1, ..., 1)
3. **Arbitrary shape**: full generality via LGV

Minimum viable result: define `hookLength` for `YoungDiagram`, verify it correctly
counts arm + leg + 1, and prove the formula for two-row shapes structurally
(extending `hook_length_formula_two_row`).

## Related Gallery Proofs

| Proof | File | Relevance |
|-------|------|-----------|
| `ballot-problem-oq-03` | `BallotProblemOQ03.lean` | 2×2 LGV lemma, 119 theorems |
| `ballot-problem-oq-03-oq-02` | `BallotProblemOQ03OQ02.lean` | General n×n LGV, 28 theorems |
| `ballot-problem-oq-03-oq-01-oq-01` | `BallotProblemOQ03OQ01OQ01.lean` | n×n LGV restatement + 3×3 examples |
| `ballot-problem-oq-03-oq-03` | `BallotProblemOQ03OQ03.lean` | 2-row hook-length proved |

## Initial Thoughts

### Potential Approaches

**Approach 1 — LGV via shifted sources/targets** (connects directly to infrastructure):
For λ = (λ₁ ≥ ... ≥ λ_r), set:
- Sources at x=0: $a_i = r - i$ (y-coordinate)
- Targets: $b_i = \lambda_i + r - i$ (x-coordinate, y=0)

Non-intersecting r-tuple count = det[C(λⱼ - i + j + r - 1, λⱼ - i + j)] which
is known to equal n! / ∏ h(u). Uses `lgv_lemma_rxr` from `BallotProblemOQ03OQ02.lean`.

**Approach 2 — Recursion on outer corners** (avoids LGV, simpler but misses connection):
$f^\lambda = \sum_{\mu \text{ outer corner}} f^\mu$, induction on $|\lambda|$.

**Approach 3 — Frobenius formula** (probabilistic/RSK, more indirect):
Use the RSK correspondence between permutations and pairs of SYT.

### Key Difficulties

1. **`YoungDiagram` in Mathlib**: Check what `hookLength`, `arm`, `leg` are available in
   `Mathlib.Combinatorics.YoungDiagram`. May need to define from scratch.
2. **Rectangular-to-arbitrary generalization**: LGV source/target encoding for
   non-rectangular shapes requires careful bookkeeping.
3. **Determinant factorization**: Showing the LGV determinant = ∏ h(u) requires
   a Vandermonde-type factorization. The 2×2 case may generalize well.

## Tractability Assessment

**Overall**: 5/10 — challenging but feasible given the extensive LGV infrastructure.

**Concrete first step**: Read `BallotProblemOQ03OQ02.lean` to understand the
`lgv_lemma_rxr` interface and source/target types. Then check Mathlib's
`YoungDiagram` for arm/leg/hook definitions.

**Fallback**: Prove the hook-length formula for rectangular shapes (m × r):
$f^{(m^r)} = \frac{(mr)!}{\prod_{i=1}^r \prod_{j=1}^m (m - j + r - i + 1)}$
using `lgv_lemma_rxr` with uniform source/target configuration.
