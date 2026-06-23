# Problem: Complete Hurwitz's Theorem (close the last sorry)

**Slug**: hurwitz-theorem-wip-01
**Created**: 2026-05-06T14:18:33Z
**Status**: Blocked on Mathlib (clean localization)
**Source**: gallery-gap

## Problem Statement

### Plain Language

The gallery entry `hurwitz-theorem` formalizes Hurwitz's theorem on $n$-square
identities and is mostly done: $n=1, 2, 3, 4, 8$ and the entire odd $n$ case are
fully proved. **One sorry remains** — `HurwitzTheorem.lean:1937` — covering even
$n \notin \{2, 4, 8\}$. Closing this sorry promotes the entry from `badge=wip`
to fully verified.

### Formal Statement

```lean
-- HurwitzTheorem.lean (line 1947)
theorem hurwitz_theorem (n : ℕ) (hn : n > 0) :
    Nonempty (NSquareIdentity n) ↔ n ∈ admissibleDimensions
```

The remaining open subgoal (line 1937 in `hurwitz_only_if`):
```lean
-- For even n = 2k with n ∉ {2, 4, 8}, given an NSquareIdentity n, derive False.
-- Equivalently: show no real n-dimensional faithful module exists for Cl(0, n-1).
```

### Why This Matters

- **Closes the only outstanding sorry** in `HurwitzTheorem.lean` (currently
  `sorries=1`, `badge=wip`).
- **Forces a Mathlib-level construction** (real Clifford algebra periodicity /
  Artin-Wedderburn for real semisimple algebras) that is broadly useful beyond
  Hurwitz — Bott periodicity, KO-theory, the Hopf invariant one theorem, the
  Radon-Hurwitz numbers, and the parallelizability of $S^{n-1}$ all need it.
- **Unblocks** the parallel sorry in `HurwitzOnlyIf.lean:111`
  (`hurwitz_only_if_ring`, the `NormedDivisionRing` formulation).

## What Is Already Proved

All upstream infrastructure is in place; the gap is **purely** in Clifford
structure theory.

| Lemma | File:line | Status |
|-------|-----------|--------|
| `oneSquareIdentity` | HurwitzTheorem.lean:119 | proved |
| `twoSquareIdentity` | HurwitzTheorem.lean (Brahmagupta-Fibonacci) | proved |
| `fourSquareIdentity` | HurwitzTheorem.lean (Euler quaternion) | proved |
| `eight_square_identity_exists` | HurwitzTheorem.lean (Cayley-Dickson) | proved |
| `no_three_square_identity` | HurwitzTheorem.lean | proved (Parseval, ~800 lines) |
| `no_odd_nsquare` | HurwitzTheorem.lean:1880 | proved (det parity) |
| `crossMat_skewSym` | HurwitzTheorem.lean:1788 | proved |
| `crossMat_transMul` | HurwitzTheorem.lean:1779 | proved |
| `crossMat_sq_neg_one` | HurwitzTheorem.lean:1869 | proved (M² = -I) |
| `crossMat_anticommute` | HurwitzTheorem.lean:1822 | proved (M_j M_k + M_k M_j = 0) |
| `hurwitz_only_if` (n∈2k∩∉{2,4,8}) | HurwitzTheorem.lean:1937 | **sorry** |
| `hurwitz_field_case` | HurwitzOnlyIf.lean | proved (Gelfand-Mazur) |
| `hurwitz_only_if_ring` (non-comm) | HurwitzOnlyIf.lean:111 | **sorry** |

## What Is Missing

The `crossMat_*` infrastructure proves: from any `NSquareIdentity n`, the matrices
$M_j := \text{crossMat}(j_0, j)$ for $j \neq j_0$ are $n - 1$ anti-commuting orthogonal
$n \times n$ real matrices with $M_j^2 = -I$. These give a **real $n$-dimensional
representation of $\mathrm{Cl}(0, n-1)$**.

To finish, one needs:

1. **Real Clifford structure classification.** Bott periodicity table:
   $\mathrm{Cl}(0, n+8) \cong \mathrm{Cl}(0, n) \otimes M_{16}(\mathbb{R})$, plus the
   small-$n$ identifications $\mathrm{Cl}(0, 1) \cong \mathbb{C}$, $\mathrm{Cl}(0, 3) \cong \mathbb{H}$,
   $\mathrm{Cl}(0, 5) \cong M_2(\mathbb{H})$, $\mathrm{Cl}(0, 7) \cong M_8(\mathbb{R}) \oplus M_8(\mathbb{R})$, etc.

2. **Minimum faithful real representation dimension.** From the Wedderburn
   decomposition $A \cong \prod_i M_{n_i}(D_i)$ with $D_i \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$,
   read off the smallest $n_i \dim_{\mathbb{R}} D_i$.

3. **Apply** to $n - 1$ in the failing-even-case branch:
   - $n = 6$: $\mathrm{Cl}(0, 5) \cong M_2(\mathbb{H})$, min dim $= 2 \cdot 4 = 8 > 6$ → contradiction.
   - $n = 10$: $\mathrm{Cl}(0, 9) \cong M_{16}(\mathbb{R})$, min dim $= 16 > 10$ → contradiction.
   - General $n = 2k \notin \{2, 4, 8\}$: similar dimension count.

**None of (1)–(2) are in Mathlib v4.26.0.** The CliffordAlgebra namespace has
the universal property and basic operations but no structure classification.

## Tractability

**Difficulty**: HIGH — estimated ~1000 lines of new Mathlib infrastructure.
**Per-session work**: nearly zero in the gallery; the bottleneck is upstream.

## Approaches

1. **Wait for Mathlib.** Track Clifford-algebra PRs in the Mathlib repository.
   Re-attempt when `CliffordAlgebra.equivOfBottPeriodicity` (or analogue) lands.

2. **Small-case decomposition.** Prove $n = 6$ and $n = 10$ directly using
   ad-hoc Wedderburn structure (hand-coded matrix algebra over $\mathbb{R}, \mathbb{C}, \mathbb{H}$),
   leaving only the asymptotic case as sorry. This narrows the open scope but
   does not eliminate it; estimated 200–400 lines per case.

3. **Algebra-level refactor (HurwitzOnlyIf only).** Split
   `hurwitz_only_if_ring` into a concrete bridge lemma
   `nsquareIdentity_of_normedDivisionRing` (provable in ~80 lines using
   Mathlib's `Module.Finite.finBasis` + isometry) plus the call to
   `HurwitzTheorem.hurwitz_only_if`. Sorry count unchanged but sorry localized
   to one place — reduces duplication.

4. **Submit Mathlib RFC.** Request a Clifford classification API. Long horizon.

## Metadata

```yaml
tags:
  - seeker-selected
  - wip
  - algebra
  - number-theory
  - clifford-algebras
  - blocked-on-mathlib
related_proofs:
  - hurwitz-theorem
  - hurwitz-impossibility
  - hurwitz-three-square-impossibility
difficulty: high
source: gallery-gap
created: 2026-05-06T14:18:33Z
```

**Significance**: 7/10 — closes the last sorry in a high-prestige gallery entry.
**Tractability**: 3/10 — requires Mathlib infrastructure not currently available.

## References

- A. Hurwitz, *Über die Composition der quadratischen Formen*, Math. Ann. 88
  (1923), 1–25 (posthumous; original 1898).
- J. Baez, *The Octonions*, Bull. Amer. Math. Soc. 39 (2002), 145–205.
- Bott & Milnor, *On the parallelizability of the spheres*, Bull. Amer. Math. Soc.
  64 (1958), 87–89.
- M.F. Atiyah, *K-theory and reality*, Quart. J. Math. Oxford 17 (1966), 367–386.

### Mathlib

- `Mathlib.Algebra.Quaternion` — `Quaternion.normSq_mul`.
- `Mathlib.Analysis.Normed.Algebra.GelfandMazur` — used in the field subcase.
- `Mathlib.LinearAlgebra.CliffordAlgebra.*` — universal property only;
  **no** structure classification as of v4.26.0.
