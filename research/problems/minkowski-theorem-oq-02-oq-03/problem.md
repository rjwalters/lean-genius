# Problem: Simultaneous Dirichlet Approximation for n Real Numbers via Minkowski

**Slug**: minkowski-theorem-oq-02-oq-03
**Created**: 2026-05-12
**Status**: Active
**Source**: seeker (gallery follow-up to `minkowski-theorem-oq-02`)

## Problem Statement

### Formal Statement

For any real numbers `α₁, …, αₙ ∈ ℝ` and any integer `Q ≥ 1`,
there exist integers `p₁, …, pₙ, q ∈ ℤ` with
`1 ≤ q ≤ Qⁿ` and `|q αᵢ − pᵢ| < 1/Q` for all `i = 1, …, n`.

Equivalently: for any `Q ≥ 1`, there is an integer `1 ≤ q ≤ Qⁿ` with
`max₁≤i≤n |αᵢ − pᵢ/q| < 1/(qQ)` for some integers `pᵢ`.

### Plain Language

The 1D Dirichlet approximation theorem (proved in
`MinkowskiTheoremOQ02.lean` / `MinkowskiTheoremOQ02OQ01.lean`) says: for any real
`α` and any `Q ≥ 1`, you can rationally approximate `α` to within
`1/(qQ)` using a denominator `q ≤ Q`. This sub-OQ asks the n-dimensional
generalization: approximate `n` reals simultaneously by rationals with
a common denominator. The catch — to share a denominator across `n`
constraints — is that `q` is now allowed up to `Qⁿ` instead of `Q`.

### Why This Matters

- The simultaneous version is one of the standard derivations of the
  `n`-dimensional case of Minkowski's theorem (`MinkowskiProved.minkowski_integer_lattice_proved`).
- It is the prototype for higher-rank Diophantine approximation and the
  starting point for Khintchine's theorem and metric Diophantine
  approximation more broadly.
- The 1D proof in `MinkowskiTheoremOQ02OQ01.lean` is already
  axiom-free; lifting it to general `n` exercises the same techniques
  (`IsOpen.measurableSet`, `convex_Ioo.linear_preimage`, the
  `map_matrix_volume_pi_eq_smul_volume_pi` shear identity).

## Known Results

### What's Already Proven

- **1D Dirichlet (`MinkowskiTheoremOQ02.lean`, 284 lines, 0 sorries, 3 axioms)**:
  Statement `dirichlet_approximation_from_minkowski` with three
  parallelogram-property axioms (convex / measurable / volume) discharged.
- **1D axiom-free (`MinkowskiTheoremOQ02OQ01.lean`, 267 lines, 0 sorries, 0 axioms)**:
  All three parallelogram axioms eliminated using
  `IsOpen.measurableSet`, `convex_Ioo.linear_preimage`, and
  `map_matrix_volume_pi_eq_smul_volume_pi` (shear determinant = −1).
- **n-dim Minkowski (`MinkowskiFundamentalTheorem.lean`, line 638)**:
  `MinkowskiProved.minkowski_integer_lattice_proved` takes a centrally
  symmetric convex set `s ⊆ ℝⁿ` with `volume s > 2ⁿ` and produces a
  nonzero `stdLattice n` point in `s`.

### What's Still Open

- Define `dirichletSetN α Q` (an `(n+1)`-dim parallelepiped) and prove
  its central symmetry, measurability, convexity, and volume.
- Apply `minkowski_integer_lattice_proved` to obtain a nonzero integer
  point of `dirichletSetN α Q`, extract the simultaneous approximation
  conclusion.
- Optional axiom-free finish (analog of `OQ-02-OQ-01`).

### Our Goal

Formalize the simultaneous Dirichlet approximation theorem as a
companion file `MinkowskiTheoremOQ02OQ03.lean`, modeled on
`MinkowskiTheoremOQ02.lean` with three measure-theoretic axioms
discharged in the same style as `OQ-02-OQ-01`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `minkowski-theorem-oq-02` | The 1D parent — directly generalized | parallelogram + Minkowski |
| `minkowski-theorem-oq-02-oq-01` | Axiom-free 1D — proof patterns to mirror | `IsOpen.measurableSet`, `convex_Ioo.linear_preimage`, shear map |
| `minkowski-fundamental-theorem` | The n-dim Minkowski API | `minkowski_integer_lattice_proved` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Direct (n+1)-dim parallelepiped (recommended)**

   Define
   ```
   dirichletSetN α Q : Set (Fin (n+1) → ℝ) :=
     {v | |v 0| < (Q^n : ℝ) + 1 ∧ ∀ i : Fin n, |αᵢ * v 0 - v i.succ| < 1 / (Q : ℝ)}
   ```
   - **Symmetry**: trivial from `abs_neg` (no Mathlib work).
   - **Measurability**: open as finite intersection of preimages of
     `Ioo` under `continuous_apply` and `continuous_const.mul - continuous_apply`.
   - **Convexity**: each predicate is the preimage of `Ioo` under a
     linear functional, hence convex; finite intersection of convex
     sets is convex (`Convex.inter` or `Set.Finite.convex_iInter`).
   - **Volume**: shear map
     `T(v) = (v 0, α 1 * v 0 - v 1, …, α n * v 0 - v n)` has matrix
     determinant `±1` (lower-triangular with 1, −1, …, −1 on the diagonal),
     and `map_matrix_volume_pi_eq_smul_volume_pi` applies.
     Resulting rectangle has measure
     `2(Qⁿ + 1) · (2/Q)ⁿ = 2^(n+1)(Qⁿ + 1) / Qⁿ > 2^(n+1)`.

   **Why it might work**: directly mirrors the 1D axiom-free proof; all
   Mathlib lemmas are already in use in `OQ-02-OQ-01.lean`.
   **Risk**: the shear determinant calculation is now
   `Matrix.det (!![1, 0, …, 0; α 1, -1, 0, …; …; α n, 0, …, -1])`; need to
   confirm `Matrix.det_of_lowerTriangular` (or
   `Matrix.det_diagonal_of_diag_blocks`) handles this. If not, expand by
   cofactors along row 0.

2. **Approach B — Pi-encoding of the dirichletSet**

   Express `dirichletSetN α Q` as `Set.pi univ (...)` after the shear,
   and use `Measure.pi` directly. This reuses
   `volume_pi_Ioo` already invoked in `OQ-02-OQ-01.lean`. Less
   structural, but no shear-determinant detour required.

   **Risk**: requires re-proving symmetry on the shear's image rather than
   on the original parallelepiped.

### Key Difficulties

- The shear map for general `n` has a non-trivial determinant formula
  but is still triangular. Verifying `Matrix.det` with
  `Matrix.det_of_lowerTriangular` (Mathlib) should close it, but the
  exact name/signature needs to be verified.
- `dirichletSetN α Q` is `Set (Fin (n+1) → ℝ)`, not `Set (Fin n → ℝ)`.
  The Minkowski hypothesis is on the lattice dimension `m = n+1`, so the
  Mathlib threshold `2^m = 2^(n+1)` matches the volume bound exactly.
- Avoiding the "off by one" between `Fin n` (free indices) and `Fin (n+1)`
  (column 0 + n approximation rows). A `Fin.succ`-based indexing is
  cleaner than a `Sum Unit (Fin n)` encoding.

### What Would a Proof Need?

- `dirichletSetN_symmetric α Q : ∀ v ∈ dirichletSetN α Q, -v ∈ dirichletSetN α Q`
  — by `Pi.neg_apply` + `abs_neg`, ~5 lines per inequality.
- `dirichletSetN_measurable α Q : MeasurableSet (dirichletSetN α Q)`
  — rewrite as `Set.iInter` of preimages of `Ioo` under continuous
  maps; apply `IsOpen.measurableSet` once.
- `dirichletSetN_convex α Q : Convex ℝ (dirichletSetN α Q)`
  — rewrite as `Set.iInter` of preimages of `Ioo` under linear maps;
  `Convex.iInter` over `Fintype (Fin n)`.
- `dirichletSetN_volume α Q : volume (dirichletSetN α Q) = ENNReal.ofReal (2^(n+1) * (Qⁿ + 1) / Qⁿ)`
  — shear map + `volume_pi_Ioo` + `Fin.prod_univ_succ`.
- `simultaneous_dirichlet_from_minkowski`: assemble via
  `minkowski_integer_lattice_proved`, extract integer coordinates via
  `Submodule.mem_span_range_iff_exists_fun`, conclude.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- All techniques exist and have been used in `OQ-02-OQ-01.lean`.
- The shear determinant for the lower-triangular form is standard
  Mathlib (`Matrix.det_of_lowerTriangular` or a manual cofactor
  expansion).
- The main `Minkowski → Dirichlet n` extraction step parallels the 1D
  case exactly.
- Risk lies in the `Fin (n+1)` indexing bookkeeping (matrix entries,
  shear inverse, Set.pi rewrite).

**Estimated Effort**:
- Exploration: ~2 sessions (this one + S2 ORIENT)
- If tractable: 4–6 sessions (S3 measurability / S4 convexity / S5
  shear + volume / S6 main theorem assembly / S7 axiom-free finish)
- Risk: shear determinant lemma availability and Fin-indexing
  ergonomics

## References

### Papers
- **Hermann Minkowski (1896)**, *Geometrie der Zahlen*, Leipzig — original
  source of the simultaneous Dirichlet derivation.
- **John W.S. Cassels (1957)**, *An Introduction to the Geometry of
  Numbers*, Springer — Theorem I.II.A (Chapter I, §2.A) gives the
  simultaneous Dirichlet derivation via the box
  `|x| ≤ Qⁿ, |αᵢx − pᵢ| ≤ 1/Q`, which we follow in Approach A.

### Online Resources
- Wikipedia: "Dirichlet's approximation theorem" §"Simultaneous version"
- Wolfram MathWorld: "Dirichlet's Approximation Theorem"

### Mathlib
- `Mathlib.MeasureTheory.Group.GeometryOfNumbers` —
  `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
- `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar` —
  `map_matrix_volume_pi_eq_smul_volume_pi` (shear / linear-map volume)
- `Mathlib.Analysis.Convex.Basic` — `convex_Ioo`, `Convex.iInter`
- `Mathlib.Topology.Order` — `isOpen_Ioo`, `IsOpen.measurableSet`
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` —
  `Matrix.det_of_lowerTriangular` (or cofactor expansion fallback)

## Metadata

```yaml
tags:
  - number-theory
  - geometry
  - lattice
  - diophantine-approximation
  - geometry-of-numbers
related_proofs:
  - minkowski-theorem-oq-02
  - minkowski-theorem-oq-02-oq-01
  - minkowski-fundamental-theorem
difficulty: medium
source: seeker
created: 2026-05-12
```
