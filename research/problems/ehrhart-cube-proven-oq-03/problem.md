# ehrhart-cube-proven-oq-03: Barvinok's Algorithm for Lattice Point Counting

## Slug Origin

Seeker-selected, tier B, significance 7, tractability 4.

**Pool entry name**: "Barvinok's algorithm for lattice point counting in fixed dimension".

**Pool notes**: "Formalize Barvinok's polynomial-time algorithm for
computing the lattice point count of a rational polytope in fixed
dimension d. Requires rational generating functions, short rational
function evalua[tion]…"

Tags: `seeker-selected`, `combinatorics`, `ehrhart-theory`,
`polytopes`, `lattice-points`, `barvinok`, `algorithms`.

## Restated Goal

Add a NEW gallery entry that

1. States **Barvinok's theorem** (1994): for every fixed dimension
   `d`, there is an algorithm that on input a rational polytope
   `P ⊆ ℝᵈ` (given by `m` inequalities with rational coefficients of
   bit-length `≤ L`) computes `#(P ∩ ℤᵈ)` in time
   `poly(m, L)`.

2. Lays out the building blocks: (a) **rational generating functions**
   `f(P; x) = ∑_{α ∈ P ∩ ℤᵈ} x^α` and short-rational-function form via
   simplicial cone decomposition; (b) **signed-simplicial decomposition**
   of a cone into cones of bounded index; (c) **specialisation
   `x → 1`** giving the lattice-point count.

3. Provides at least one **non-trivial corollary** the existing
   `ehrhart-cube-proven*` family does not have, such as:
   - polynomial-time formula for `#([0, n]ᵈ ∩ ℤᵈ) = (n + 1)ᵈ` via short
     rational generating function (sanity-check identity);
   - Brion's formula for the generating function of a lattice polytope
     `P` as the sum over vertices `v` of the generating function of the
     tangent cone at `v` — provable in special cases via Mathlib's
     `Polynomial.exp`-like machinery;
   - Barvinok's signed decomposition for the 2-D case (`d = 2`),
     achievable in 200–400 Lean lines.

## What the Gallery Already Has

| Slug                                | Status    | Notes                                                                                  |
|-------------------------------------|-----------|----------------------------------------------------------------------------------------|
| `ehrhart-cube-proven`               | verified  | First-principles `L([0,1]ᵈ, n) = (n+1)ᵈ`, 296 lines, 26 theorems, 0 axioms, 0 sorries. |
| `ehrhart-cube-proven-oq-01`         | varies    | Sibling — see meta.json (not surveyed in S1).                                          |
| `ehrhart-cube-proven-oq-02`         | COMPLETED | "Ehrhart Polynomials Without General Existence Theorem"                                |
| `ehrhart-cube-proven-oq-04`         | PROVED    | Eulerian h*-vector identity for `[0,1]ᵈ`, Worpitzky + palindrome.                      |

**Gap**: no entry addresses the **algorithmic complexity** of lattice-point counting.
Barvinok-1994 is the canonical result; signed simplicial-cone decomposition is a
genuinely new gallery direction.

## Plain Statement

(To be sharpened in S2.)

**Barvinok 1994 (informal).**  For every fixed `d ∈ ℕ`, there exists a
deterministic polynomial-time algorithm `B_d` such that on input

- a rational polytope `P = { x ∈ ℝᵈ : Ax ≤ b }` with `A ∈ ℚ^{m×d}`,
  `b ∈ ℚᵐ`, all coefficients of bit-length `≤ L`,

`B_d(A, b)` outputs `|P ∩ ℤᵈ| ∈ ℕ` in time `poly(m, L)`.

The bound on `d` is essential: with `d` as part of the input, even
deciding whether `P ∩ ℤᵈ ≠ ∅` is NP-hard (integer programming).

## Tractability

**4/10 from-scratch** for the full polynomial-time bound (requires
complexity-theoretic infrastructure that Mathlib lacks).
**7/10 for the structural-decomposition core** (signed-cone sum,
rational generating function statement, specialisation to lattice
count) — this is the realistic S2/S3 target.

## Constraints

- **Path**: full.
- **No fast-track from Mathlib alone**: Mathlib has Ehrhart theory
  (`Mathlib.Combinatorics.Polytope.Ehrhart`) and `MvPowerSeries` /
  `RatFunc` but **does not** formalise Barvinok-style short rational
  functions or signed cone decompositions (as of v4.26.0 — verify in
  S2 probe).
- **File-size**: target ≤ 400 lines for the S2 deliverable; the
  algorithm's complexity argument is deferred to S3+.

## Why This Slug Is Non-Redundant

- `ehrhart-cube-proven-oq-01/02/04` all address **identity-type**
  statements (specific cubes, h*-vectors, recursions).
- **OQ-03** addresses an **algorithmic / generating-function** angle
  orthogonal to those.
- Barvinok's signed-cone decomposition produces a **succinct
  representation** of `f(P; x)` that the existing gallery does not
  define.  Even a partial formalisation (S2 statement-only, S3
  signed-cone construction in 2-D, S4 polytime claim as `axiom`) is a
  genuine additive contribution.

## References (S1)

- Barvinok, A. I. (1994) "A polynomial time algorithm for counting
  integral points in polyhedra when the dimension is fixed."
  *Math. Oper. Res.* **19**, 769–779.
- Barvinok, A. & Pommersheim, J. E. (1999) "An algorithmic theory of
  lattice points in polyhedra." *New Perspectives in Algebraic
  Combinatorics* (MSRI), 91–147.
- De Loera, J. A., Hemmecke, R., Tauzer, J., Yoshida, R. (2004)
  "Effective lattice point counting in rational convex polytopes."
  *J. Symb. Comp.* **38**(4), 1273–1302.  (LattE software.)
- Beck, M. & Robins, S. (2015) *Computing the Continuous Discretely*,
  2nd ed., Springer UTM, ch. 11.
- Mathlib4 `Mathlib.Combinatorics.Polytope.Ehrhart` (existing v4.26.0).

## Open Decisions

- **Naming convention**: file `Proofs/EhrhartCubeProvenOQ03.lean`,
  gallery dir `src/data/proofs/ehrhart-cube-proven-oq-03/`.
- **First S2 corollary**: Barvinok-style short generating function for
  `[0, n]ᵈ` (cube) — already known to equal
  `∏ᵢ (1 − xᵢⁿ⁺¹) / (1 − xᵢ)`.  Provable as a thin wrapper around
  geometric series in Mathlib.  Acts as a sanity test for the L-W of
  the file's framework.
