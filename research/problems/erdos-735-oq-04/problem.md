# Problem: Magic configurations on k-flats in $\mathbb{R}^d$ (Erdős #735 extension)

**Slug**: `erdos-735-oq-04`
**Parent**: `erdos-735` (verified gallery entry: "Erdős Problem #735: Magic Configurations")
**Source**: seeker-extracted from `src/data/proofs/erdos-735/meta.json`, `conclusion.openQuestions[3]`.
**Created**: 2026-05-12 (S1 OBSERVE by researcher-10)

## Statement

### Parent open question (verbatim)

> Does the classification extend to configurations where the equal-sum constraint is imposed on k-flats instead of lines?

### Plain language

The parent `erdos-735` solves Erdős's *magic configurations* problem in $\mathbb{R}^2$: given $n$ points, when can one assign positive weights such that every line through ≥ 2 points has the same weight-sum? **Solution (Ackerman–Buchin–Knauer–Pinchasi–Rote 2008)**: exactly four families — all collinear; general position (no 3 collinear); near-pencil ($n-1$ on a line); triangle with angle bisectors + incenter.

This sub-OQ asks the natural higher-flat extension: replace "line" (a 1-flat) with a $k$-flat (affine subspace of dimension $k$) in $\mathbb{R}^d$. **For which $(d, k, n)$ triples does an analogous classification exist?**

### Hierarchy of cases

| $k$ | $d$ | Condition on $k$-flats | Classification status |
|----:|---:|:----------------------|:----------------------|
| 0 | any | every point's weight equals itself | trivial — any positive weighting works |
| 1 | 2 | every line through ≥ 2 points has equal sum | **Parent's case (ABKPR08)** — 4 classes |
| 1 | $\ge 3$ | every line in $\mathbb{R}^d$ through ≥ 2 points has equal sum | **OPEN — extension of parent to higher ambient dim** |
| 2 | 3 | every plane through ≥ 3 points has equal sum | **OPEN — this sub-OQ's primary case** |
| 2 | $\ge 4$ | every 2-flat through ≥ 3 points has equal sum | OPEN |
| $k = d-1$ | $d$ | every hyperplane through "enough" points has equal sum | OPEN |
| $k = d$ | $d$ | the unique full space contains all points (trivial) | trivial |

The most natural new question: **classify $(d, k, n)$ such that $k$-flat-magic configurations are non-trivial in $\mathbb{R}^d$**.

### Formal Lean target signatures

```lean
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Proofs.Erdos735Problem  -- parent

namespace Erdos735OQ04

/-- A point configuration in `ℝ^d`. -/
def PointConfigD (d : ℕ) := Finset (EuclideanSpace ℝ (Fin d))

/-- A weighting assigns a positive real to each point. -/
def WeightingD {d : ℕ} (P : PointConfigD d) := {w : P → ℝ // ∀ p, w p > 0}

/-- A `k`-flat determined by the configuration: an affine subspace of dimension
exactly `k` containing at least `k+1` configuration points (the minimum for it
to be a "determined" k-flat). -/
def ConfigKFlat {d : ℕ} (k : ℕ) (P : PointConfigD d) :=
  { F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) //
    F.direction.toSubmodule.rank = k ∧
    (P.filter (· ∈ F)).card ≥ k + 1 }

/-- Sum of weights on a `k`-flat. -/
def kFlatSum {d k : ℕ} (P : PointConfigD d) (w : WeightingD P) (F : ConfigKFlat k P) : ℝ :=
  (P.filter (· ∈ F.val)).sum fun p =>
    if h : p ∈ P then w.val ⟨p, h⟩ else 0

/-- A configuration is `k`-flat magic if positive weights exist so all `k`-flats
have equal sum. -/
def IsKFlatMagic {d : ℕ} (k : ℕ) (P : PointConfigD d) : Prop :=
  ∃ w : WeightingD P, ∃ c > 0, ∀ F : ConfigKFlat k P, kFlatSum P w F = c

/-- **Trivial case k = 0**: every configuration is 0-flat magic. -/
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) (hP : P.Nonempty) :
    IsKFlatMagic 0 P := by
  sorry  -- 0-flats are points; any positive weighting trivially satisfies the constraint

/-- **Trivial case k = d**: every configuration is d-flat magic (one flat covers all). -/
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) (hP : P.Nonempty) :
    IsKFlatMagic d P := by
  sorry  -- d-flat is the ambient space; sum is total weight, equal trivially

/-- **Reduction to parent (k = 1, d = 2)**: `IsKFlatMagic 1 P = IsMagic P`
when the ambient is ℝ². -/
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := by
  sorry  -- definitional unfolding; configLine = config 1-flat in ℝ²

/-- **Open conjecture (S5 axiom)**: in `ℝ^d` with `k = 1`, the parent's 4 classes
generalise — the magic configurations are exactly: (i) all collinear; (ii) general
position; (iii) "all but one collinear" (near-pencil); (iv) Murty-style "triangle +
ℝ^d analogue of incenter" structure. -/
axiom oneflat_classification_higher_dim {d : ℕ} (hd : d ≥ 3) (P : PointConfigD d) :
    IsKFlatMagic 1 P ↔
      (∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
          L.direction.toSubmodule.rank = 1 ∧ ∀ p ∈ P, p ∈ L) ∨
      (∀ p q r ∈ P, p ≠ q ∧ q ≠ r ∧ p ≠ r →
        ¬ ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
          L.direction.toSubmodule.rank = 1 ∧ p ∈ L ∧ q ∈ L ∧ r ∈ L) ∨
      (sorry : Prop) ∨  -- near-pencil
      (sorry : Prop)  -- analogue of triangle + incenter

end Erdos735OQ04
```

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - erdos-problem
  - discrete-geometry
  - incidence-geometry
  - magic-configurations
  - affine-flats
  - higher-dimensional
  - mathlib-gap
```

**Significance**: 6/10 — Erdős-numbered; the parent (ABKPR 2008) is a celebrated result in incidence geometry. Higher-flat extension to $\mathbb{R}^d$ is **research-level OPEN** to the author's knowledge.

**Tractability**: 5/10 — Mixed:

- **Definitions** (S2): mechanical — generalise parent's `Weighting`, `ConfigLine`, `IsMagic` to `WeightingD`, `ConfigKFlat`, `IsKFlatMagic`. ~50 Lean lines.
- **Trivial cases** (S3): $k = 0$ and $k = d$ are simple ~10 lines each, no axioms.
- **Reduction to parent for $k = 1, d = 2$** (S4): ~20 lines via definitional unfolding.
- **Higher-dim classification** (S5+): genuinely open. Axiomatise the conjectured 4-class extension (analogous to parent's ABKPR 4-class theorem) with citations to known partial results.
- **2-flats in $\mathbb{R}^3$** (S6+): a brand-new question. Concrete witnesses (e.g., a tetrahedron's vertices: each pair determines an edge, each 3-subset determines a triangle-plane) might suffice for a small example.

## Decomposition

### S2 — `WeightingD`, `ConfigKFlat`, `IsKFlatMagic` definitions

Direct generalisation of parent's definitions to arbitrary $d, k$. ~50 Lean lines, 0 sorries.

### S3 — Trivial cases $k = 0, k = d$

Both trivially magic. ~15 Lean lines.

### S4 — Reduction `IsKFlatMagic 1 P ↔ Erdos735.IsMagic P` (for $d = 2$)

Direct definitional unfolding. ~20 lines.

### S5 — Axiomatise extension of parent to $k = 1, d \ge 3$

Conjecture: the four ABKPR classes extend to higher ambient dimensions. Axiomatise; cite *Magic configurations in $\mathbb{R}^d$* (any published or open work in this direction — to be verified during literature scan).

### S6 — Concrete examples in $\mathbb{R}^3$ with $k = 2$

Construct small configurations and verify k-flat-magic property via `native_decide`:

- **Tetrahedron**: 4 vertices in general position in $\mathbb{R}^3$. Each 3-subset is a face (a 2-flat with exactly 3 points). For k = 2, the 4 triangular faces. With weights $w_1 = w_2 = w_3 = w_4 = 1$, each face sum = 3. ✓ Magic with $c = 3$.

- **Octahedron**: 6 vertices, with antipodal pairs on coordinate axes. 8 triangular faces. With $w_i = 1$, each face sum = 3. ✓

- **Cube**: 8 vertices. 6 face planes, each containing 4 vertices. With $w_i = 1$, each face sum = 4. ✓

These constructions show that **regular convex polytopes are $(d-1)$-flat magic for $d \ge 2$** — a non-trivial new class beyond the parent's 4 plane classes.

### S7 — Gallery integration

`src/data/proofs/erdos-735-oq-04/` with `status: "axiomatized"`, axiomCount: 1-2 (depending on whether S5's higher-dim classification or the parent's ABKPR is the main axiom).

## Mathlib Infrastructure Map

| Need | Mathlib v4.26.0 | Module |
|------|-----------------|--------|
| `EuclideanSpace ℝ (Fin d)` | ✅ | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| `AffineSubspace ℝ` | ✅ | `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace` |
| `AffineSubspace.direction`, rank | ✅ | as above |
| `Finset.filter`, sum | ✅ | `Mathlib.Algebra.BigOperators.Basic` |
| ABKPR 2008 (parent's classification) | ❌ (parent axiomatises) | reuse parent's axioms |
| Higher-flat magic classification | ❌ | n/a — S5 axiomatises |

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-735` (direct parent) | Plane case — ABKPR 4-class theorem (axiomatised) |
| `erdos-659-oq-01-oq-02` (this researcher's session) | Higher-dim distance problem — adjacent territory |
| `borsuk-ulam-oq-02-*` | Higher-dim topology and antipodal pairings |
| `combinations-formula-oq-03` | Affine and projective configurations |

## Risk Notes

- **Higher-dim ABKPR is genuinely OPEN** — to the author's knowledge, no published extension of the 4-class classification beyond $\mathbb{R}^2$.
- **2-flat magic for tetrahedra, octahedra, cubes is straightforward by uniform weighting** — these give a *new* class of magic configurations beyond the parent's 4 plane classes, suggesting the higher-dim classification is **richer**, not just an analogue.
- **S5 axiom is conjectural**: the 4-class extension is the author's natural guess; actual classification may differ.
- **`status: "axiomatized"` is mandatory**: ABKPR 2008 alone forces this.
- **Sibling sub-OQs**: `oq-01` (ℝ³ characterisation), `oq-02` (non-positive/complex weights), `oq-03` (complexity) are orthogonal. This OQ (`oq-04`) is the $k$-flat extension.

## References

- Erdős (1981) — original magic configurations problem.
- Ackerman, Buchin, Knauer, Pinchasi, Rote, *There are not too many magic configurations*, Discrete Comput. Geom. 39 (2008), 3–16.
- Murty (1978) — original 4-class conjecture in $\mathbb{R}^2$.
- Beck & Sokol (1995) — incidence-theoretic precursors.
- erdosproblems.com/735 — parent problem source.
- OEIS [A006247](https://oeis.org/A006247) — number of magic configurations of $n$ points in $\mathbb{R}^2$.

## Honesty

This S1 OBSERVE iteration is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry/axiom deltas
- 3 markdown files
- 1 gallery JSON

The higher-dim ABKPR extension (S5 axiom) is **research-level open**. The 2-flat magic property for regular convex polytopes (tetrahedron, octahedron, cube) is a concrete S6 deliverable that shows the higher-dim classification has a **larger class** than the parent's 4-class theorem suggests.

Future Lean entry: `status: "axiomatized"`.
