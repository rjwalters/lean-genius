# Problem: Blichfeldt's Theorem for an Arbitrary Full-Rank Lattice Λ (Covolume Threshold)

**Slug**: minkowski-theorem-oq-04-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $\Lambda \subseteq \mathbb{R}^n$ be a full-rank $\mathbb{Z}$-lattice (a discrete cocompact
additive subgroup, equivalently $\Lambda = \operatorname{span}_{\mathbb{Z}}(b)$ for some
$\mathbb{R}$-basis $b$ of $\mathbb{R}^n$), with covolume $V = \operatorname{covol}(\Lambda)$
(the Lebesgue measure of any fundamental domain). Then:

$$
S \subseteq \mathbb{R}^n \text{ measurable}, \quad \operatorname{vol}(S) > k\cdot V
\;\Longrightarrow\;
\exists\, x_0,\dots,x_k \in S \text{ distinct}, \; \forall i,j:\; x_i - x_j \in \Lambda.
$$

The $k = 1$ case is: $\operatorname{vol}(S) > V \Rightarrow \exists\, x \ne y \in S$ with
$x - y \in \Lambda$. The current gallery entry proves exactly the $\Lambda = \mathbb{Z}^n$,
$V = 1$ specialization; this child removes that normalization.

### Plain Language

Blichfeldt's theorem says that if a measurable set in $\mathbb{R}^n$ is "big enough," it must
contain several points that are all congruent to each other modulo the integer lattice
$\mathbb{Z}^n$. The threshold for "big enough" (to force $k+1$ mutually congruent points) is
volume $> k$, because the integer lattice tiles space by unit-volume cubes. For a general
lattice $\Lambda$ the tiles are the (skewed) fundamental parallelepipeds, each of volume $V =
\operatorname{covol}(\Lambda)$, so the natural threshold becomes volume $> k\cdot V$. The task
is to prove Blichfeldt's pigeonhole with this scaled threshold for an arbitrary full-rank
lattice.

### Why This Matters

The integer-lattice statement is a special case; the geometry-of-numbers literature (Cassels,
Siegel) always states Blichfeldt for a general lattice, since applications (Diophantine
approximation, transference theorems, ideal-lattice bounds in algebraic number theory) require
lattices that are not $\mathbb{Z}^n$ — e.g. the Minkowski embedding of a ring of integers,
whose covolume is $2^{-r_2}\sqrt{|d_K|}$. A covolume-parametric Blichfeldt is the clean
building block for a covolume-parametric Minkowski convex body theorem
($\operatorname{vol}(S) > 2^n V \Rightarrow$ nonzero lattice point), which is the form used in
essentially every number-theoretic application.

## Known Results

### What's Already Proven

- **Parent gallery entry** (`minkowski-theorem-oq-04`, `Proofs/MinkowskiTheoremOQ04.lean`,
  verified, 0 axioms): full Blichfeldt for $\Lambda = \mathbb{Z}^n$. Key proved theorems:
  - `blichfeldt_basic` ($k=1$) via `IsAddFundamentalDomain.exists_ne_zero_vadd_eq`.
  - `volume_eq_setLIntegral_indicator_tsum` — the covering-count identity
    $\int_F \sum'_{g}\, \mathbf 1_S((g:\mathbb{R}^n)+x)\,dx = \operatorname{vol}(S)$ for
    $\mathbb{Z}^n$.
  - `blichfeldt_general` (general $k$) via the Path A contrapose route (Moves A/B/C).
- **Already present in the parent file, lattice-parametric** (crucial head start):
  `volume_eq_setLIntegral_indicator_tsum_lattice` — the covering-count identity **for an
  arbitrary basis** `b : Module.Basis (Fin n) ℝ (Fin n → ℝ)`, integrating over
  `ZSpan.fundamentalDomain b` over the submodule `Submodule.span ℤ (Set.range b)`, proved from
  `ZSpan.isAddFundamentalDomain' b volume` + `lintegral_tsum` (Tonelli). This is Move A already
  generalized. So the analytic engine is done; only Moves B/C need re-parametrizing.
- **Mathlib** (verify names against the pinned v4.26.0 SHA `2df2f01...`):
  - `MeasureTheory.IsAddFundamentalDomain` and `IsAddFundamentalDomain.lintegral_eq_tsum''`
    (the additive covering-count identity used in Move A). (verify exact prime count)
  - `ZSpan.fundamentalDomain`, `ZSpan.isAddFundamentalDomain' b volume` — the half-open
    parallelepiped fundamental domain of a basis and its fundamental-domain property.
  - `ZLattice.covolume` (`Mathlib.Algebra.Module.ZLattice.Covolume`): defined as
    `(addCovolume L E μ).toReal : ℝ`, i.e. the **real** volume of a fundamental domain.
  - `ZLattice.covolume_eq_measure_fundamentalDomain` :
    `covolume L μ = μ.real F` for any `IsAddFundamentalDomain L F μ`.
  - `IsAddFundamentalDomain.covolume_eq_volume` (the ENNReal-level statement that
    `volume F` is independent of the fundamental domain). (verify)
  - `MeasureTheory.setLIntegral_mono_ae`, `setLIntegral_const`, `lintegral_indicator_const`
    (Move C integration steps).
  - `ENNReal.tsum_set_one`, `tsum_subtype`, `Set.toFinset_card`,
    `Fintype.equivFinOfCardEq` (Move B extraction, reused verbatim).

### What's Still Open

The child theorem itself: assemble a `blichfeldt_general_lattice` (and its $k=1$ corollary)
stating $\operatorname{vol}(S) > k\cdot V \Rightarrow k+1$ pairwise-$\Lambda$-congruent points,
where $V$ is the lattice covolume, and derive it for a general full-rank $\Lambda$. The parent
file's docstrings explicitly flag this as the intended PR-B (`blichfeldt_general_lattice`) /
PR-C (`minkowski_general_k_lattice`) follow-up.

### Our Goal

Prove `blichfeldt_general_lattice` for an arbitrary basis `b` (hence for an arbitrary full-rank
$\mathbb{Z}$-lattice via `Submodule.span ℤ (Set.range b)`), with the threshold expressed as
`(k : ENNReal) * volume (ZSpan.fundamentalDomain b) < volume s` (or equivalently via
`ZLattice.covolume`). Deliver the $k=1$ corollary and, if cheap, the covolume-Minkowski
corollary `minkowski_general_k_lattice`. Ship as a NEW child file/entry (do not mutate the
verified parent), importing the parent for the already-proved lattice-parametric identity.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `minkowski-theorem-oq-04` (parent) | Provides `volume_eq_setLIntegral_indicator_tsum_lattice` (Move A, already general) and the $\mathbb{Z}^n$ Moves B/C template to re-parametrize | Fundamental-domain integral identity, contrapose covering-count, Tonelli |
| `minkowski-fundamental-theorem` | Source of `stdLattice`, `stdFundDomain`, `stdLattice_covolume = 1`; the covolume-general result subsumes it | ZLattice / Zspan fundamental domain |
| `minkowski-theorem-oq-02`, `-oq-02-oq-01` | Sibling Minkowski OQs (Dirichlet approximation); consumers of a covolume-parametric Minkowski | Convexity + symmetry lattice-point extraction |

## Initial Thoughts

### Potential Approaches

1. **(Recommended) Re-parametrize the parent's Path A contrapose, swapping the covolume step.**
   The parent's `volume_eq_setLIntegral_indicator_tsum_lattice` already gives Move A for a
   general basis. Copy `blichfeldt_general`'s Moves B and C almost verbatim, replacing:
   - `stdLattice n` → `Submodule.span ℤ (Set.range b)` (its `.toAddSubgroup`),
   - `stdFundDomain n` → `ZSpan.fundamentalDomain b`,
   - the terminal `stdLattice_covolume : volume (stdFundDomain n) = 1` → a generic
     `volume (ZSpan.fundamentalDomain b) = V` fact (either kept symbolic as `V` or discharged
     via `ZLattice.covolume` / `covolume_eq_measure_fundamentalDomain`).

   Move C then yields `volume s ≤ k * volume F = k * V`, contradicting the hypothesis
   `k * V < volume s`. Move B (the `Fin (k+1)` extraction from the encard bound) is
   lattice-agnostic and transfers unchanged.
   - Why it might work: the hardest analytic step (Move A) is already proved in general in the
     parent; the only genuinely new line is the covolume substitution in Move C.
   - Risk: Mathlib API drift on `ZSpan.isAddFundamentalDomain'` / `lintegral_eq_tsum''` prime
     count, and ENNReal↔ℝ bookkeeping for `ZLattice.covolume`.

2. **Pull back to $\mathbb{Z}^n$ via the basis linear map.** Use the linear iso $B:\mathbb{R}^n
   \to \mathbb{R}^n$ sending $\mathbb{Z}^n$ to $\Lambda$, apply the parent $\mathbb{Z}^n$
   result to $B^{-1}(S)$, and push forward.
   - Why it might work: reuses the finished $\mathbb{Z}^n$ theorem as a black box.
   - Risk: requires the change-of-variables volume scaling
     $\operatorname{vol}(B^{-1}S) = \operatorname{vol}(S)/|\det B|$ and $V = |\det B|$
     (`ZLattice.covolume_eq_det`), adding a Jacobian/`Measure.map` layer and det bookkeeping —
     more moving parts than Approach 1. Keep as fallback.

Recommend **Approach 1**: it reuses the already-general Move A, keeps Move B untouched, and
isolates all new work to the single covolume line in Move C.

### Key Difficulties

- **Threshold representation.** `ZLattice.covolume` lives in $\mathbb{R}$ (`.toReal`), while the
  parent's inequalities live in `ENNReal` (`volume s`, `k * volume F`). Cleanest to state the
  hypothesis directly as `(k : ENNReal) * volume (ZSpan.fundamentalDomain b) < volume s` and
  only bridge to `ZLattice.covolume` in a corollary via
  `covolume_eq_measure_fundamentalDomain` + `Measure.real` (`ENNReal.toReal`), handling
  finiteness (`volume F ≠ ∞`, true for a bounded fundamental domain).
- **Choosing / naming the fundamental domain for arbitrary $\Lambda$.** A bare "full-rank
  lattice $\Lambda$" needs a fundamental domain to run the argument. The clean Mathlib handle is
  to parametrize by a **basis** `b` and use `ZSpan.fundamentalDomain b` +
  `ZSpan.isAddFundamentalDomain' b volume`; then $\Lambda = \operatorname{span}_{\mathbb Z}
  (\operatorname{range} b)$. If a version stated over an abstract `ZLattice` `L` is wanted, one
  must invoke `ZLattice.module.free`/`Free.chooseBasis` to obtain a basis first.
- **Measurability under the general fundamental domain.** The parent's `h_shift_meas_vadd` and
  indicator-measurability transfer directly (already done in
  `volume_eq_setLIntegral_indicator_tsum_lattice`); confirm no `stdFundDomain`-specific
  `measurableSet` lemma leaks into Moves B/C.
- **Countability of $\Lambda$.** The parent uses `haveI : Countable (stdLattice n).toAddSubgroup`.
  The general analogue is `Countable (Submodule.span ℤ (Set.range b))` (discrete lattice);
  `volume_eq_setLIntegral_indicator_tsum_lattice` already discharges this via `infer_instance`.
- **The a.e. covering-count pigeonhole over a general domain.** Move C's `setLIntegral_mono_ae`
  + `setLIntegral_const` step is domain-agnostic once `volume F` is the constant; no new a.e.
  subtlety beyond the parent's, provided `volume F` is finite (needed for the `const` integral
  to be `k * volume F`).

### What Would a Proof Need?

- Key lemma 1: `blichfeldt_general_lattice (b) (k) (s) (h_meas) (h_vol : (k:ENNReal) * volume
  (ZSpan.fundamentalDomain b) < volume s)` with the `Fin (k+1) → ℝⁿ` injective /
  pairwise-in-Λ conclusion. Move A = cite existing
  `volume_eq_setLIntegral_indicator_tsum_lattice b h_meas`.
- Key lemma 2: Moves B/C copied from `blichfeldt_general`, substituting lattice/domain names;
  the only genuine edit is replacing `rw [stdLattice_covolume]` with the symbolic `volume F`
  (kept as-is on both sides — it need not even be evaluated, since the threshold already carries
  `volume F`).
- Corollaries: $k=1$ (`blichfeldt_basic_lattice`) and, optionally,
  `minkowski_general_k_lattice` via half-scaling + covolume (may be deferred to a further child
  if it balloons).
- Technical requirements: a covolume-phrased restatement using `ZLattice.covolume` for the
  gallery-facing statement; finiteness of `volume (ZSpan.fundamentalDomain b)`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- This is a genuine generalization but with an unusually strong head start: the hardest analytic
  step (Move A, the covering-count integral identity) is **already proved in general** in the
  parent file as `volume_eq_setLIntegral_indicator_tsum_lattice`.
- Move B is lattice-agnostic and copies verbatim; the only real new content is Move C's covolume
  line plus ENNReal/ℝ bookkeeping around `ZLattice.covolume`.
- Main risks are Mathlib API drift (exact names of `ZSpan.isAddFundamentalDomain'`, the
  `lintegral_eq_tsum''` prime count, `covolume` finiteness lemmas) and stating the threshold
  cleanly — not a research-level obstacle, but careful re-plumbing of a verified proof.

**Estimated Effort**:
- Exploration: a few hours to confirm the Mathlib `ZLattice.covolume` / `ZSpan.fundamentalDomain`
  API at the pin.
- If tractable: 1–2 focused sessions, ~150–250 Lean lines for `blichfeldt_general_lattice` +
  $k=1$ corollary + covolume restatement, reusing the parent's Move B/C skeleton.
- If hard: +1 session if `minkowski_general_k_lattice` (half-scaling for a general lattice) is
  included.

## References

### Papers
- Blichfeldt, H. F. (1914). *A new principle in the geometry of numbers, with some
  applications.* Trans. Amer. Math. Soc. 15(3), 227–235. — Original; stated for a general
  lattice.
- Cassels, J. W. S. (1959). *An Introduction to the Geometry of Numbers*, Ch. III. Springer. —
  General-lattice Blichfeldt and its relation to Minkowski.
- Siegel, C. L. (1989). *Lectures on the Geometry of Numbers.* Springer. — Covolume /
  fundamental-domain formulation.
- Gruber, P. M. & Lekkerkerker, C. G. (1987). *Geometry of Numbers*, 2nd ed., Ch. 6.
  North-Holland. — Measure-theoretic detail.

### Online Resources
- https://en.wikipedia.org/wiki/Blichfeldt%27s_theorem — Blichfeldt's theorem (general-lattice
  statement).
- Mathlib docs for `MeasureTheory.IsAddFundamentalDomain` and `ZLattice.covolume`.

### Mathlib
- `MeasureTheory.IsAddFundamentalDomain` — fundamental-domain structure.
- `MeasureTheory.IsAddFundamentalDomain.lintegral_eq_tsum''` — covering-count integral identity
  (additive form; verify exact prime count at the v4.26.0 pin).
- `ZSpan.fundamentalDomain`, `ZSpan.isAddFundamentalDomain'` — basis fundamental domain and its
  fundamental-domain property. (verify exact name `isAddFundamentalDomain'`)
- `ZLattice.covolume`, `ZLattice.covolume_eq_measure_fundamentalDomain`,
  `IsAddFundamentalDomain.covolume_eq_volume` (`Mathlib.Algebra.Module.ZLattice.Covolume`).
  (verify last name)
- `ZLattice.covolume_eq_det` — covolume equals `|det b|` (for Approach 2 / det bridge).
- `MeasureTheory.setLIntegral_mono_ae`, `MeasureTheory.setLIntegral_const`,
  `MeasureTheory.lintegral_indicator_const`, `MeasureTheory.lintegral_tsum`.
- `ENNReal.tsum_set_one`, `tsum_subtype`, `Set.toFinset_card`, `Fintype.equivFinOfCardEq`
  (Move B extraction, reused).
- `MeasureTheory.Measure.addHaar_smul` — for the optional Minkowski half-scaling corollary.

## Metadata

```yaml
tags:
  - number-theory
  - geometry-of-numbers
  - lattice
  - blichfeldt
related_proofs:
  - minkowski-theorem-oq-04
difficulty: medium
source: gallery-gap
created: 2026-06-30
```
