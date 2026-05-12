# Problem: Shapley–Folkman extension to infinite-dim Hilbert spaces

**Slug**: shapley-folkman-oq-01
**Created**: 2026-05-12
**Status**: Active
**Source**: seeker (gallery follow-up to `shapley-folkman`)

## Problem Statement

### Formal Statement

The parent gallery proof `shapley-folkman` (`proofs/Proofs/ShapleyFolkman.lean`,
1238 lines, 0 sorries, 0 axioms) states:

```lean
theorem shapley_folkman [FiniteDimensional ℝ E]
    {N : ℕ} (S : Fin N → Set E) :
    ∀ x ∈ convexHull ℝ (∑ i, S i),
    ∃ decomposition, …,
    decomposition.excessIndices.card ≤ Module.finrank ℝ E
```

i.e. every point of the convex hull of a Minkowski sum decomposes
so that **at most `d := Module.finrank ℝ E` summands** come from
the convex hulls rather than the original sets.

**Open question (OQ-01):** drop the `[FiniteDimensional ℝ E]`
hypothesis. Either:

1. Find a "suitable dimension" replacement for `Module.finrank ℝ E`
   under which the same statement holds for infinite-dim Hilbert
   space `E`; or
2. Show that no such replacement exists, and instead formalize the
   **correct** infinite-dim analog (Aumann 1965 / Lyapunov 1940
   convexity of the range of an atomless vector measure).

### Plain Language

Shapley–Folkman says: in `d`-dim Euclidean space, the convex hull
of a sum of many sets is "approximately" the sum of the convex
hulls, with the discrepancy bounded by `d`. As you sum more sets
(`N → ∞`), the relative discrepancy `d/N → 0`, so Minkowski sums
become "asymptotically convex". The OQ-01 asks: does this story
generalize from `ℝᵈ` to an infinite-dim Hilbert space `H`? The
naive answer is **no** — `Module.finrank ℝ H = 0` for non-finite-dim
modules in Lean, breaking the bound trivially, and the geometric
content (at most `d` non-convex summands) does not have an obvious
infinite-dim replacement.

### Why This Matters

- **Economics**: Aumann (1965) used Lyapunov's convexity theorem
  to prove that markets with a continuum of agents have convex
  aggregate excess-demand sets. This is the infinite-dim analog
  of Shapley–Folkman that economists actually use.
- **Convex analysis**: Lyapunov's theorem (range of an atomless
  ℝⁿ-valued measure is convex and compact) is the bridge from
  finite-dim Shapley–Folkman to infinite-dim convexification
  results.
- **Lean status**: Mathlib has the building blocks (`MeasureTheory.IsAtom`,
  vector-valued integration, infinite-dim Hilbert spaces) but
  **does not** have Lyapunov's convexity theorem at the theorem
  level. The honest infinite-dim extension would either (a) drop
  the goal entirely with a "no naive extension" survey, or
  (b) state and try to prove Lyapunov, the much harder upstream
  result.

## Known Results

### What's Already Proven (parent + Mathlib)

- **Parent `shapley-folkman` (verified)**:
  `shapley_folkman` at `ShapleyFolkman.lean:1140` with
  `[FiniteDimensional ℝ E]`, 0 sorries, 0 axioms.
- **Mathlib (finite-dim)**:
  - `Convex.Carathéodory` (`Mathlib.Analysis.Convex.Caratheodory`):
    every point of `convexHull s` in `ℝᵈ` is a convex combination
    of at most `d+1` points of `s`.
  - `AffineIndependent` over `ℝ` requires `Module.finrank` to
    obtain the dimension bound.
- **Mathlib (infinite-dim, partial)**:
  - `MeasureTheory.MeasureSpace.IsAtom` and related
    atomless-measure-space API.
  - `MeasureTheory.lintegral` / `integral` for vector-valued
    integration into Banach spaces, but
  - **Lyapunov's convexity theorem is NOT in Mathlib** (verified
    by `grep -rn "Lyapunov\|lyapunov" mathlib_path/.lake`).
    No `convex_range_atomless_vector_measure` lemma.
  - `Convex.iInter` and `Convex.add` work in arbitrary topological
    vector spaces.

### What's Still Open

1. **Does the literal `Module.finrank ℝ E` bound make sense for
   `E = ℓ²`?** No — `Module.finrank ℝ ℓ² = 0` in Lean's convention
   for non-finite-dim modules, which makes the bound `0` and the
   conclusion trivial (every point would need 0 excess indices,
   which is generally impossible).

2. **Is there a "spread" or "Ekeland" replacement?**
   In Ekeland and Témam's *Convex Analysis and Variational Problems*
   (1976, §I.4 Remark 4.10), an infinite-dim version of
   Shapley–Folkman is stated using the notion of a Banach space
   with finite "non-convexity index"; but this remains a
   finite-dimensional concept smuggled through the Loewner
   ellipsoid of the unit ball.

3. **What CAN be formalized?**
   - **Aumann (1965) "Integrals of Set-valued Functions"**:
     for an atomless measure space `(Ω, μ)` and a measurable
     `F : Ω → Set H` (set-valued), `∫ F dμ` is convex.
   - **Lyapunov's convexity theorem (finite-dim range)**:
     for an atomless `μ : MeasureSpace Ω` and a vector measure
     `m : Σ → ℝⁿ`, `range m` is convex and compact in `ℝⁿ`.
   - **Hilbert-space (sometimes-true) replacement**: for an
     equi-convex family of subsets in a separable Hilbert space,
     the "average" approaches its convex hull in Hausdorff
     distance — but no clean theorem-level statement.

### Our Goal

Produce an honest doc-only S1 OBSERVE that:

- **Confirms** the literal `finrank ℝ E` extension is vacuous /
  false in infinite dim;
- **Maps** the three viable correct-but-different infinite-dim
  analogs (Aumann's set-valued integral / Lyapunov vector measure /
  Ekeland's non-convexity index);
- **Shortlists** 2-3 narrow S2 ACT targets, prioritizing the most
  Mathlib-ready one.

## Related Gallery Proofs

| Proof                       | Relevance                                    | Techniques                                      |
|-----------------------------|----------------------------------------------|-------------------------------------------------|
| `shapley-folkman`           | Direct finite-dim parent                     | Carathéodory + dimension counting (`finrank`)   |
| `shapley-folkman-oq-03`     | Related sub-OQ (203 lines, currently OQ-03)  | (different angle)                               |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Honest negative result + scope narrowing (recommended)**

   Document the obstruction (`Module.finrank ℝ ℓ² = 0` collapses
   the bound), survey the three viable alternatives (Aumann /
   Lyapunov / Ekeland), and pick one narrow S2 ACT target:
   typically a Mathlib formalization of one direction of
   Lyapunov's theorem for a 2-dim vector measure
   (`m : Σ → ℝ²`) — the smallest case where convexity is non-trivial.

   **Why it might work**: matches the gallery's "honesty standards"
   (do not overstate; small concrete steps).

   **Risk**: Lyapunov's full proof requires the Halmos–Lyapunov
   bang-bang principle, ~200-300 lines of measure-theoretic
   machinery not in Mathlib.

2. **Approach B — Σ-finite atomless probability variant**

   Restrict to atomless probability spaces `(Ω, μ)` with
   `μ(Ω) = 1`, and state Aumann's integral-of-set-valued-functions
   convexity for `F : Ω → Set ℝᵈ`. This still needs Lyapunov
   internally but the statement is cleaner.

   **Why it might work**: Aumann's theorem is the named result
   directly used in economic applications.

   **Risk**: same Lyapunov prerequisites.

3. **Approach C — Negative shapley-folkman counter-example in `ℓ²`**

   Construct an explicit `S : ℕ → Set ℓ²` and a point in
   `convexHull ℝ (∑ Sᵢ)` that admits NO Shapley-Folkman-style
   decomposition with bounded excess count — formalize this as a
   `theorem shapley_folkman_fails_in_infinite_dim`.

   **Why it might work**: a single negative example is much
   cheaper than the full Lyapunov machinery.

   **Risk**: constructing an explicit `ℓ²` counter-example is
   not entirely trivial; might require an infinite sequence of
   pairwise-orthogonal segments.

### Key Difficulties

- The "obvious" Lean-side obstruction (`finrank = 0` in infinite
  dim) is a formalization artifact rather than a deep theorem;
  the real geometric content requires choosing the right
  alternative dimension notion or stating Lyapunov-style results.
- Lyapunov's convexity theorem is non-trivial (~200-300 lines)
  and not currently in Mathlib.
- The seeker note "finrank → suitable dimension" suggests the
  question-poser may not have realized that no such
  drop-in replacement exists.

### What Would a Proof Need?

For Approach C (negative result, narrowest):

- An explicit `S : ℕ → Set ℓ²` (e.g. `S i = {0, eᵢ}`) where
  `eᵢ` is the i-th standard basis vector.
- The Minkowski sum `∑ᵢ Sᵢ` consists of all sums of distinct
  basis vectors, hence is a subset of `ℓ²` with `‖·‖² = (# summands)`.
- A point `x ∈ convexHull ℝ (∑ᵢ Sᵢ)` with `x = (1/2) ∑ᵢ eᵢ`
  requires every `Sᵢ` to contribute non-trivially, but each
  contribution must be `(1/2) eᵢ ∈ conv {0, eᵢ}` — so **every**
  index is an "excess index". No finite-`d` bound holds.

This negative result is ~50–100 lines of Lean using `EuclideanSpace ℝ ℕ`
or `ℓ²` from Mathlib's `Analysis.InnerProductSpace.l2Space`.

## Tractability Assessment

**Difficulty**: Medium (Approach C — negative example) /
High (Approach A/B — Lyapunov upstream).

**Justification**:
- Approach C is concrete and Mathlib has all required APIs
  (`EuclideanSpace`, basis-vector definitions, convex hulls).
- Approach A/B require Lyapunov's theorem, which is a multi-session
  formalization project on its own.

**Estimated Effort**:
- Exploration: 1–2 sessions (this S1 OBSERVE counts as one).
- Approach C: 3–4 sessions (state + prove the `ℓ²` counter-example;
  add a positive Hausdorff-distance-style fallback if time permits).
- Approach A/B: 8+ sessions (Lyapunov as a prerequisite).

## References

### Papers

- **Hugo Steinhaus, Lloyd Shapley, Jon Folkman (1959, unpublished)** —
  original finite-dim observation; first appearance in Starr (1969).
- **Ross M. Starr (1969)**, *Quasi-equilibria in markets with
  non-convex preferences*, Econometrica 37(1), pp. 25–38 —
  the canonical Shapley–Folkman citation.
- **Robert J. Aumann (1965)**, *Integrals of set-valued functions*,
  J. Math. Anal. Appl. 12(1), pp. 1–12 — the infinite-dim
  analog via Lyapunov's theorem.
- **A. A. Lyapunov (1940)**, *On completely additive vector-functions*,
  Izv. Akad. Nauk SSSR Ser. Mat. 4 — the convexity-of-range theorem
  underlying Aumann's result.
- **Paul Halmos (1948)**, *The range of a vector measure*,
  Bull. Amer. Math. Soc. 54(4), pp. 416–421 — bang-bang principle.
- **Ivar Ekeland & Roger Témam (1976)**, *Convex Analysis and
  Variational Problems*, North-Holland, §I.4 Remark 4.10 —
  "non-convexity index" for Banach spaces.

### Online Resources

- Wikipedia: "Shapley–Folkman lemma" (covers finite-dim only).
- Wikipedia: "Lyapunov's theorem (measure theory)".
- nLab: "Lyapunov's theorem".

### Mathlib

- `Mathlib.Analysis.Convex.Caratheodory` — Carathéodory's
  theorem (finite-dim).
- `Mathlib.Analysis.InnerProductSpace.l2Space` — `ℓ²` Hilbert
  space.
- `Mathlib.MeasureTheory.Measure.Atomic` — atomless measure
  spaces (`MeasureTheory.Measure.IsAtom`).
- **Missing**: Lyapunov's convexity theorem.
- **Missing**: Aumann's set-valued integral.

## Metadata

```yaml
tags:
  - convex-analysis
  - economics
  - hilbert-space
  - geometry
related_proofs:
  - shapley-folkman
  - shapley-folkman-oq-03
difficulty: medium
source: seeker
created: 2026-05-12
```
