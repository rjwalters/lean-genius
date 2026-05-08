# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (axiom revision applied)
**Path**: full
**Since**: 2026-05-08T17:30:00Z
**Iteration**: 7

## Current Focus
S7 (researcher-6, 2026-05-08): **Implements the S6 next-action.**
Revises `approx_selection_exists` from the (false) pointwise form to
the (provable) Cellina–Browder graph form, and re-threads
`kakutani_from_brouwer` through one triangle-inequality step.

Concretely (single file `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`):

  1. **Adds** `IsGraphApproxSelection` def: graph-form approximate selection.
  2. **Restates** the axiom `approx_selection_exists` to assert the
     graph form rather than the (false) pointwise form.
  3. **Patches** `kakutani_from_brouwer`:
     - request `(ε/2)`-graph approximate selection from the axiom;
     - apply Brouwer to get `x₀ = f(x₀)`;
     - graph property gives `x' ∈ S, y ∈ F(x')` with `dist(x₀, x') < ε/2`
       and `dist(f(x₀), y) < ε/2`;
     - triangle inequality: `dist(x', y) ≤ dist(x', x₀) + dist(x₀, y) < ε`.
  4. **Updates** docstrings to cite Cellina–Browder and document the
     S6 → S7 history.

Counts: 2 axioms, 0 sorries. Helper `approx_fixedpoint_implies_fixedpoint`
unchanged. Build pending; new triangle-inequality step uses only
`linarith`/`ring`/`dist_triangle`/`dist_comm`.

## Active Approach
S7 is the *axiom-side* salvage promised in S6. The remaining work is the
PartitionOfUnity proof of `IsGraphApproxSelection` itself (S8+), which is
the standard Cellina–Browder PoU construction (Aubin–Frankowska §9.2).
With S7 applied, the PoU proof now has the right TARGET — the graph form
matches what Mathlib's PoU infrastructure actually supports.

## Attempt Count
- Total attempts: 7
- Approaches tried:
  - S2 documentation (researcher-3, #16731);
  - S3 full proof submission (researcher-11, #16784);
  - S4 build verification + meta sync (researcher-10);
  - S5 PR flush off fresh main (researcher-?, content already on main);
  - S6 axiom-strength counterexample analysis (researcher-6, #17265);
  - S7 graph-form axiom + kakutani patch (researcher-6, this PR).

## Blockers
None at the math level. The remaining axioms (`brouwer_fpt`,
`approx_selection_exists`-graph-form) are both provable from Mathlib;
their proofs are S8+ work.

## Next Action
S8: prove `approx_selection_exists` (graph form) via Mathlib's
PartitionOfUnity infrastructure. Standard recipe (Cellina–Browder):

  1. For each `x ∈ S`, pick `y_x ∈ F(x)` and use USC to get a neighborhood
     `U_x ∋ x` with `F(U_x) ⊆ ε`-thickening of `F(x)`.
  2. Compactness extracts a finite subcover `U_{x_1}, ..., U_{x_k}`.
  3. Mathlib `PartitionOfUnity` gives a subordinate `{φ_i}`.
  4. Define `f(x) = Σ φ_i(x) · y_{x_i}`. Convexity of `S` ⇒ `f(x) ∈ S`.
  5. **Graph property** (the corrected step-6): for any `x'`, the support
     of `{φ_i}` at `x'` is finite; pick the `x_i` with `dist(x', x_i)`
     minimal. Then `dist(x_i, x') < ε` (it's in `U_i`'s ball), and
     `dist(f(x'), y_{x_i}) ≤ ε` (since `f(x')` is a convex combination
     of points each within `ε` of `F(x_i) ⊆ F(x_i)`-thickening),
     giving the graph form.

S9+: verify `brouwer_fpt` against Mathlib's existing
`Topology.MetricSpace.Brouwer` (extension from unit ball to general
compact convex `S` via a retraction argument; folklore-level, the
easier of the two axioms).
