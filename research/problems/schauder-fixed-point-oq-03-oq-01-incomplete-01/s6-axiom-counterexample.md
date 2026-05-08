# S6 Analysis — `approx_selection_exists` is false as stated

**Researcher**: researcher-6
**Date**: 2026-05-08
**Status**: Mathematical finding, no Lean changes (axiom remains pending revision)

## Summary

The S4-verified file `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` posits two axioms:
1. `brouwer_fpt` — Brouwer's FPT for compact convex `S ⊆ EuclideanSpace ℝ (Fin n)`.
2. `approx_selection_exists` — for an upper-hemicontinuous (UHC) `F : ↥S → 2^↥S` with
   nonempty convex values and any `ε > 0`, there exists a continuous
   `f : ↥S → ↥S` such that `IsApproxSelection F f ε` holds **pointwise**.

The S4 next-action proposed proving axiom 2 from `Mathlib.Topology.PartitionOfUnity`
("Cellina-style partition-of-unity averaging"). **This S6 analysis shows that
the pointwise statement is FALSE under the listed hypotheses, so the proposed
PartitionOfUnity proof cannot succeed.** The salvage path — weaken the axiom
to its provable graph-form variant and re-thread `kakutani_from_brouwer`
through that variant — is concrete but requires a non-trivial rewrite of the
main reduction.

This finding does not invalidate Kakutani's theorem (well-known) nor the
S3+S4 work on `approx_fixedpoint_implies_fixedpoint` and the limit argument
(which are independent of the axiom's exact form). It does invalidate the
**proof strategy** chosen for `kakutani_from_brouwer` as currently stated.

## The relevant definitions, verbatim from the file

```lean
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}

def IsApproxSelection {X : Type*} [PseudoMetricSpace X]
    (F : SetValuedMap X X) (f : X → X) (ε : ℝ) : Prop :=
  ∀ x, ∃ y ∈ F x, dist (f x) y < ε
```

`IsApproxSelection F f ε` requires that **at every point `x`**, the value
`f(x)` is within `ε` of `F(x)`. This is the pointwise form, strictly stronger
than the graph form `∀ x, ∃ x', dist(x, x') < ε ∧ ∃ y ∈ F(x'), dist(f(x), y) < ε`.

## A counterexample in dimension 1

Take `n = 1`, identifying `EuclideanSpace ℝ (Fin 1) ≅ ℝ` (isometric, the
proof transfers verbatim through the homeomorphism).

Set `S := [-1, 1] ⊆ ℝ` (compact convex, nonempty). Define `F : ↥S → 2^↥S` by

| `t`            | `F(t)`     |
| -------------- | ---------- |
| `t = 0`        | `[0, 1]`   |
| `t ∈ (0, 1]`   | `{0}`      |
| `t ∈ [-1, 0)`  | `{1}`      |

### `F` satisfies every hypothesis of `approx_selection_exists`

1. **Nonempty values** (`hF_ne`): `[0,1]`, `{0}`, `{1}` are all nonempty. ✓
2. **Convex values** (`hF_convex`, after `Subtype.val`-lift): each value is a
   sub-interval of `[-1, 1] ⊆ ℝ` and intervals are convex. ✓
3. **UHC** (`hF_uhc`): we check `∀ V open, {t : F(t) ⊆ V}` is open.
   - If `V ⊇ [0, 1]`, then `F(0) = [0,1] ⊆ V`, `F(t>0) = {0} ⊆ [0,1] ⊆ V`,
     `F(t<0) = {1} ⊆ [0,1] ⊆ V`. So `{t : F(t) ⊆ V} = [-1, 1]`, open.
   - If `V ⊇ {0}` but `V ⊉ [0,1]` (so `V` misses some point of `(0,1]`),
     then `F(0) ⊄ V`. `F(t>0) = {0} ⊆ V` ✓; `F(t<0) = {1} ⊆ V` iff `1 ∈ V`.
     So `{t : F(t) ⊆ V}` is either `(0,1]` (if `1 ∉ V`) or `[-1,0) ∪ (0,1]`
     (if `1 ∈ V`). Both are open in `[-1, 1]` (subspace topology — `(0,1]`
     is `(0, 2) ∩ [-1, 1]`, `[-1, 0)` is `(-2, 0) ∩ [-1, 1]`).
   - The remaining cases are symmetric or trivial (`V` misses `0`, etc.).
   ✓ UHC holds.

(The graph of `F` is also closed, so the counterexample also rules out the
"closed graph + USC" strengthening.)

### No continuous `f : ↥S → ↥S` is a pointwise `(1/3)`-approximate selection

Suppose for contradiction such `f` exists with `ε = 1/3`.

- At any `t ∈ (0, 1]`: `IsApproxSelection` requires `∃ y ∈ {0}, dist(f(t), y) < 1/3`,
  i.e. `|f(t)| < 1/3`. So `f(t) ∈ (-1/3, 1/3)`.
- At any `t ∈ [-1, 0)`: similarly `|f(t) - 1| < 1/3`, so `f(t) ∈ (2/3, 4/3) ∩ S = (2/3, 1]`.
- At `t = 0`: `f(0)` within `1/3` of some point of `[0, 1]`, so `f(0) ∈ [-1/3, 4/3] ∩ S = [-1/3, 1]`.

Continuity at `0`:
- Right limit: `lim_{t→0⁺} f(t) = f(0)` and `f(t) ∈ (-1/3, 1/3)` for `t > 0`,
  so `f(0) ∈ [-1/3, 1/3]`.
- Left limit:  `lim_{t→0⁻} f(t) = f(0)` and `f(t) ∈ (2/3, 1]` for `t < 0`,
  so `f(0) ∈ [2/3, 1]`.

These two intervals are disjoint (`[-1/3, 1/3] ∩ [2/3, 1] = ∅`), so no such
`f(0)` exists. ∎

The same argument rules out any continuous pointwise `ε`-approximate selection
for every `ε < 1/2`. So the existential in `approx_selection_exists` fails for
this `F` at every sufficiently small `ε`.

## Why the proposed PartitionOfUnity proof cannot work

The S4-suggested proof outline (in the axiom's docstring) says:
> 1. For each `x`, pick `y_x ∈ F(x)` and use UHC to get a neighborhood `U_x`
>    where `F(U_x) ⊆ B(F(x), ε)` ...
> 4. Define `f(x) = Σ φ_i(x) · y_{x_i}` ...
> 6. By construction, `f(x)` is within `ε` of `F(x)`.

Step 6 is the gap. UHC at `xᵢ` gives `F(U_i) ⊆ ε`-thickening of `F(xᵢ)`, i.e.
`∀ x' ∈ U_i, ∀ z ∈ F(x'), dist(z, F(xᵢ)) < ε`. Reading the **other**
direction — that `y_{x_i} ∈ F(x_i)` is close to some point of `F(x')` — is
exactly *lower hemicontinuity*, not UHC. Without LHC, the chosen `y_{x_i}`
need not be near `F(x')`, and the convex combination `f(x') = Σ φ_i(x') · y_{x_i}`
need not be either. The counterexample makes this concrete: at `t = 0` and
`F(0) = [0,1]`, the natural choice `y_0 ∈ [0,1]` is "fine" only at `t = 0`
itself; the moment we step to `t > 0` the only point of `F(t) = {0}` is `0`,
and any positive `y_0` becomes "far".

This matches the literature: under USC + convex values one obtains only a
**graph approximate selection** (Cellina–Browder), not a pointwise one.

## What is actually provable, and how to repair `kakutani_from_brouwer`

### The provable graph-form selection

```lean
def IsGraphApproxSelection {X : Type*} [PseudoMetricSpace X]
    (F : SetValuedMap X X) (f : X → X) (ε : ℝ) : Prop :=
  ∀ x, ∃ x' y, dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε
```

The Cellina–Browder theorem (Cellina 1969, Browder 1968; modern reference:
Aubin–Frankowska *Set-Valued Analysis* §9.2) gives:

> Let `X` be a paracompact metric space, `Y` a Banach space, `F : X → 2^Y`
> USC with nonempty convex values. Then for every `ε > 0` there is a
> continuous `f : X → Y` whose graph is in the `ε`-neighborhood of
> `graph(F)`.

A constructive PoU proof of this *does* go through (steps 1–5 above are
correct; step 6 changes from "pointwise" to "graph", and the convex
combination conclusion follows by averaging into the `ε`-fattened graph).

### Re-threading `kakutani_from_brouwer`

The current proof uses the pointwise form **at exactly one point**: the
Brouwer fixed point `x₀ = f_ε(x₀)`, deduces `dist(x₀, F(x₀)) < ε`, and
hands `(x₀, y, hy_dist)` triples to `approx_fixedpoint_implies_fixedpoint`.

With a graph approximate selection, the analogous step gives:
`x' ∈ S, y ∈ F(x')` with `dist(x₀, x') < ε` and `dist(f_ε(x₀), y) < ε`,
hence `dist(x', y) < dist(x', x₀) + dist(x₀, f_ε(x₀)) + dist(f_ε(x₀), y) < 2ε`
(using `f_ε(x₀) = x₀`). So the diagonal property
`∀ ε > 0, ∃ x ∈ S, ∃ y ∈ F x, dist x y < ε` is recovered with `ε ↦ 2ε`,
a harmless change. **The helper `approx_fixedpoint_implies_fixedpoint`
itself is unaffected.**

In short: the `kakutani_from_brouwer` reduction is rescuable with a roughly
ten-line edit — replace the use of pointwise `IsApproxSelection` with the
graph form, and supply one triangle-inequality step.

## Recommended next steps (S7+)

1. **Replace** `IsApproxSelection` with `IsGraphApproxSelection` in the file
   (or keep both, marking the pointwise one explicitly as
   "stronger than is provable from USC alone").
2. **Restate** the axiom to assert the graph form. Update its docstring to
   cite Cellina–Browder rather than the (incorrect) pointwise sketch.
3. **Patch** `kakutani_from_brouwer` to chain `dist(x₀, x') + dist(x₀, y)`
   into the diagonal-distance hypothesis fed to
   `approx_fixedpoint_implies_fixedpoint` (with `2ε` substitution).
4. **Then** attempt the PartitionOfUnity proof of the *graph* form, which
   is the standard textbook proof and matches what Mathlib's PoU
   infrastructure actually supports.
5. (Optional, much later) — If a strengthened pointwise approximate
   selection is desired, it requires LHC of `F`, which is a non-trivial
   additional hypothesis. For Kakutani as used in game theory, the graph
   form is what's available and what's needed.

## Independent finding: Brouwer-FPT axiom is also stronger than Mathlib

Mathlib proves Brouwer's FPT only for the closed unit ball
(`Mathlib.Topology.MetricSpace.Brouwer`); the axiom `brouwer_fpt` extends
this to arbitrary nonempty compact convex sets via a homeomorphism /
retraction argument. That extension is folklore-level and provable in
Mathlib (the standard trick: any compact convex set in `ℝⁿ` is a retract
of a closed ball, and a retract of a fixed-point space has the FPP).
This is not a counterexample, just a note that *both* axioms are pending
formalization, and the Brouwer extension is the easier of the two.

## Confidence

- The counterexample is checked by hand twice; the disjoint-interval
  conclusion is elementary.
- The literature alignment (Cellina–Browder gives only the graph form
  under USC) is consistent with Aubin–Cellina, Aubin–Frankowska, and
  Repovš–Semenov.
- The `kakutani_from_brouwer` salvage uses only triangle inequality
  and is not subtle.

No Lean build was attempted in this iteration; finding is purely
mathematical and does not depend on Mathlib's current state.
