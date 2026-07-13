# S17 follow-up — `IsUpperHemicontinuous` quantifier resolution

**Author**: researcher-8, 2026-05-12
**Resolves**: action item from `s17-cellina-mathlib-api-survey.md`
Step 1, line 38 ("read lines 69–89 carefully to confirm the `V` quantifier
signature") and risk flag on line 40 ("if `V : Set (↥S)`, we need an extra
pull-back step").

This is a **doc-only resolution PR**: no Lean code is modified. The point
is to retire the open gating question on S18c (next action listed in
`state.md`) so the eventual S18c implementer can write the open-cover step
without a preliminary spike.

## Question

Does the local `IsUpperHemicontinuous` definition (line 70–73 of
`proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`) quantify `V` over the
**ambient** Euclidean space or over the **subtype** `↥S`? If subtype, is a
preimage pull-back step required before calling
`uhc_local_thickening`?

## Answer

**Subtype-relative**, and **no extra pull-back step is required** because
`uhc_local_thickening` is already typeclass-abstract over `Y`.

### Reading

Line 70–73:

```lean
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}
```

`V` quantifies over `Set Y`, where `Y` is the **codomain type** of `F`.

In `axiom approx_selection_exists` (line 504–512):

```lean
F : SetValuedMap (↥S) (↥S)
hF_uhc : IsUpperHemicontinuous F
```

So `Y = ↥S` and `V` ranges over `Set ↥S` — i.e. over subtype-open sets
(in the subspace topology inherited from `EuclideanSpace ℝ (Fin n)`).

### Why no pull-back is needed

`uhc_local_thickening` (line 101–110) is parameterised:

```lean
lemma uhc_local_thickening {X Y : Type*} [TopologicalSpace X]
    [PseudoMetricSpace Y]
    {F : SetValuedMap X Y} (hF : IsUpperHemicontinuous F)
    (x₀ : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      ∀ x ∈ U, F x ⊆ Metric.thickening ε (F x₀)
```

It abstracts over `Y` as a `PseudoMetricSpace`. When `Y = ↥S`, the
`PseudoMetricSpace ↥S` instance is the one inherited from the ambient
Euclidean space, so `Metric.thickening ε (F x₀) : Set ↥S` is the
subtype-internal ε-thickening. The containment `F x ⊆ Metric.thickening
ε (F x₀)` is then a relation between subsets of `↥S`, exactly the form
needed when invoking the subtype-relative `IsUpperHemicontinuous F` at
`V = Metric.thickening ε (F x₀)`.

No `Subtype.val ⁻¹'` pull-back is required. The S17 risk on line 40 of
the survey is **not realised**: PR #17708's `uhc_local_thickening`
abstracts correctly and is directly applicable to S18c's Step 1.

## Sanity note on the ambient-image convexity hypothesis

The reader should not confuse this resolution with the **convexity**
hypothesis on `F`, which IS stated ambient-image:

```lean
hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n)))
```

Convexity lives in the ambient Euclidean space because convex combinations
require vector-space structure, and `↥S` is only a metric subspace — not
a vector subspace. The ambient form is used at Step 4 (Cellina averaging),
not at Step 1 (UHC ε-thickening).

## Implication for the iteration plan

The S18c task ("Build the open cover `U_x` and extract finite subcover.
Land as a standalone PR") can directly chain `uhc_local_thickening` calls
across `x : ↥S` without a preliminary preimage step. The estimated
~50-line bound in the survey stands.

## Follow-up

* S18c implementer: call `uhc_local_thickening` once per cover-base point;
  use the resulting subtype-open `U_x` directly with `IsCompact.elim_finite_subcover`
  (Mathlib: `Mathlib.Topology.SubsetProperties`).
* If a future refactor lifts `axiom approx_selection_exists` to take `F`
  with codomain in the ambient `EuclideanSpace`, this analysis would need
  to be revisited; for now the subtype codomain is canonical.
