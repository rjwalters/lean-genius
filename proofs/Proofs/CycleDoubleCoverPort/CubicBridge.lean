import Proofs.CycleDoubleCoverPort.Basic

/-
# Cycle Double Cover port, step 3a: passing between the general and cubic encodings

Third slice of the port of the openai/cdc-lean development of the Cycle Double
Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery.
It corresponds to upstream `CDCLean/CubicBridge.lean`; see #37507 for the
porting order, #43625 for step 1 (`GeneralGraph.lean` / `CycleDecomposition.lean`)
and #43626 for step 2 (`Basic.lean` / `EvenCover.lean`).

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin. In particular
`sum_incident_ends` is proved by collapsing the outer vertex sum with an
explicit pointwise `if`-normalisation rather than via `Fintype.sum_eq_single`,
and `neg_gamma` is *derived* from `gamma_add_self` (step 2) instead of being
re-checked by exhaustive kernel decision over the eight elements of `Gamma`.

## Mathematical content

Step 2 introduced two encodings of the same object:

* `FiniteGraph V E` (step 1, and the encoding in which
  `cycleDoubleCover_of_bridgeless` is stated) — edges are primitive objects with
  two numbered ends;
* `CubicGraph V E` (step 2) — additionally, an equivalence
  `(V × Fin 3) ≃ (E × Fin 2)` matching the three local slots at every vertex
  with the numbered edge ends.

`CubicGraph.toFiniteGraph` forgets the slot structure. The point of this file is
that nothing is lost in the flow theory when one does so: a nowhere-zero
`Gamma`-valued flow on the forgotten graph (the general, signed, conservation
condition of `FiniteGraph.IsFlow`) is literally the same data as a `GammaFlow`
on the cubic graph (the unsigned three-slot condition). Two facts make this
work:

* `sum_incident_ends` — summing any edge function over the edge ends incident
  with `v` is the same as summing it over the three slots at `v`. This is pure
  transport along `incidence` (step 2's `sum_edgeEnds_eq_sum_vertexSlots`), with
  the outer sum over vertices collapsing because each slot sits at a known
  vertex.
* `neg_gamma` — in `Gamma = F₂³` every element is its own additive inverse, so
  the orientation signs in `IsFlow` are invisible and the difference of the two
  end-sums coincides with their sum.

This file does **not** discharge
`CycleDoubleCover.cycleDoubleCover_of_bridgeless`; that is done in
`CycleDoubleCoverPort/Main.lean`, the last file of the port.

## Delta from upstream

Upstream's `CubicBridge.lean` sits after `SixFlow.lean` in the import graph
purely for file-ordering reasons; none of its content depends on the flow-count
machinery. Here it is placed directly on top of step 2, which is where it
mathematically belongs, so that `Expansion.lean` can be ported before the
692-line `FlowCount.lean`.
-/

namespace CycleDoubleCover

/-- `Gamma = F₂³` has characteristic two, in negation form: every element is its
own additive inverse. Derived from `gamma_add_self` (step 2) rather than
re-decided. -/
@[simp]
theorem neg_gamma (x : Gamma) : -x = x :=
  neg_eq_of_add_eq_zero_right (gamma_add_self x)

namespace CubicGraph

variable {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E)

/-- Forget the three-slot presentation, keeping the two numbered ends of every
edge. Looplessness transfers verbatim, since step 2's `endAt_zero_ne_one` is
already stated in the shape of the `FiniteGraph` field. -/
def toFiniteGraph : FiniteGraph V E where
  endAt := G.endAt
  loopless := G.endAt_zero_ne_one

@[simp]
theorem toFiniteGraph_endAt : G.toFiniteGraph.endAt = G.endAt := rfl

variable [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
/-- Reading an edge function around a vertex: summing over all edge ends that
land at `v` is the same as summing over the three local slots at `v`.

The proof is transport along `incidence` followed by collapsing the resulting
outer sum over vertices: after transport the `if`-condition at the slot `(w, i)`
says exactly `w = v`, so all but one summand vanishes. -/
theorem sum_incident_ends {A : Type*} [AddCommMonoid A] (q : E → A) (v : V) :
    ∑ e : E, ∑ j : Fin 2, (if G.endAt e j = v then q e else 0) =
      ∑ i : Fin 3, q (G.edgeAt v i) := by
  classical
  rw [G.sum_edgeEnds_eq_sum_vertexSlots fun e j => if G.endAt e j = v then q e else 0]
  have hslot : ∀ w : V,
      (∑ i : Fin 3,
          (if G.endAt (G.edgeAt w i) (G.incidence (w, i)).2 = v then q (G.edgeAt w i) else 0))
        = if w = v then (∑ i : Fin 3, q (G.edgeAt w i)) else 0 := by
    intro w
    simp only [G.endAt_edgeAt_incidence]
    by_cases hw : w = v
    · simp [hw]
    · simp [hw]
  rw [Finset.sum_congr rfl fun w (_ : w ∈ (Finset.univ : Finset V)) => hslot w]
  simp

/-- A nowhere-zero `Gamma`-flow on the forgotten graph *is* a cubic
`GammaFlow`. Only the conservation law needs an argument: the general condition
is a difference of the two end-sums, which in characteristic two equals their
sum, and that sum is the three-slot sum by `sum_incident_ends`. -/
def gammaFlowOfNowhereZero (f : G.toFiniteGraph.NowhereZeroFlow Gamma) : GammaFlow G where
  val := f.val
  nowhereZero := f.nowhereZero
  conservation := by
    intro v
    have hsub : (∑ e : E, if G.endAt e 0 = v then f.val e else 0)
        - (∑ e : E, if G.endAt e 1 = v then f.val e else 0) = 0 := f.conservation v
    have hends : (∑ e : E, if G.endAt e 0 = v then f.val e else 0)
        = ∑ e : E, if G.endAt e 1 = v then f.val e else 0 := sub_eq_zero.mp hsub
    have hadd : (∑ e : E, if G.endAt e 0 = v then f.val e else 0)
        + (∑ e : E, if G.endAt e 1 = v then f.val e else 0) = 0 := by
      rw [← hends]
      exact gamma_add_self _
    rw [← G.sum_incident_ends f.val v]
    calc ∑ e : E, ∑ j : Fin 2, (if G.endAt e j = v then f.val e else 0)
        = ∑ e : E, ((if G.endAt e 0 = v then f.val e else 0)
            + (if G.endAt e 1 = v then f.val e else 0)) :=
          Finset.sum_congr rfl fun e _ => Fin.sum_univ_two _
      _ = (∑ e : E, if G.endAt e 0 = v then f.val e else 0)
            + ∑ e : E, if G.endAt e 1 = v then f.val e else 0 := Finset.sum_add_distrib
      _ = 0 := hadd

end CubicGraph

end CycleDoubleCover
