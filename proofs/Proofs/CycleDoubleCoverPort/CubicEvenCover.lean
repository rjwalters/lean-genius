import Proofs.CycleDoubleCoverPort.EvenCover
import Proofs.CycleDoubleCoverPort.CubicLabeling

/-
# Cycle Double Cover port, step 7b: from a cubic labelling to an exact even double cover

This slice of the port of the openai/cdc-lean development of the Cycle Double
Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) closes the gap that
step 2 (#43626) deliberately left open: upstream `CDCLean/EvenCover.lean` ends
with `cubic_even_double_cover`, which turns the labelling produced by
`CDCLean/CubicLabeling.lean` into an `IndexedEvenDoubleCover`. Since the
labelling only landed in step 7a (#43628), that final declaration could not be
ported with the rest of `EvenCover.lean`; it is ported here.

See #37507 for the porting order, #43625 / #43626 for steps 1 and 2, #43630 for
step 3, and #43628 for step 7a.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin.

Two structural differences from upstream are worth naming:

* upstream builds the cover directly from `cubic_labeling` inside a single
  `refine` block. Here the construction is factored through
  `CubicLabeling.toIndexedEvenDoubleCover`, which converts an *arbitrary*
  labelling, and `cubic_even_double_cover` is the one-line application of it to
  the labelling supplied by step 7a. The factored form is what a consumer of the
  port needs if it ever obtains a labelling by some other route, and it keeps
  the noncomputability confined to the `Classical.choose` inside
  `cubic_labeling`.
* upstream leaves the resulting cover opaque. The membership characterisation
  (`mem_support_toIndexedEvenDoubleCover`) and the fact that the two indices
  covering an edge are genuinely distinct (`base_ne_base_add_flow`) are added
  here, because step 8 has to reason about which edge sets an edge belongs to
  and not merely about how many.

## Mathematical content

Everything hard has already happened. `cubic_labeling` (step 7a) attaches to
each edge `e` a base point `p e ∈ Gamma = F₂³` such that at every vertex the
three affine pairs `{p e, p e + f e}` cover each index an even number of times.
Reading that family of pairs as eight `F₂`-indicator functions on edges — one
per element of `Gamma` — the two fields of `CubicGraph.IndexedEvenDoubleCover`
are exactly the two facts already in hand:

* `vertexEven` is the labelling's `vertexParity`, with its two arguments
  swapped;
* `coveredTwice` is `pairIndicator_card` (step 2b), applied with the direction
  `h := f e`, whose nonvanishing is the nowhere-zeroness of the flow.

The second bullet is where the whole 8-flow strategy pays off. An affine pair
`{p, p + h}` has two elements precisely when `h ≠ 0`; a flow that could vanish
on an edge would leave that edge in a single set counted twice, i.e. a
degenerate cover. So a nowhere-zero `Gamma`-flow yields an *exact double* cover
rather than the quadruple cover available from weaker hypotheses.

## Deliberate omissions

All of `CDCLean/CubicTheorem.lean` remains unported, and this file does **not**
discharge `CycleDoubleCover.cycleDoubleCover_of_bridgeless` — that is step 8.
The two merged files this one builds on, `EvenCover.lean` and
`CubicLabeling.lean`, are left untouched.
-/

namespace CycleDoubleCover

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- Membership in the affine pair `{p, p + h}`, read off the indicator. This is
the pointwise form of `pairIndicator_filter` from step 2b, which is where the
content sits. -/
theorem pairIndicator_eq_one_iff (p h s : Gamma) :
    pairIndicator p h s = 1 ↔ s = p ∨ s = p + h := by
  have hmem := Finset.ext_iff.mp (pairIndicator_filter p h) s
  simpa using hmem

namespace CubicLabeling

variable {G : CubicGraph V E} {f : GammaFlow G}

/-- The eight `F₂`-indicators determined by a labelling: the index `s` selects
the edge `e` exactly when `s` lies in the affine pair `{p e, p e + f e}` based
at the label of `e` in the direction of its flow value. -/
def member (P : CubicLabeling G f) (s : Gamma) (e : E) : F₂ :=
  pairIndicator (P.base e) (f.val e) s

theorem member_eq_one_iff (P : CubicLabeling G f) (s : Gamma) (e : E) :
    P.member s e = 1 ↔ s = P.base e ∨ s = P.base e + f.val e :=
  pairIndicator_eq_one_iff _ _ _

/-- The two indices selecting an edge are distinct. Equivalently: the affine
pair based at `P.base e` in the direction `f.val e` does not degenerate, which
is exactly nowhere-zeroness of the flow. -/
theorem base_ne_base_add_flow (P : CubicLabeling G f) (e : E) :
    P.base e ≠ P.base e + f.val e := by
  intro hb
  refine f.nowhereZero e (add_left_cancel (a := P.base e) ?_)
  rw [add_zero]
  exact hb.symm

/-- **A labelling is an exact indexed even double cover.** The `vertexEven`
field is the labelling's own parity condition; the `coveredTwice` field is the
two-element count of a nondegenerate affine pair, where nondegeneracy is
nowhere-zeroness of the flow. -/
def toIndexedEvenDoubleCover (P : CubicLabeling G f) : G.IndexedEvenDoubleCover where
  member := P.member
  vertexEven s v := P.vertexParity v s
  coveredTwice e := pairIndicator_card (P.base e) (f.val e) (f.nowhereZero e)

@[simp]
theorem toIndexedEvenDoubleCover_member (P : CubicLabeling G f) (s : Gamma) (e : E) :
    P.toIndexedEvenDoubleCover.member s e = pairIndicator (P.base e) (f.val e) s :=
  rfl

theorem mem_support_toIndexedEvenDoubleCover (P : CubicLabeling G f) (s : Gamma) (e : E) :
    e ∈ P.toIndexedEvenDoubleCover.support s ↔ s = P.base e ∨ s = P.base e + f.val e := by
  rw [CubicGraph.IndexedEvenDoubleCover.mem_support]
  exact P.member_eq_one_iff s e

theorem base_mem_support (P : CubicLabeling G f) (e : E) :
    e ∈ P.toIndexedEvenDoubleCover.support (P.base e) :=
  (P.mem_support_toIndexedEvenDoubleCover _ e).mpr (Or.inl rfl)

theorem base_add_flow_mem_support (P : CubicLabeling G f) (e : E) :
    e ∈ P.toIndexedEvenDoubleCover.support (P.base e + f.val e) :=
  (P.mem_support_toIndexedEvenDoubleCover _ e).mpr (Or.inr rfl)

end CubicLabeling

/-- **A cubic multigraph with a nowhere-zero `Gamma`-flow carries an exact
indexed even double cover.** This is the conclusion of the cubic half of the
argument: the labelling stage (step 7a) supplies coherent base points, and the
counting lemma of step 2b turns each edge's affine pair into the two indices
that select it.

Downstream, `Expansion.projectEvenDoubleCover` pushes such a cover from a cubic
expansion back to the original graph, and step 1's
`FiniteGraph.IndexedEvenDoubleCover.toCycleDoubleCover` decomposes each even
edge set into circuits — which is how this object eventually becomes a genuine
`CycleDoubleCover`. -/
noncomputable def cubic_even_double_cover (G : CubicGraph V E) (f : GammaFlow G) :
    G.IndexedEvenDoubleCover :=
  (cubic_labeling G f).toIndexedEvenDoubleCover

@[simp]
theorem cubic_even_double_cover_member (G : CubicGraph V E) (f : GammaFlow G)
    (s : Gamma) (e : E) :
    (cubic_even_double_cover G f).member s e
      = pairIndicator ((cubic_labeling G f).base e) (f.val e) s :=
  rfl

/-- Existence form, which is what the assembly step actually consumes: the cover
itself is noncomputable (the labelling is chosen by `Classical.choose`), so
later stages should quantify over its existence rather than over the particular
construction. -/
theorem nonempty_indexedEvenDoubleCover_of_gammaFlow (G : CubicGraph V E) (f : GammaFlow G) :
    Nonempty G.IndexedEvenDoubleCover :=
  ⟨cubic_even_double_cover G f⟩

end CycleDoubleCover
