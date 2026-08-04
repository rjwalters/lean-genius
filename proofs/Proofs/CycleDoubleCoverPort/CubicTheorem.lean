-- Ported from openai/cdc-lean, CubicTheorem.lean, vendored with adaptation per
-- operator decision 2026-08-03. Part of epic #37507.
import Proofs.CycleDoubleCoverPort.CubicBridge
import Proofs.CycleDoubleCoverPort.CubicEvenCover
import Proofs.CycleDoubleCoverPort.FlowCount

/-
# Cycle Double Cover port: the certified cubic implication and its transfer boundary

Port of upstream `CDCLean/CubicTheorem.lean` (all three declarations), the file
that assembles the previously ported cubic machinery into the conditional cubic
theorem. Part of epic #37507.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies.
Earlier files in this port were written as independent re-derivations for that
reason. For this file the operator recorded a decision on 2026-08-03 (#37507)
permitting the upstream text to be vendored with attribution and adaptation.
That is a **risk acceptance, not a license grant**: the statements and the
three-line proof scripts below follow upstream `CDCLean/CubicTheorem.lean`
closely, and are attributed as such. Should the upstream licensing position
change, this file is the one to revisit — nothing else in the port vendors
upstream text.

The adaptations are naming, not mathematics:

* upstream's `namespace CDCLean` becomes this port's `namespace CycleDoubleCover`;
* upstream writes the conclusion as a bare `IndexedEvenDoubleCover K`. This port
  has *two* such structures — `CycleDoubleCover.FiniteGraph.IndexedEvenDoubleCover`
  (general graphs, `GeneralGraph.lean`) and
  `CycleDoubleCover.CubicGraph.IndexedEvenDoubleCover` (cubic graphs,
  `EvenCover.lean`) — so the conclusion is written `K.IndexedEvenDoubleCover`,
  pinning the cubic one by the type of `K`. Neither namespace is opened here;
  every reference below is qualified or resolved by dot notation.

## Mathematical content

Everything in this file is **conditional**. Neither theorem asserts anything
unconditionally about cubic graphs: Seymour's six-flow theorem and the
order-eight coefficient transfer both enter as explicit hypotheses, so what is
proved is precisely the implication

> Seymour + transfer ⟹ every bridgeless cubic multigraph has an indexed even
> double cover

with the two named inputs kept visible in the statement. The point of the file
is exactly that visibility: it is the integration boundary of the cubic half of
the argument, and it is where a future discharge of either hypothesis plugs in.

`OrderEightFlowTransferStatement` names the second input as a `Prop`. It is
Tutte's order-only invariance specialized to the single transfer the manuscript
uses, `ZMod 8 → Gamma`; `FlowCount.lean` already proves it for any finite graph
satisfying the counting hypothesis (`zmodEight_to_gamma`), and `PathCut.lean`
supplies the graph-theoretic route to that hypothesis.

The two theorems differ only in how the transfer input is phrased.
`cubic_even_double_cover_of_sixFlow` takes it abstractly, in the shape of
`OrderEightFlowTransferStatement` instantiated at one pair of types.
`cubic_even_double_cover_of_sixFlow_of_cardinalityInvariant` instead takes
Tutte's flow-count cardinality invariant for the graph at hand and derives the
transfer internally via `FiniteGraph.zmodEight_to_gamma`, which is the form the
downstream assembly actually consumes.

Both proofs are the same three steps: get a 6-flow from Seymour, push it to a
nowhere-zero `Gamma`-flow (reduce mod 8 by `SixFlow.toZModEight`, then transfer),
and feed that flow to `cubic_even_double_cover`.

## Universe note

`FiniteGraph.SeymourSixFlowStatement` and `OrderEightFlowTransferStatement` are
universe-polymorphic (`.{u, v}`), since they quantify over the vertex and edge
types. Consumers instantiating them against a `variable {V E : Type*}` block can
hit a universe mismatch; declaring `universe u v` and instantiating explicitly
avoids it. The hypotheses of the two theorems here are therefore written out
inline, at the theorem's own `V` and `E`, rather than as
`OrderEightFlowTransferStatement` applications — matching upstream, and keeping
each theorem monomorphic in its universes.

The third declaration deliberately binds `{V E : Type}` (i.e. `Type 0`) rather
than `Type*`, mirroring upstream: `FiniteGraph.FlowCardinalityInvariant`
quantifies its two groups over `Type`, and the `Type 0` binding keeps the
hypothesis in the shape `FlowCount.lean` proves. Generalizing to `Type*` here
would change the statement rather than strengthen it.

## Downstream status

Nothing else in this repository's port calls these theorems — upstream's own
import of this file is vestigial in the same way. This module is a leaf, so its
build status does not gate the remaining waves of the port.
-/

universe u v

namespace CycleDoubleCover

/-- Tutte's order-only invariance specialized to the one transfer used by the
manuscript: on any finite graph, a nowhere-zero `ZMod 8`-flow yields a
nowhere-zero `Gamma`-flow. `ZMod 8` and `Gamma = F₂³` are non-isomorphic groups
of the same order, so this is a counting statement, not a relabelling —
`FiniteGraph.zmodEight_to_gamma` proves it from the flow-count cardinality
invariant. Retaining it as a named proposition gives the conditional cubic
theorem below a precise integration boundary. -/
def OrderEightFlowTransferStatement : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E),
    Nonempty (G.NowhereZeroFlow (ZMod 8)) → Nonempty (G.NowhereZeroFlow Gamma)

/-- **The complete cubic portion of the argument.** Its only inputs beyond
finite graph data are Seymour's literal integer 6-flow statement and the
separately named group-order transfer statement, both taken here as explicit
hypotheses at this `V` and `E`. Given those, every bridgeless cubic multigraph
carries an indexed even double cover: the eight `Gamma`-indexed edge sets, each
even at every vertex, each edge in exactly two of them. -/
theorem cubic_even_double_cover_of_sixFlow
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (seymour : ∀ G : FiniteGraph V E,
      FiniteGraph.Bridgeless G → Nonempty G.SixFlow)
    (transfer : ∀ G : FiniteGraph V E,
      Nonempty (G.NowhereZeroFlow (ZMod 8)) → Nonempty (G.NowhereZeroFlow Gamma))
    (K : CubicGraph V E) (hK : FiniteGraph.Bridgeless K.toFiniteGraph) :
    Nonempty K.IndexedEvenDoubleCover := by
  obtain ⟨sf⟩ := seymour K.toFiniteGraph hK
  obtain ⟨gammaFlow⟩ := transfer K.toFiniteGraph ⟨sf.toZModEight⟩
  exact ⟨cubic_even_double_cover K (K.gammaFlowOfNowhereZero gammaFlow)⟩

/-- The same cubic theorem with the transfer hypothesis stated exactly as
Tutte's flow-count cardinality invariant for this graph, which is the form
`FlowCount.lean` establishes and the form the downstream assembly consumes. The
transfer is then derived internally by `FiniteGraph.zmodEight_to_gamma`. -/
theorem cubic_even_double_cover_of_sixFlow_of_cardinalityInvariant
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (seymour : ∀ G : FiniteGraph V E,
      FiniteGraph.Bridgeless G → Nonempty G.SixFlow)
    (K : CubicGraph V E) (hK : FiniteGraph.Bridgeless K.toFiniteGraph)
    (hcount : K.toFiniteGraph.FlowCardinalityInvariant) :
    Nonempty K.IndexedEvenDoubleCover := by
  obtain ⟨sf⟩ := seymour K.toFiniteGraph hK
  obtain ⟨gammaFlow⟩ := K.toFiniteGraph.zmodEight_to_gamma hcount ⟨sf.toZModEight⟩
  exact ⟨cubic_even_double_cover K (K.gammaFlowOfNowhereZero gammaFlow)⟩

end CycleDoubleCover
