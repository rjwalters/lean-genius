import Proofs.CycleDoubleCoverPort.CubicTheorem
import Proofs.CycleDoubleCoverPort.CubicEvenCover
import Proofs.CycleDoubleCoverPort.CycleDecomposition
import Proofs.CycleDoubleCoverPort.Expansion
import Proofs.CycleDoubleCoverPort.PathCut
import Proofs.CycleDoubleCoverPort.JaegerKilpatrick

-- Ported from openai/cdc-lean, Main.lean, vendored with adaptation per operator
-- decision 2026-08-03. Discharges the cycleDoubleCover_of_bridgeless axiom;
-- completes epic #37507.

/-
# The assembled implication: the Cycle Double Cover theorem

This is the final file of the port of the `openai/cdc-lean` development of the Cycle
Double Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery.
It corresponds to upstream `CDCLean/Main.lean` and assembles the two halves of the
development into the unconditional theorem:

> Every finite bridgeless loopless multigraph has a cycle double cover.

## The three theorems

* `cycleDoubleCover_of_gammaFlow` is the *construction*. Given a rotation system `R`
  on `G` and a nowhere-zero `Gamma`-flow on the cubic expansion `G.cubicExpansion R`,
  it produces a cycle double cover of `G`. The chain is
  `gammaFlowOfNowhereZero` (a nowhere-zero flow on the forgotten graph of a cubic
  graph *is* a cubic `GammaFlow`, `CubicBridge`) followed by
  `cubic_even_double_cover` (the labelling/linear-algebra argument that turns a cubic
  `Gamma`-flow into an *exact* indexed even double cover, `CubicEvenCover` — this is
  the new mathematical content of the 2026 proof, since classically an eight-flow was
  only known to yield a cycle *quadruple* cover), then `projectEvenDoubleCover`
  (restrict the eight edge sets from the expansion back along the spokes,
  `Expansion`), then `IndexedEvenDoubleCover.toCycleDoubleCover` (decompose each of
  the eight even edge sets into circuits and concatenate, `CycleDecomposition`).

* `cycleDoubleCover_of_sixFlow` records the *conditional* route that the port reached
  first: it carries Seymour's literal nowhere-zero integer six-flow theorem as an
  explicit hypothesis (`SeymourSixFlowStatement`) and feeds it through
  `SixFlow.toZModEight` and `zmodEight_to_gamma_unconditional` (Tutte's coefficient
  transfer, `FlowCount`/`PathCut`) into the construction above. It is retained for
  the record and as a smoke test of the six-flow layer; nothing downstream uses it,
  and in particular the main theorem does **not** depend on it.

* `cycleDoubleCover_of_bridgeless` is the *theorem*. It replaces the six-flow
  hypothesis by the ported Jaeger--Kilpatrick eight-flow theorem
  (`jaegerKilpatrickEightFlow`, `JaegerKilpatrick`), which is proved outright in this
  development, and so carries no mathematical premise at all.

## Discharging the axiom

Before this file, `Proofs/CycleDoubleCover.lean` declared

```
axiom cycleDoubleCover_of_bridgeless
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (hb : G.Bridgeless) :
    Nonempty G.CycleDoubleCover
```

That axiom is deleted in the same change that adds this file, and the theorem below
takes over its fully qualified name `CycleDoubleCover.cycleDoubleCover_of_bridgeless`
with a character-identical statement, so every prose reference to that name in the
gallery continues to denote the same proposition — now proved rather than assumed.
The theorem cannot live in `Proofs/CycleDoubleCover.lean` itself, because every file
of this port imports that module; it must sit at the top of the import graph, which
is here.

`#print axioms CycleDoubleCover.cycleDoubleCover_of_bridgeless` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Universe generality

Upstream binds a single universe, `{V E : Type u}`. The axiom deleted here bound
`{V E : Type*}`, i.e. two *independent* universes, and the theorem below is stated in
that stronger two-universe form so that the replacement is not silently weaker than
the axiom it discharges. No transport is needed: every definition and theorem in this
port is `Type*`-polymorphic in the vertex and edge types separately.

The one place where universes are genuinely constrained is
`cycleDoubleCover_of_sixFlow`, whose hypothesis must be instantiated at the universes
of the *expansion*. Since `ExpandedVertex G = HalfEdge E = E × Fin 2` and
`ExpandedEdge G = E ⊕ HalfEdge E` both live in the universe of `E`, the required
instance is `SeymourSixFlowStatement.{v, v}` for `E : Type v`; upstream, where
`V` and `E` share a universe, wrote `.{u, u}` for the same reason.

## Provenance, licensing and attribution

Ported from `openai/cdc-lean`, `CDCLean/Main.lean`, vendored with adaptation per the
operator decision recorded on #37507 (comment of 2026-08-03). `openai/cdc-lean`
carries **no license file**, so default copyright applies; the operator's decision is
an explicit *risk acceptance*, not a license. The mathematical content and the proof
scripts originate with `openai/cdc-lean`.

## Adaptations from upstream

* Namespace: upstream `CDCLean` becomes `CycleDoubleCover`, and upstream
  `CDCLean.FiniteGraph` becomes `CycleDoubleCover.FiniteGraph`.
* Universes: `{V E : Type u}` becomes `{V : Type u} {E : Type v}` throughout, to
  match the binders of the axiom being discharged (see above).
* Upstream's intermediate `let` bindings are inlined. Two distinct structures are in
  play — `CubicGraph.IndexedEvenDoubleCover` (evenness stated over the three slots of
  a cubic vertex) and `FiniteGraph.IndexedEvenDoubleCover` (evenness stated over the
  incidence sum) — and inlining lets each construction be applied at its definitional
  form, so no type ascription is needed to disambiguate them under `open FiniteGraph`.
* `cycleDoubleCover_of_gammaFlow` is stated before `cycleDoubleCover_of_sixFlow`
  (upstream orders them the other way round), since both later theorems call it.
-/

namespace CycleDoubleCover

open FiniteGraph

universe u v

/-- A nowhere-zero `Gamma`-flow on a cubic expansion supplies the even double cover
that projects back to a cycle double cover of the original graph.

This is the constructive core of the proof, and the only place where the four stages
of the 2026 argument meet: cubic labelling, exact even double cover, projection along
the spokes, and circuit decomposition. -/
theorem cycleDoubleCover_of_gammaFlow
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (R : G.RotationSystem)
    (gamma : (G.cubicExpansion R).toFiniteGraph.NowhereZeroFlow Gamma) :
    Nonempty G.CycleDoubleCover :=
  ⟨(G.projectEvenDoubleCover R
      (cubic_even_double_cover (G.cubicExpansion R)
        ((G.cubicExpansion R).gammaFlowOfNowhereZero gamma))).toCycleDoubleCover⟩

/-- The claimed implication with Seymour's literal nowhere-zero integer six-flow
theorem as its only mathematical premise. Tutte's coefficient transfer, cubic
expansion, the affine-pair construction, projection and circuit decomposition are all
proved internally.

This is the conditional form the port reached before Jaeger--Kilpatrick was available;
`cycleDoubleCover_of_bridgeless` below supersedes it and does *not* depend on it. The
hypothesis is instantiated at the universes of the expansion, both of which are the
universe of `E`. -/
theorem cycleDoubleCover_of_sixFlow
    (seymour : SeymourSixFlowStatement.{v, v})
    {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (hb : G.Bridgeless) :
    Nonempty G.CycleDoubleCover := by
  classical
  have hK : (G.cubicExpansion (G.rotationSystemOfBridgeless hb)).toFiniteGraph.Bridgeless :=
    G.cubicExpansion_bridgeless (G.rotationSystemOfBridgeless hb) hb
  obtain ⟨sf⟩ :=
    seymour _ _ (G.cubicExpansion (G.rotationSystemOfBridgeless hb)).toFiniteGraph hK
  obtain ⟨gamma⟩ :=
    (G.cubicExpansion (G.rotationSystemOfBridgeless hb)).toFiniteGraph.zmodEight_to_gamma_unconditional
      ⟨sf.toZModEight⟩
  exact cycleDoubleCover_of_gammaFlow G (G.rotationSystemOfBridgeless hb) gamma

/-- **The Cycle Double Cover theorem** (Szekeres 1973 / Seymour 1979, resolved 2026):
every finite bridgeless loopless multigraph has a cycle double cover.

Jaeger--Kilpatrick's eight-flow theorem supplies a nowhere-zero `Gamma`-flow on the
cubic expansion of `G`, which is bridgeless because `G` is
(`cubicExpansion_bridgeless`), and `cycleDoubleCover_of_gammaFlow` turns that flow
into the desired cover.

This theorem replaces the `axiom cycleDoubleCover_of_bridgeless` that
`Proofs/CycleDoubleCover.lean` carried until this file landed; the statement is
character-identical to the deleted axiom, including the two independent universes of
`{V E : Type*}`. It has no hypotheses beyond finiteness and decidability, and
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. -/
theorem cycleDoubleCover_of_bridgeless
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (hb : G.Bridgeless) :
    Nonempty G.CycleDoubleCover := by
  classical
  have hK : (G.cubicExpansion (G.rotationSystemOfBridgeless hb)).toFiniteGraph.Bridgeless :=
    G.cubicExpansion_bridgeless (G.rotationSystemOfBridgeless hb) hb
  obtain ⟨gamma⟩ :=
    (G.cubicExpansion (G.rotationSystemOfBridgeless hb)).toFiniteGraph.jaegerKilpatrickEightFlow hK
  exact cycleDoubleCover_of_gammaFlow G (G.rotationSystemOfBridgeless hb) gamma

end CycleDoubleCover
