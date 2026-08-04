import Proofs.CycleDoubleCover
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.Card

/-
# Cycle Double Cover port, step 1a: general finite loopless multigraphs

This is the first slice of the port of the openai/cdc-lean development of the
Cycle Double Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into
this gallery. It corresponds to upstream `CDCLean/GeneralGraph.lean`.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*:
the upstream source was consulted only for the mathematical content — the
shapes of the definitions and the statements of the results — and every proof
script here was written from scratch against this repository's Mathlib pin.

## Relationship to `Proofs/CycleDoubleCover.lean`

`Proofs/CycleDoubleCover.lean` (landed in #37506) already carries the core
statement-level definitions, which were checked against upstream when that
entry was created:

| definition | home |
| --- | --- |
| `F₂` | `Proofs/CycleDoubleCover.lean` |
| `FiniteGraph` | `Proofs/CycleDoubleCover.lean` |
| `FiniteGraph.Crosses` | `Proofs/CycleDoubleCover.lean` |
| `FiniteGraph.cut` | `Proofs/CycleDoubleCover.lean` |
| `FiniteGraph.Bridgeless` | `Proofs/CycleDoubleCover.lean` |

Rather than restate them (which would risk exactly the statement drift the
epic warns about), this file **imports and extends** that namespace. Every
definition below therefore refers to *the very same* `FiniteGraph` against
which `CycleDoubleCover.cycleDoubleCover_of_bridgeless` is stated, so no
equivalence bridge is needed and no drift is possible. (When this file landed,
that name was an `axiom` in `Proofs/CycleDoubleCover.lean`; it is now a theorem
proved by `CycleDoubleCoverPort/Main.lean`, under the same name and statement.)

This file does **not** itself prove that theorem; that is done in
`CycleDoubleCoverPort/Main.lean`, the last file of the port (#37507).

## Contents

Half-edges and degree, flow conservation over an arbitrary abelian group,
nowhere-zero and integral 6-flows, the theorem-shaped trust boundary for
Seymour's six-flow theorem, and the eight-indexed even double cover used by
the projection stage.
-/

namespace CycleDoubleCover

/-- The additive group `F₂³ = (ZMod 2)³` that indexes the eight edge sets of the
projection stage. It is used as the index type of `IndexedEvenDoubleCover`. -/
abbrev Gamma := Fin 3 → F₂

namespace FiniteGraph

/-- A half-edge (edge end): an edge object together with one of its two
numbered ends. Loopless multigraphs are handled by treating the two ends of an
edge as distinct objects. -/
abbrev HalfEdge (E : Type*) := E × Fin 2

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-- The vertex sitting at a given half-edge. -/
def vertex (h : HalfEdge E) : V := G.endAt h.1 h.2

/-- The subtype of half-edges incident with `v`. -/
def halfEdgesAt (v : V) := {h : HalfEdge E // G.vertex h = v}

instance instFintypeHalfEdgesAt (v : V) : Fintype (G.halfEdgesAt v) :=
  Subtype.fintype fun h : HalfEdge E => G.vertex h = v

/-- The degree of a vertex, with parallel edge objects counted separately. -/
def degree (v : V) : ℕ := Fintype.card (G.halfEdgesAt v)

/-- Signed conservation at every vertex, for a labelling of the oriented edge
objects by an abelian group. The end numbering supplies the orientation; in
characteristic two it is irrelevant. -/
def IsFlow {A : Type*} [AddCommGroup A] (f : E → A) : Prop :=
  ∀ v : V,
    (∑ e : E, if G.endAt e 0 = v then f e else 0) -
      (∑ e : E, if G.endAt e 1 = v then f e else 0) = 0

/-- A labelling of edge objects that avoids `0`. -/
def IsNowhereZero {A : Type*} [Zero A] (f : E → A) : Prop := ∀ e, f e ≠ 0

/-- An integer nowhere-zero 6-flow: the direct conclusion of Seymour's
six-flow theorem. -/
structure SixFlow where
  val : E → ℤ
  conservation : G.IsFlow val
  bound : ∀ e, 0 < Int.natAbs (val e) ∧ Int.natAbs (val e) < 6

/-- A nowhere-zero flow valued in an arbitrary abelian group. -/
structure NowhereZeroFlow (A : Type*) [AddCommGroup A] where
  val : E → A
  conservation : G.IsFlow val
  nowhereZero : IsNowhereZero val

/-- The theorem-shaped trust boundary for Seymour's six-flow theorem: every
finite bridgeless loopless multigraph carries a nowhere-zero integral 6-flow.
Stated as a `Prop` so that later stages of the port can take it as an explicit
hypothesis rather than an ambient axiom. -/
def SeymourSixFlowStatement : Prop :=
  ∀ (V : Type*) (E : Type*) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E), Bridgeless G → Nonempty G.SixFlow

/-- The eight edge sets used by the projection stage, stated for an arbitrary
graph: an assignment of an `F₂`-indicator to each edge for each of the eight
elements of `Gamma`, such that each indicator set is even at every vertex and
each edge is selected by exactly two of the eight. -/
structure IndexedEvenDoubleCover where
  member : Gamma → E → F₂
  vertexEven : ∀ s v,
    ∑ e : E,
      ((if G.endAt e 0 = v then member s e else 0) +
       (if G.endAt e 1 = v then member s e else 0)) = 0
  coveredTwice : ∀ e,
    (Finset.univ.filter fun s : Gamma => member s e = 1).card = 2

-- ============================================================
-- Elementary consequences (proved here, no axiom dependence)
-- ============================================================

/-- `Gamma` really does have eight elements, so `IndexedEvenDoubleCover` is the
promised *eight*-set object and `coveredTwice` asks for two out of eight. -/
theorem card_gamma : Fintype.card Gamma = 8 := by decide

omit [DecidableEq E] in
/-- Degree as the cardinality of a `Finset` of half-edges. -/
theorem degree_eq_card_filter (v : V) :
    G.degree v = (Finset.univ.filter fun h : HalfEdge E => G.vertex h = v).card :=
  Fintype.card_subtype _

omit [DecidableEq E] in
/-- Handshake lemma for multigraphs: the degrees sum to twice the number of
edge objects. Each edge contributes exactly its two ends. -/
theorem sum_degree_eq_two_mul_card_edges :
    ∑ v : V, G.degree v = 2 * Fintype.card E := by
  classical
  simp_rw [G.degree_eq_card_filter]
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := fun h : HalfEdge E => G.vertex h) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

omit [DecidableEq E] in
/-- The zero labelling is a flow. (Sanity check on `IsFlow`; it is of course
not nowhere-zero unless there are no edges.) -/
theorem zero_isFlow {A : Type*} [AddCommGroup A] : G.IsFlow (fun _ : E => (0 : A)) := by
  intro v
  simp

omit [DecidableEq V] [DecidableEq E] in
/-- A bridgeless graph has no vertex whose incident edges form a one-element
cut; specialised to the empty subset this says the empty cut is not a single
edge, which is immediate. Recorded as a smoke test that `Bridgeless` from
`Proofs/CycleDoubleCover.lean` is usable from this file. -/
theorem cut_empty_card_ne_one (hb : G.Bridgeless) : (G.cut ∅).card ≠ 1 := hb ∅

end FiniteGraph

end CycleDoubleCover
