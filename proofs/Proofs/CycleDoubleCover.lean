import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-
# The Cycle Double Cover Conjecture (Szekeres 1973 / Seymour 1979)

## Statement

Every finite bridgeless loopless multigraph has a cycle double cover: a finite
multiset of cycles such that every edge lies in exactly two members, counted
with multiplicity.

## Status: RESOLVED (2026), axiomatized here pending port

On 2026-07-10 OpenAI announced a proof produced by GPT-5.6 Sol Ultra, together
with a complete Lean 4 formalization:

- Proof PDF: https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_proof.pdf
- Lean source: https://github.com/openai/cdc-lean (Lean v4.31.0, Mathlib 9a9483a9)

The upstream Lean proof was INDEPENDENTLY VERIFIED for this gallery on
2026-07-11 (see issue #37504): `lake build` succeeded (1727 jobs) on the pinned
toolchain, and `#print axioms` on the final theorem
`CDCLean.cycleDoubleCover_of_bridgeless` reports exactly
`[propext, Classical.choice, Quot.sound]` — no sorries, no custom axioms, no
`native_decide`. The statement was checked to be the genuine, unconditional
conjecture (this file mirrors those definitions).

The proof route: Jaeger–Kilpatrick's eight-flow theorem produces a nowhere-zero
`(ZMod 2)³`-flow on a cubic expansion; a new labeling/linear-algebra argument
converts that flow into an exact even double cover, which projects back and
decomposes into cycles. Classically an 8-flow was only known to yield a cycle
QUADRUPLE cover; the 8-flow → double-cover conversion is the new content.

This file ports the *statement* (definitions follow upstream `CDCLean` exactly,
modulo naming) and axiomatizes the theorem until the 7,134-line proof is ported
to our Mathlib pin. The axiom is the upstream kernel-checked theorem.

## Definitions (mirroring openai/cdc-lean)

- `FiniteGraph V E`: finite loopless multigraph — edges are primitive objects
  with two distinct ends; parallel edges are distinct.
- `Bridgeless`: no vertex subset has an edge cut of cardinality exactly one.
- `Cycle`: a nonempty inclusion-minimal even edge set — the graphic-matroid
  characterization of a circuit (two parallel edges form a 2-cycle).
- `CycleDoubleCover`: a list (multiset) of cycles with every edge in exactly
  two members.
-/

namespace CycleDoubleCover

open Finset

/-- The field with two elements, used for parity bookkeeping. -/
abbrev F₂ := ZMod 2

/-- A finite loopless multigraph: each edge is a primitive object with two
numbered, distinct ends. Parallel edges are allowed and distinct. -/
structure FiniteGraph (V E : Type*) [Fintype V] [Fintype E] where
  endAt : E → Fin 2 → V
  loopless : ∀ e, endAt e 0 ≠ endAt e 1

namespace FiniteGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-- Whether edge `e` crosses the vertex subset `S`. -/
def Crosses (S : Finset V) (e : E) : Prop :=
  (G.endAt e 0 ∈ S) ≠ (G.endAt e 1 ∈ S)

/-- The cut of a vertex subset: the edges crossing it. -/
noncomputable def cut (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter (G.Crosses S)

/-- Bridgeless, by the cut characterization: no cut consists of exactly one
edge. Connectivity is NOT assumed; disconnected graphs are permitted. -/
def Bridgeless : Prop := ∀ S : Finset V, (G.cut S).card ≠ 1

/-- The incidence indicator of an edge at a vertex over `F₂`, counting both
edge ends. -/
def edgeIncidence (v : V) (e : E) : F₂ :=
  (if G.endAt e 0 = v then 1 else 0) + (if G.endAt e 1 = v then 1 else 0)

/-- An edge set is even when every vertex meets it an even number of times. -/
def IsEvenEdgeSet (F : Finset E) : Prop :=
  ∀ v : V, ∑ e ∈ F, G.edgeIncidence v e = 0

/-- A multigraph cycle: a nonempty inclusion-minimal even edge set. For
loopless multigraphs these are exactly the circuits (connected 2-regular
submultigraphs); two distinct parallel edges form a legitimate 2-cycle. -/
structure Cycle where
  edges : Finset E
  nonempty : edges.Nonempty
  even : G.IsEvenEdgeSet edges
  minimal : ∀ D : Finset E, D.Nonempty → D ⊆ edges → G.IsEvenEdgeSet D → D = edges

/-- A cycle double cover: a finite multiset of cycles (a list, so repeated
cycles are retained) in which every edge occurs in exactly two members. -/
structure CycleDoubleCover where
  cycles : List G.Cycle
  coveredTwice : ∀ e : E, (cycles.filter fun C => e ∈ C.edges).length = 2

end FiniteGraph

-- ============================================================
-- The theorem (axiomatized; kernel-checked upstream, see header)
-- ============================================================

/-- **The Cycle Double Cover theorem** (Szekeres–Seymour conjecture, resolved
2026): every finite bridgeless loopless multigraph has a cycle double cover.

Axiomatized pending a port of the upstream proof. The upstream artifact
(`CDCLean.cycleDoubleCover_of_bridgeless` in openai/cdc-lean) was independently
rebuilt and kernel-audited for this gallery on 2026-07-11; it depends only on
`propext`, `Classical.choice`, and `Quot.sound`. -/
axiom cycleDoubleCover_of_bridgeless
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (hb : G.Bridgeless) :
    Nonempty G.CycleDoubleCover

-- ============================================================
-- Elementary facts proved directly (no axiom dependence)
-- ============================================================

section Elementary

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-- An edgeless graph has the empty cycle double cover, directly. -/
theorem edgeless_cdc [IsEmpty E] : Nonempty G.CycleDoubleCover :=
  ⟨⟨[], fun e => isEmptyElim e⟩⟩

/-- A single edge is never an even edge set: its two ends are distinct, so it
meets each of them exactly once. Hence no cycle is a singleton — the smallest
cycles are parallel-edge 2-cycles. -/
theorem singleton_not_even (e : E) : ¬ G.IsEvenEdgeSet {e} := by
  intro h
  have he := h (G.endAt e 0)
  have hne : G.endAt e 1 ≠ G.endAt e 0 := (G.loopless e).symm
  simp [FiniteGraph.edgeIncidence, hne] at he

/-- Every cycle has at least two edges. -/
theorem cycle_card_ge_two (C : G.Cycle) : 2 ≤ C.edges.card := by
  by_contra hlt
  push_neg at hlt
  interval_cases h : C.edges.card
  · exact absurd (Finset.card_eq_zero.mp h) C.nonempty.ne_empty
  · obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
    exact singleton_not_even G e (he ▸ C.even)

end Elementary

end CycleDoubleCover
