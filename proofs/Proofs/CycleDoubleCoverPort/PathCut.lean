import Proofs.CycleDoubleCoverPort.FlowCount

/-
# Cycle Double Cover port, step 5b: the integral path/cut dichotomy

Companion file to `FlowCount.lean` (same slice), corresponding to upstream
`CDCLean/PathCut.lean`. It discharges the one graph-theoretic hypothesis that the
flow-counting recurrence of `FlowCount.lean` leaves open, and so turns Tutte's
group-order invariance from a conditional statement into a theorem about every
finite graph.

## Provenance, licensing and attribution

`openai/cdc-lean` carries **no license file**, so default copyright applies. The
operator has recorded an explicit risk acceptance on #37507 (comment of
2026-08-03) permitting vendoring of upstream sources with attribution. As with
the five sibling slices already merged, this file is nevertheless an
*independent re-derivation*: upstream was consulted for the statements only, and
every proof script here was written from scratch. Attribution: the theorem
statements originate with `openai/cdc-lean` (`CDCLean/PathCut.lean`).

## Mathematical content

Fix a forbidden edge set `S` and an edge `e ∈ S`. `FlowCount.lean` needs to know
that one of two things always happens:

* there is a unit integral circulation through `e` supported off `S.erase e`
  (`HasCycleCorrection`), which makes the value on `e` a free parameter; or
* some vertex set separates the two ends of `e` and is crossed by no allowed
  edge (`HasCutSeparation`), which forces the value on `e` to be zero.

The proof is the usual reachability argument, run with integral chains instead of
walks. Let `U` be the set of vertices reachable from `G.endAt e 0` by an integral
chain supported off `S` (`HasIntegerPath`). Reachability is reflexive, symmetric
and transitive — the three lemmas `hasIntegerPath_refl`, `HasIntegerPath.symm`
and `HasIntegerPath.trans` of `FlowCount.lean` — so `U` is a union of "components"
in this sense.

* If `G.endAt e 1 ∈ U`, the chain realising that closes up with `e` into the
  required circulation (`hasCycleCorrection_of_integerPath`).
* Otherwise `U` separates the ends of `e`. And no *allowed* edge `k ∉ S` crosses
  `U`: such a `k` is itself a one-edge chain avoiding `S`
  (`hasIntegerPath_single`), so its two ends are reachable from each other and
  are therefore both in `U` or both out of it.

That is the entire graph-theoretic content of the flow-count theorem; everything
else was algebra.

## Delta from upstream

Upstream leaves the `Crosses` predicate — a disequality of `Prop`s — unfolded at
each use and finishes both crossing obligations with `propext` by hand. Here the
two `not_crosses_iff` / `crosses_iff` bridges added in `FlowCount.lean` are used
instead, so both obligations are ordinary `Iff` manipulations. This file also
adds a final corollary (`nonempty_nowhereZeroFlow_gamma_of_seymour`, no upstream
counterpart) chaining the unconditional transfer onto the step-1 trust boundary
`SeymourSixFlowStatement`, matching the shape of step 5a's
`nonempty_nowhereZeroFlow_zmodEight_of_seymour`.

## Deliberate omissions

This file does **not** discharge `CycleDoubleCover.cycleDoubleCover_of_bridgeless`
and does not prove Seymour's six-flow theorem — `SeymourSixFlowStatement` stays
an explicit hypothesis. Upstream's `JaegerKilpatrick.lean`, `CubicTheorem.lean`
and `Main.lean` are later steps of the port.
-/

namespace CycleDoubleCover

namespace FiniteGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-- **The integral path/cut dichotomy.** Every finite graph satisfies the
hypothesis that the flow-count recurrence of `FlowCount.lean` was stated over. -/
theorem integralPathCutDichotomy : G.IntegralPathCutDichotomy := by
  classical
  intro S e he
  by_cases hpath : G.HasIntegerPath S (G.endAt e 0) (G.endAt e 1)
  · exact Or.inl (G.hasCycleCorrection_of_integerPath S e he hpath)
  -- the vertices reachable from the tail of `e` by chains avoiding `S`
  refine Or.inr ⟨Finset.univ.filter fun w => G.HasIntegerPath S (G.endAt e 0) w, ?_, ?_⟩
  · -- `e` itself crosses: its tail is reachable, its head is not
    have h0 : G.endAt e 0 ∈ Finset.univ.filter fun w => G.HasIntegerPath S (G.endAt e 0) w := by
      simpa using G.hasIntegerPath_refl S (G.endAt e 0)
    have h1 : G.endAt e 1 ∉ Finset.univ.filter fun w => G.HasIntegerPath S (G.endAt e 0) w := by
      simpa using hpath
    exact (G.crosses_iff _ e).2 fun hiff => h1 (hiff.1 h0)
  · -- no allowed edge crosses: it joins two mutually reachable vertices
    intro k hk
    have hedge : G.HasIntegerPath S (G.endAt k 0) (G.endAt k 1) := G.hasIntegerPath_single S k hk
    refine (G.not_crosses_iff _ k).2 ⟨fun h0 => ?_, fun h1 => ?_⟩
    · have hreach : G.HasIntegerPath S (G.endAt e 0) (G.endAt k 0) := by simpa using h0
      simpa using HasIntegerPath.trans G hreach hedge
    · have hreach : G.HasIntegerPath S (G.endAt e 0) (G.endAt k 1) := by simpa using h1
      simpa using HasIntegerPath.trans G hreach (HasIntegerPath.symm G hedge)

/-- **Tutte's group-order invariance for nowhere-zero flows**, unconditional: the
number of nowhere-zero `A`-flows on a finite graph depends only on
`Fintype.card A`. -/
theorem tutteFlowCardinalityInvariant : G.FlowCardinalityInvariant :=
  G.flowCardinalityInvariant_of_pathCut G.integralPathCutDichotomy

/-- The concrete order-eight coefficient transfer used by the CDC construction:
a nowhere-zero `ZMod 8`-flow yields a nowhere-zero `Gamma = F₂³`-flow, even though
the two groups are not isomorphic. -/
theorem zmodEight_to_gamma_unconditional :
    Nonempty (G.NowhereZeroFlow (ZMod 8)) → Nonempty (G.NowhereZeroFlow Gamma) :=
  G.zmodEight_to_gamma G.tutteFlowCardinalityInvariant

/-- Seymour's integral six-flow conclusion yields a nowhere-zero `Gamma`-flow,
with no remaining hypothesis: reduce mod eight (step 5a) and transfer. -/
theorem sixFlow_to_gamma_unconditional :
    Nonempty G.SixFlow → Nonempty (G.NowhereZeroFlow Gamma) :=
  G.sixFlow_to_gamma G.tutteFlowCardinalityInvariant

/-- Every bridgeless graph carries a nowhere-zero `Gamma`-flow, *given* Seymour's
six-flow theorem. As in step 5a, Seymour's theorem is carried as the explicit
hypothesis `SeymourSixFlowStatement` (the trust boundary fixed in step 1) rather
than as an ambient axiom, so the Lean content here is unconditional: the whole
chain from an integral 6-flow to an `F₂³`-flow is now proved. -/
theorem nonempty_nowhereZeroFlow_gamma_of_seymour
    (hs : SeymourSixFlowStatement.{u, v}) (hb : G.Bridgeless) :
    Nonempty (G.NowhereZeroFlow Gamma) :=
  G.sixFlow_to_gamma_unconditional (hs V E G hb)

end FiniteGraph

end CycleDoubleCover
