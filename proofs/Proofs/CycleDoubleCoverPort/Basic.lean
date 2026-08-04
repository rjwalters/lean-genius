import Proofs.CycleDoubleCoverPort.GeneralGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Prod

/-
# Cycle Double Cover port, step 2a: cubic multigraphs and Γ-flows

Second slice of the port of the openai/cdc-lean development of the Cycle Double
Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery.
It corresponds to upstream `CDCLean/Basic.lean`; see #37507 for the porting
order and step 1 (#43625) for `GeneralGraph.lean` / `CycleDecomposition.lean`.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin. Where upstream
discharges a goal by `simp`, the proofs below are given in term mode or by
explicit `calc` chains; the two finite case analyses are packaged as standalone
`decide`-checked combinatorial lemmas rather than inlined `omega` calls.

## Mathematical content

A *cubic* multigraph is encoded by an equivalence

  `incidence : (V × Fin 3) ≃ (E × Fin 2)`

between the three local slots at each vertex and the two numbered ends of each
edge. This presentation has three virtues over "every vertex has degree 3"
stated as a cardinality:

* parallel edges stay genuinely distinct, because `E` is a type of edge objects
  rather than a set of vertex pairs;
* 3-regularity is definitional — no vertex can reuse an edge accidentally,
  since `incidence` is a bijection;
* the handshake double count becomes reindexing along an equivalence
  (`sum_edgeEnds_eq_sum_vertexSlots`), so no combinatorial bookkeeping is
  needed downstream.

`loopless` is stated on the *edge* side: the two ends of an edge sit at
distinct vertices.

A `GammaFlow` is a nowhere-zero flow valued in `Gamma = F₂³`. In characteristic
two orientation signs vanish (`x = -x`), so conservation at `v` is simply that
the three slot values at `v` sum to zero. The extra lemma
`GammaFlow.val_edgeAt_ne` records the first real consequence: the three values
around a vertex are pairwise distinct, hence form one of the seven nonzero
`Gamma` values' triples summing to zero — the finite fact the labelling stage
of the proof runs on.

This file does **not** discharge `CycleDoubleCover.cycleDoubleCover_of_bridgeless`;
that is done in
`CycleDoubleCoverPort/Main.lean`, the last file of the port.

## Relationship to the general encoding

The bridge `CubicGraph.toFiniteGraph` (forgetting the slot structure) and the
translation between `GammaFlow` and `FiniteGraph.NowhereZeroFlow Gamma` live in
upstream `CubicBridge.lean` and are deliberately **not** ported here — they
belong to step 3 of the porting order.
-/

namespace CycleDoubleCover

/-- A finite cubic multigraph. `incidence` matches each of the three local slots
at every vertex with exactly one of the two numbered ends of an edge, so
3-regularity holds definitionally and parallel edges remain distinct objects.
`loopless` says the two ends of any edge lie at distinct vertices. -/
structure CubicGraph (V E : Type*) [Fintype V] [Fintype E] where
  incidence : (V × Fin 3) ≃ (E × Fin 2)
  loopless : ∀ e : E,
    (incidence.symm (e, 0)).1 ≠ (incidence.symm (e, 1)).1

namespace CubicGraph

variable {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E)

/-- The edge object occupying local slot `i` at the vertex `v`. -/
def edgeAt (v : V) (i : Fin 3) : E := (G.incidence (v, i)).1

/-- The vertex at end number `j` of the edge object `e`. -/
def endAt (e : E) (j : Fin 2) : V := (G.incidence.symm (e, j)).1

/-- `loopless` restated through `endAt`. This is the form matching the field of
`FiniteGraph` in `Proofs/CycleDoubleCover.lean`, and it holds by definition. -/
theorem endAt_zero_ne_one (e : E) : G.endAt e 0 ≠ G.endAt e 1 := G.loopless e

@[simp]
theorem incidence_symm_edgeAt (v : V) (i : Fin 3) :
    (G.incidence.symm (G.incidence (v, i))).1 = v :=
  congrArg Prod.fst (G.incidence.symm_apply_apply (v, i))

/-- Walking from a vertex slot to the edge and back returns the same vertex. -/
@[simp]
theorem endAt_edgeAt_incidence (v : V) (i : Fin 3) :
    G.endAt (G.edgeAt v i) (G.incidence (v, i)).2 = v :=
  congrArg Prod.fst (G.incidence.symm_apply_apply (v, i))

/-- Walking from an edge end to the vertex and back returns the same edge. -/
@[simp]
theorem edgeAt_incidence_symm (e : E) (j : Fin 2) :
    G.edgeAt (G.endAt e j) (G.incidence.symm (e, j)).2 = e :=
  congrArg Prod.fst (G.incidence.apply_symm_apply (e, j))

/-- The two elements of `Fin 2` are `0` and `1`, in one order or the other.
Checked exhaustively by the kernel. -/
private theorem fin_two_ne_cases :
    ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide

/-- The three slots at a vertex carry three *different* edge objects: a vertex
cannot see the same edge twice. If it did, that edge would have both of its
ends at the vertex, contradicting looplessness. -/
theorem edgeAt_injective (v : V) : Function.Injective (G.edgeAt v) := by
  intro i k hik
  by_cases hj : (G.incidence (v, i)).2 = (G.incidence (v, k)).2
  · -- Same edge and same end number: the incidence images coincide outright.
    have hpair : G.incidence (v, i) = G.incidence (v, k) := Prod.ext hik hj
    exact congrArg Prod.snd (G.incidence.injective hpair)
  · -- Different end numbers: both ends of `G.edgeAt v i` would sit at `v`.
    exfalso
    have hi : G.endAt (G.edgeAt v i) (G.incidence (v, i)).2 = v :=
      G.endAt_edgeAt_incidence v i
    have hk : G.endAt (G.edgeAt v i) (G.incidence (v, k)).2 = v := by
      rw [hik]
      exact G.endAt_edgeAt_incidence v k
    rcases fin_two_ne_cases _ _ hj with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha] at hi
      rw [hb] at hk
      exact G.endAt_zero_ne_one (G.edgeAt v i) (hi.trans hk.symm)
    · rw [ha] at hi
      rw [hb] at hk
      exact G.endAt_zero_ne_one (G.edgeAt v i) (hk.trans hi.symm)

/-- Handshake, in the reindexing form the later stages actually consume: a sum
over all edge ends equals the same sum read off the vertex slots. This is
exactly transport along `incidence`, so no counting argument is involved. -/
theorem sum_edgeEnds_eq_sum_vertexSlots
    {A : Type*} [AddCommMonoid A] (h : E → Fin 2 → A) :
    ∑ e : E, ∑ j : Fin 2, h e j =
      ∑ v : V, ∑ i : Fin 3,
        h (G.edgeAt v i) (G.incidence (v, i)).2 := by
  -- Uncurry both iterated sums, then transport the single sum along `incidence`.
  have hL : ∑ q : E × Fin 2, h q.1 q.2 = ∑ e : E, ∑ j : Fin 2, h e j :=
    Fintype.sum_prod_type' h
  have hR : ∑ p : V × Fin 3,
      h (G.edgeAt p.1 p.2) (G.incidence (p.1, p.2)).2 =
        ∑ v : V, ∑ i : Fin 3, h (G.edgeAt v i) (G.incidence (v, i)).2 :=
    Fintype.sum_prod_type' (fun v i => h (G.edgeAt v i) (G.incidence (v, i)).2)
  have hE : ∑ p : V × Fin 3, h (G.incidence p).1 (G.incidence p).2 =
      ∑ q : E × Fin 2, h q.1 q.2 :=
    G.incidence.sum_comp (fun q : E × Fin 2 => h q.1 q.2)
  rw [← hL, ← hR]
  exact hE.symm

include G in
/-- The numerical shadow of `incidence`: a cubic multigraph has `3|V| = 2|E|`.
Recorded as a sanity check that the slot encoding really is 3-regular. -/
theorem card_slots_eq_card_ends : Fintype.card V * 3 = Fintype.card E * 2 := by
  have h := Fintype.card_congr G.incidence
  simpa [Fintype.card_prod] using h

end CubicGraph

/-- `Gamma` has characteristic two: every element is its own additive inverse.
Eight elements, checked by the kernel. -/
theorem gamma_add_self : ∀ x : Gamma, x + x = 0 := by decide

/-- A nowhere-zero `Gamma = F₂³` flow on a cubic multigraph. In characteristic
two every element is its own negation, so the orientation signs of the general
flow condition cancel and conservation at `v` is the vanishing of the sum over
the three local slots. -/
structure GammaFlow {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) where
  val : E → Gamma
  nowhereZero : ∀ e, val e ≠ 0
  conservation : ∀ v, ∑ i : Fin 3, val (G.edgeAt v i) = 0

namespace GammaFlow

variable {V E : Type*} [Fintype V] [Fintype E] {G : CubicGraph V E}

/-- Conservation with the three-term sum spelled out. -/
theorem sum_three (f : GammaFlow G) (v : V) :
    f.val (G.edgeAt v 0) + f.val (G.edgeAt v 1) + f.val (G.edgeAt v 2) = 0 := by
  have h := f.conservation v
  rwa [Fin.sum_univ_three] at h

/-- In characteristic two, two equal summands of a vanishing triple force the
third to vanish. -/
private theorem third_eq_zero {x y z : Gamma} (hsum : x + y + z = 0) (hxy : x = y) :
    z = 0 := by
  subst hxy
  rwa [gamma_add_self, zero_add] at hsum

/-- Case split on an ordered pair of distinct elements of `Fin 3`. Checked
exhaustively by the kernel. -/
private theorem fin_three_ne_cases :
    ∀ i j : Fin 3, i ≠ j →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨
      (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by decide

/-- The three flow values around a vertex are pairwise distinct. If two of them
agreed, the third would be forced to zero by conservation in characteristic
two, contradicting nowhere-zeroness. Consequently each vertex sees three of the
seven nonzero elements of `Gamma`, summing to zero — the configuration the
labelling stage of the proof exploits. -/
theorem val_edgeAt_ne (f : GammaFlow G) (v : V) {i j : Fin 3} (hij : i ≠ j) :
    f.val (G.edgeAt v i) ≠ f.val (G.edgeAt v j) := by
  have h01 : f.val (G.edgeAt v 0) ≠ f.val (G.edgeAt v 1) := fun hEq =>
    f.nowhereZero (G.edgeAt v 2) (third_eq_zero (f.sum_three v) hEq)
  have h02 : f.val (G.edgeAt v 0) ≠ f.val (G.edgeAt v 2) := fun hEq =>
    f.nowhereZero (G.edgeAt v 1)
      (third_eq_zero (by linear_combination f.sum_three v) hEq)
  have h12 : f.val (G.edgeAt v 1) ≠ f.val (G.edgeAt v 2) := fun hEq =>
    f.nowhereZero (G.edgeAt v 0)
      (third_eq_zero (by linear_combination f.sum_three v) hEq)
  rcases fin_three_ne_cases i j hij with
      ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    subst ha <;> subst hb
  · exact h01
  · exact h01.symm
  · exact h02
  · exact h02.symm
  · exact h12
  · exact h12.symm

end GammaFlow

end CycleDoubleCover
