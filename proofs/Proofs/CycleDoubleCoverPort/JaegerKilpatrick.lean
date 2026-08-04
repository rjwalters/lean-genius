import Proofs.CycleDoubleCoverPort.JaegerKilpatrickPacking
import Proofs.CycleDoubleCoverPort.JaegerKilpatrickContraction

-- Ported from openai/cdc-lean, JaegerKilpatrick.lean (lines 795-1219), vendored with
-- adaptation per operator decision 2026-08-03. Part of epic #37507. Completes the
-- upstream file (segments in JaegerKilpatrickEvenCover/Packing/Contraction).

/-
# Jaeger--Kilpatrick, segment 4: component decomposition and the eight-flow theorem

This is the final segment of the port of upstream `JaegerKilpatrick.lean` and the
capstone of the Jaeger--Kilpatrick half of the Cycle Double Cover port. The three
earlier segments supply the two halves of the recursion:

* `JaegerKilpatrickEvenCover` / `JaegerKilpatrickPacking` prove
  `nowhereZeroGammaFlow_of_threeEdgeConnected`: a three-edge-connected graph has a
  nowhere-zero `Gamma`-flow, via three spanning trees packed in the doubled graph.
* `JaegerKilpatrickContraction` proves
  `nowhereZeroGammaFlow_of_contractEdge_of_twoCut`: a `Gamma`-flow on the contraction
  of one edge of a two-edge cut lifts back across that cut.

This file closes the loop:

* **The recursion** (`jaegerKilpatrickEightFlow_connected`). A *connected* bridgeless
  graph either is three-edge-connected — and the packing segment applies directly —
  or has a proper nonempty cut with fewer than three edges. Bridgelessness forbids
  one edge and `cut_nonempty_of_connects` forbids zero, so the cut has exactly two
  edges; contracting one of them (`contractEdge_connects_univ` keeps connectedness,
  `contractEdge_bridgeless` keeps bridgelessness) and recursing gives a flow that the
  contraction segment lifts. `card_contractEdge_lt` — a contracted quotient is
  strictly smaller because the two ends of the contracted edge are distinct — is the
  well-founded measure. Note the recursion re-enters at a *different* type
  instantiation (the contracted quotient/subtype), which is why the theorem is stated
  for a fresh `K : FiniteGraph W F` rather than for the section variable `H`, and why
  `card_contractEdge_lt` must precede it in the same file.

* **The decomposition** (`componentGraph` and friends). A general bridgeless graph
  need not be connected, so `V` is split along `componentSetoid Finset.univ`. Each
  class `q` carries the induced graph on `ComponentVertex q` / `ComponentEdge q`
  (`componentGraph`), which is connected (`componentGraph_connects_univ`) and
  bridgeless (`componentGraph_bridgeless`, via `mem_componentGraph_cut_iff`: a cut of
  a component is a cut of the whole graph). `ComponentEdge` selects edges by their
  *first* endpoint, which is well defined precisely because
  `endpoints_componentSetoid_rel` puts both ends of an edge in one component.

* **The assembly** (`jaegerKilpatrickEightFlow_of_nonempty`, then
  `jaegerKilpatrickEightFlow`). Choose a flow on each component and glue: the value
  of an edge is its value in the component of its first endpoint. Conservation at `v`
  reduces to conservation in the component of `v` because every edge incident to `v`
  lies in that component (`component_eq_of_endAt_eq`), so the sum over `E` collapses
  to a sum over `ComponentEdge q` (`Finset.sum_subtype_eq_sum_filter`). The
  vertex-empty case is handled separately, giving the unconditional statement.

The final theorem, `jaegerKilpatrickEightFlow`, is the group-valued eight-flow
theorem: every bridgeless finite multigraph carries a nowhere-zero flow with values
in `Gamma = (ZMod 2)^3`. It is the input to the `CubicLabeling` / `CubicTheorem`
half of the port, which converts an eight-flow into an exact cycle double cover.

## Provenance, licensing and attribution

Ported from `openai/cdc-lean`, `CDCLean/JaegerKilpatrick.lean` (lines 795-1219),
vendored with adaptation per the operator decision recorded on #37507 (comment of
2026-08-03). `openai/cdc-lean` carries **no license file**, so default copyright
applies; the operator's decision is an explicit *risk acceptance*, not a license.
The mathematical content and the proof scripts originate with `openai/cdc-lean`.

## Adaptations from upstream

* Namespace: upstream `CDCLean.FiniteGraph` becomes `CycleDoubleCover.FiniteGraph`.
  `FiniteGraph`, `Crosses`, `cut` and `Bridgeless` come from
  `Proofs/CycleDoubleCover.lean`; `Gamma` and `NowhereZeroFlow` from
  `CycleDoubleCoverPort/GeneralGraph.lean`; `supportGraph`, `Connects`,
  `ReachableIn`, `componentSetoid`, `reachable_map_of_adj_reachable` and the
  `instFintypeQuotientSetoid` instance from `CycleDoubleCoverPort/NashWilliams.lean`.
* Declaration names are unchanged from upstream, so that the assembly file (`Main`)
  can call `jaegerKilpatrickEightFlow` by its upstream name.
* Upstream's `push Not at h3` is kept verbatim: the generalized `push` tactic is
  present in this repository's pin (`push_neg` is the deprecated spelling).
-/

namespace CycleDoubleCover

namespace FiniteGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (H : FiniteGraph V E)

omit [DecidableEq E] in
/-- A nontrivial vertex shore of a connected graph has a crossing edge. -/
theorem cut_nonempty_of_connects [Nonempty V] (hconn : H.Connects Finset.univ)
    (S : Finset V) (hS : S.Nonempty) (hSne : S ≠ Finset.univ) :
    (H.cut S).Nonempty := by
  classical
  by_contra hcut
  have hcutempty : H.cut S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcut
  obtain ⟨u, hu⟩ := hS
  have hcompl : (Finset.univ \ S).Nonempty :=
    Finset.sdiff_nonempty.mpr (by simpa using hSne)
  obtain ⟨v, hv⟩ := hcompl
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
  have hreach := hconn.preconnected u v
  rcases hreach with ⟨p⟩
  have hprop : ∀ {x y : V}, (H.supportGraph Finset.univ).Adj x y →
      x ∈ S → y ∈ S := by
    intro x y hxy hx
    rw [H.supportGraph_adj_iff Finset.univ x y] at hxy
    rcases hxy with ⟨_, e, _, hends | hends⟩
    · by_contra hy
      have hecut : e ∈ H.cut S := by
        simp [cut, Crosses, hends.1, hends.2, hx, hy]
      rw [hcutempty] at hecut
      simp at hecut
    · by_contra hy
      have hecut : e ∈ H.cut S := by
        simp [cut, Crosses, hends.1, hends.2, hx, hy]
      rw [hcutempty] at hecut
      simp at hecut
  have hvmem : v ∈ S := by
    have hwalk : ∀ {x y : V} (p : (H.supportGraph Finset.univ).Walk x y),
        x ∈ S → y ∈ S := by
      intro x y p
      induction p with
      | nil => intro hx; exact hx
      | @cons x y z hxy p ih =>
          intro hx
          exact ih (hprop hxy hx)
    exact hwalk p hu
  exact (hvS hvmem).elim

omit [DecidableEq V] [DecidableEq E] in
/-- Contracting an edge preserves connectedness after the resulting loops are discarded. -/
theorem contractEdge_connects_univ [Nonempty V] (e : E)
    (hconn : H.Connects Finset.univ) :
    (H.contractEdge e).Connects Finset.univ := by
  classical
  letI : Nonempty (Quotient (H.contractEdgeSetoid e)) :=
    Nonempty.map (Quotient.mk (H.contractEdgeSetoid e)) inferInstance
  refine { preconnected := ?_ }
  intro q r
  induction q using Quotient.inductionOn with
  | _ u =>
      induction r using Quotient.inductionOn with
      | _ v =>
          apply FiniteGraph.reachable_map_of_adj_reachable
            (fun x => Quotient.mk (H.contractEdgeSetoid e) x)
          · intro x y hxy
            rw [H.supportGraph_adj_iff Finset.univ x y] at hxy
            rcases hxy with ⟨hxy, f, _, hends | hends⟩
            · by_cases hf : H.SurvivesContraction e f
              · apply SimpleGraph.Adj.reachable
                rw [(H.contractEdge e).supportGraph_adj_iff Finset.univ]
                exact ⟨by
                  intro h
                  apply hf
                  simpa [hends.1, hends.2] using Quotient.eq'.mp h, ⟨f, hf⟩, by simp,
                  Or.inl ⟨by simp [contractEdge, hends.1],
                    by simp [contractEdge, hends.2]⟩⟩
              · have hEq : Quotient.mk (H.contractEdgeSetoid e) x =
                    Quotient.mk (H.contractEdgeSetoid e) y := by
                  apply Quotient.sound
                  simpa [hends.1, hends.2] using not_not.mp hf
                rw [hEq]
            · by_cases hf : H.SurvivesContraction e f
              · apply SimpleGraph.Adj.reachable
                rw [(H.contractEdge e).supportGraph_adj_iff Finset.univ]
                exact ⟨by
                  intro h
                  apply hf
                  simpa [hends.1, hends.2] using
                    (H.contractEdgeSetoid e).symm (Quotient.eq'.mp h), ⟨f, hf⟩, by simp,
                  Or.inr ⟨by simp [contractEdge, hends.1],
                    by simp [contractEdge, hends.2]⟩⟩
              · have hEq : Quotient.mk (H.contractEdgeSetoid e) x =
                    Quotient.mk (H.contractEdgeSetoid e) y := by
                  apply Quotient.sound
                  simpa [hends.1, hends.2] using
                    (H.contractEdgeSetoid e).symm (not_not.mp hf)
                rw [hEq]
          · exact hconn.preconnected u v

omit [DecidableEq V] [DecidableEq E] in
theorem card_contractEdge_lt [Nonempty V] (e : E) :
    Fintype.card (Quotient (H.contractEdgeSetoid e)) < Fintype.card V := by
  apply Fintype.card_lt_of_surjective_not_injective
    (Quotient.mk (H.contractEdgeSetoid e))
  · intro q
    induction q using Quotient.inductionOn with
    | _ v => exact ⟨v, rfl⟩
  · intro hinj
    apply H.loopless e
    apply hinj
    apply Quotient.sound
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Connected bridgeless graphs have a nowhere-zero `Gamma`-flow.  A two-edge cut is
contracted recursively; when no such cut remains, the doubled-edge tree packing above
applies. -/
theorem jaegerKilpatrickEightFlow_connected
    {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
    (K : FiniteGraph W F) [Nonempty W]
    (hconn : K.Connects Finset.univ) (hb : K.Bridgeless) :
    Nonempty (K.NowhereZeroFlow Gamma) := by
  classical
  by_cases h3 : K.IsThreeEdgeConnected
  · exact K.nowhereZeroGammaFlow_of_threeEdgeConnected h3
  · unfold IsThreeEdgeConnected at h3
    push Not at h3
    obtain ⟨S, hS, hSne, hlt⟩ := h3
    have hcutne : (K.cut S).Nonempty := K.cut_nonempty_of_connects hconn S hS hSne
    have hcardne : (K.cut S).card ≠ 1 := hb S
    have hcard : (K.cut S).card = 2 := by
      have hpos := hcutne.card_pos
      omega
    obtain ⟨e₁, e₂, he₁₂, hcut⟩ := Finset.card_eq_two.mp hcard
    have he₁ : e₁ ∈ K.cut S := by simp [hcut]
    have he₂ : e₂ ∈ K.cut S := by simp [hcut]
    letI : Nonempty (Quotient (K.contractEdgeSetoid e₁)) :=
      Nonempty.map (Quotient.mk (K.contractEdgeSetoid e₁)) inferInstance
    have hrec : Nonempty ((K.contractEdge e₁).NowhereZeroFlow Gamma) :=
      jaegerKilpatrickEightFlow_connected (K.contractEdge e₁)
        (K.contractEdge_connects_univ e₁ hconn) (K.contractEdge_bridgeless e₁ hb)
    exact K.nowhereZeroGammaFlow_of_contractEdge_of_twoCut S hcut he₁ he₁₂ hrec
termination_by Fintype.card W
decreasing_by
  exact K.card_contractEdge_lt e₁

omit [DecidableEq V] [DecidableEq E] in
/-- The component relation of the full support graph relates the two ends of every edge. -/
theorem endpoints_componentSetoid_rel (e : E) :
    (H.componentSetoid Finset.univ).r (H.endAt e 0) (H.endAt e 1) := by
  change (H.supportGraph Finset.univ).Reachable (H.endAt e 0) (H.endAt e 1)
  apply SimpleGraph.Adj.reachable
  rw [H.supportGraph_adj_iff Finset.univ]
  exact ⟨H.loopless e, e, by simp, Or.inl ⟨rfl, rfl⟩⟩

/-- Vertices of one connected component of the full support graph. -/
abbrev ComponentVertex (q : Quotient (H.componentSetoid Finset.univ)) :=
  {v : V // Quotient.mk (H.componentSetoid Finset.univ) v = q}

/-- Edge objects whose first endpoint lies in one connected component. -/
abbrev ComponentEdge (q : Quotient (H.componentSetoid Finset.univ)) :=
  {e : E // Quotient.mk (H.componentSetoid Finset.univ) (H.endAt e 0) = q}

noncomputable instance componentVertexFintype
    (q : Quotient (H.componentSetoid Finset.univ)) : Fintype (H.ComponentVertex q) :=
  Fintype.ofFinite _

noncomputable instance componentEdgeFintype
    (q : Quotient (H.componentSetoid Finset.univ)) : Fintype (H.ComponentEdge q) :=
  Fintype.ofFinite _

/-- The finite graph induced by one connected component, keeping genuine edge objects. -/
noncomputable def componentGraph
    (q : Quotient (H.componentSetoid Finset.univ)) :
    FiniteGraph (H.ComponentVertex q) (H.ComponentEdge q) where
  endAt e i := if i = 0 then
      ⟨H.endAt e.1 0, e.2⟩
    else
      ⟨H.endAt e.1 1, by
        have hEq : Quotient.mk (H.componentSetoid Finset.univ) (H.endAt e.1 1) =
            Quotient.mk (H.componentSetoid Finset.univ) (H.endAt e.1 0) :=
          (Quotient.sound (H.endpoints_componentSetoid_rel e.1)).symm
        exact hEq.trans e.2⟩
  loopless := by
    intro e h
    apply H.loopless e.1
    exact congrArg Subtype.val h

omit [DecidableEq V] [DecidableEq E] in
theorem componentGraph_connects_univ
    (q : Quotient (H.componentSetoid Finset.univ)) :
    (H.componentGraph q).Connects Finset.univ := by
  classical
  letI : Nonempty (H.ComponentVertex q) := by
    induction q using Quotient.inductionOn with
    | _ v => exact ⟨⟨v, rfl⟩⟩
  refine { preconnected := ?_ }
  intro u v
  have huvRel : (H.componentSetoid Finset.univ).r u.1 v.1 :=
    Quotient.eq'.mp (u.2.trans v.2.symm)
  change (H.supportGraph Finset.univ).Reachable u.1 v.1 at huvRel
  rcases huvRel with ⟨p⟩
  have hwalk : ∀ {x y : V} (p : (H.supportGraph Finset.univ).Walk x y)
      (hx : Quotient.mk (H.componentSetoid Finset.univ) x = q)
      (hy : Quotient.mk (H.componentSetoid Finset.univ) y = q),
      (H.componentGraph q).ReachableIn Finset.univ ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y p
    induction p with
    | nil =>
        intro hx _
        exact SimpleGraph.Reachable.refl (⟨_, hx⟩ : H.ComponentVertex q)
    | @cons x y z hxy p ih =>
        intro hx hz
        have hxyRel : (H.componentSetoid Finset.univ).r x y := by
          change (H.supportGraph Finset.univ).Reachable x y
          exact SimpleGraph.Adj.reachable hxy
        have hy : Quotient.mk (H.componentSetoid Finset.univ) y = q :=
          (Quotient.sound hxyRel).symm.trans hx
        have hstep : ((H.componentGraph q).supportGraph Finset.univ).Adj
            ⟨x, hx⟩ ⟨y, hy⟩ := by
          rw [(H.componentGraph q).supportGraph_adj_iff Finset.univ]
          rw [H.supportGraph_adj_iff Finset.univ x y] at hxy
          rcases hxy with ⟨hxy, e, _, hends | hends⟩
          · let e' : H.ComponentEdge q := ⟨e, by simpa [hends.1] using hx⟩
            refine ⟨by
              intro h
              exact hxy (congrArg Subtype.val h), e', by simp, Or.inl ⟨?_, ?_⟩⟩
            · apply Subtype.ext
              simp [componentGraph, e', hends.1]
            · apply Subtype.ext
              simp [componentGraph, e', hends.2]
          · let e' : H.ComponentEdge q := ⟨e, by simpa [hends.1] using hy⟩
            refine ⟨by
              intro h
              exact hxy (congrArg Subtype.val h), e', by simp, Or.inr ⟨?_, ?_⟩⟩
            · apply Subtype.ext
              simp [componentGraph, e', hends.1]
            · apply Subtype.ext
              simp [componentGraph, e', hends.2]
        exact (SimpleGraph.Adj.reachable hstep).trans (ih hy hz)
  exact hwalk p u.2 v.2

omit [DecidableEq E] in
theorem mem_componentGraph_cut_iff
    (q : Quotient (H.componentSetoid Finset.univ))
    (A : Finset (H.ComponentVertex q)) (e : H.ComponentEdge q) :
    e ∈ (H.componentGraph q).cut A ↔
      e.1 ∈ H.cut (A.image Subtype.val) := by
  classical
  simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, Crosses]
  have hmem (w : H.ComponentVertex q) :
      w.1 ∈ A.image Subtype.val ↔ w ∈ A := by
    constructor
    · rw [Finset.mem_image]
      rintro ⟨z, hz, hzw⟩
      have hEq : z = w := by
        apply Subtype.ext
        exact hzw
      simpa [hEq] using hz
    · intro hw
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hval0 : ((H.componentGraph q).endAt e 0).1 = H.endAt e.1 0 := by
    simp [componentGraph]
  have hval1 : ((H.componentGraph q).endAt e 1).1 = H.endAt e.1 1 := by
    simp [componentGraph]
  rw [← hval0, ← hval1, hmem ((H.componentGraph q).endAt e 0),
    hmem ((H.componentGraph q).endAt e 1)]

omit [DecidableEq E] in
/-- A connected component of a bridgeless graph is bridgeless. -/
theorem componentGraph_bridgeless
    (q : Quotient (H.componentSetoid Finset.univ)) (hb : H.Bridgeless) :
    (H.componentGraph q).Bridgeless := by
  classical
  intro A hcard
  obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hcard
  let S : Finset V := A.image Subtype.val
  have hcut : H.cut S = {e.1} := by
    ext f
    constructor
    · intro hf
      have hcross : H.Crosses S f := (Finset.mem_filter.mp hf).2
      have h0or1 : H.endAt f 0 ∈ S ∨ H.endAt f 1 ∈ S := by
        unfold Crosses at hcross
        by_cases h0 : H.endAt f 0 ∈ S <;> by_cases h1 : H.endAt f 1 ∈ S <;>
          simp [h0, h1] at hcross ⊢
      have hfq : Quotient.mk (H.componentSetoid Finset.univ) (H.endAt f 0) = q := by
        rcases h0or1 with h0 | h1
        · rcases Finset.mem_image.mp h0 with ⟨v, _, hv⟩
          simpa [hv] using v.2
        · rcases Finset.mem_image.mp h1 with ⟨v, _, hv⟩
          have hEq : Quotient.mk (H.componentSetoid Finset.univ) (H.endAt f 0) =
              Quotient.mk (H.componentSetoid Finset.univ) (H.endAt f 1) :=
            Quotient.sound (H.endpoints_componentSetoid_rel f)
          exact hEq.trans (by simpa [hv] using v.2)
      let f' : H.ComponentEdge q := ⟨f, hfq⟩
      have hf' : f' ∈ (H.componentGraph q).cut A :=
        (H.mem_componentGraph_cut_iff q A f').2 hf
      have hfe : f' = e := by simpa [heq] using hf'
      simpa using congrArg Subtype.val hfe
    · intro hf
      have hfe : f = e.1 := by simpa using hf
      subst f
      have he : e ∈ (H.componentGraph q).cut A := by simp [heq]
      exact (H.mem_componentGraph_cut_iff q A e).1 he
  apply hb S
  rw [hcut]
  simp

omit [DecidableEq V] [DecidableEq E] in
theorem component_eq_of_endAt_eq {e : E} {v : V} (j : Fin 2)
    (h : H.endAt e j = v) :
    Quotient.mk (H.componentSetoid Finset.univ) (H.endAt e 0) =
      Quotient.mk (H.componentSetoid Finset.univ) v := by
  classical
  fin_cases j
  · exact congrArg (Quotient.mk (H.componentSetoid Finset.univ)) h
  · have hEq : Quotient.mk (H.componentSetoid Finset.univ) (H.endAt e 0) =
        Quotient.mk (H.componentSetoid Finset.univ) (H.endAt e 1) :=
      Quotient.sound (H.endpoints_componentSetoid_rel e)
    exact hEq.trans (congrArg (Quotient.mk (H.componentSetoid Finset.univ)) h)

/-- The nonempty-vertex case of Jaeger--Kilpatrick's eight-flow theorem. -/
theorem jaegerKilpatrickEightFlow_of_nonempty [Nonempty V] (hb : H.Bridgeless) :
    Nonempty (H.NowhereZeroFlow Gamma) := by
  classical
  let P := H.componentSetoid Finset.univ
  have hcomp : ∀ q : Quotient P,
      Nonempty ((H.componentGraph q).NowhereZeroFlow Gamma) := by
    intro q
    letI : Nonempty (H.ComponentVertex q) := by
      induction q using Quotient.inductionOn with
      | _ v => exact ⟨⟨v, rfl⟩⟩
    apply jaegerKilpatrickEightFlow_connected (H.componentGraph q)
    · exact H.componentGraph_connects_univ q
    · exact H.componentGraph_bridgeless q hb
  let ψ : ∀ q : Quotient P, (H.componentGraph q).NowhereZeroFlow Gamma :=
    fun q => Classical.choice (hcomp q)
  let φ : E → Gamma := fun e =>
    let q : Quotient P := Quotient.mk P (H.endAt e 0)
    (ψ q).val ⟨e, rfl⟩
  refine ⟨⟨φ, ?_, ?_⟩⟩
  · intro v
    let q : Quotient P := Quotient.mk P v
    have hsum (j : Fin 2) :
        (∑ e : E, if H.endAt e j = v then φ e else 0) =
          ∑ e : H.ComponentEdge q,
            if (H.componentGraph q).endAt e j = (⟨v, rfl⟩ : H.ComponentVertex q)
              then (ψ q).val e else 0 := by
      let g : E → Gamma := fun e =>
        if heq : Quotient.mk P (H.endAt e 0) = q then
          if H.endAt e j = v then (ψ q).val ⟨e, heq⟩ else 0
        else 0
      calc
        (∑ e : E, if H.endAt e j = v then φ e else 0) =
            ∑ e : E, g e := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases hev : H.endAt e j = v
          · have heq : Quotient.mk P (H.endAt e 0) = q := by
              exact H.component_eq_of_endAt_eq j hev
            have hφ : φ e = (ψ q).val ⟨e, heq⟩ := by
              have hφ_of_eq : ∀ (q' : Quotient P)
                  (heq' : Quotient.mk P (H.endAt e 0) = q'),
                  φ e = (ψ q').val ⟨e, heq'⟩ := by
                intro q' heq'
                subst q'
                rfl
              exact hφ_of_eq q heq
            simp [g, heq, hev, hφ]
          · simp [g, hev]
        _ = ∑ e : H.ComponentEdge q, g e.1 := by
          calc
            (∑ e : E, g e) =
                ∑ e ∈ (Finset.univ.filter fun e =>
                  Quotient.mk P (H.endAt e 0) = q), g e := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro e _
              by_cases heq : Quotient.mk P (H.endAt e 0) = q <;>
                simp [g, heq]
            _ = ∑ e : H.ComponentEdge q, g e.1 := by
              symm
              simpa [P] using (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset E))
                (p := fun e => Quotient.mk P (H.endAt e 0) = q) g)
        _ = ∑ e : H.ComponentEdge q,
            if (H.componentGraph q).endAt e j = (⟨v, rfl⟩ : H.ComponentVertex q)
              then (ψ q).val e else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          have hval : ((H.componentGraph q).endAt e j).1 = H.endAt e.1 j := by
            fin_cases j <;> simp [componentGraph]
          have hiff : H.endAt e.1 j = v ↔
              (H.componentGraph q).endAt e j =
                (⟨v, rfl⟩ : H.ComponentVertex q) := by
            constructor
            · intro h
              apply Subtype.ext
              exact hval.trans h
            · intro h
              exact hval.symm.trans (congrArg Subtype.val h)
          change (if heq : Quotient.mk P (H.endAt e.1 0) = q then
              if H.endAt e.1 j = v then (ψ q).val ⟨e.1, heq⟩ else 0
            else 0) =
            if (H.componentGraph q).endAt e j =
                (⟨v, rfl⟩ : H.ComponentVertex q) then (ψ q).val e else 0
          rw [dif_pos e.2]
          simp [hiff]
    rw [hsum 0, hsum 1]
    exact (ψ q).conservation ⟨v, rfl⟩
  · intro e
    dsimp [φ]
    exact (ψ (Quotient.mk P (H.endAt e 0))).nowhereZero _

/-- Jaeger--Kilpatrick's eight-flow theorem, stated directly for the elementary abelian
group `Gamma = (ZMod 2)^3`. -/
theorem jaegerKilpatrickEightFlow (hb : H.Bridgeless) :
    Nonempty (H.NowhereZeroFlow Gamma) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
      letI := hV
      letI : IsEmpty E := ⟨fun e => isEmptyElim (H.endAt e 0)⟩
      refine ⟨⟨fun e => isEmptyElim e, ?_, ?_⟩⟩
      · intro v
        exact isEmptyElim v
      · intro e
        exact isEmptyElim e
  | inr hV =>
      letI := hV
      exact H.jaegerKilpatrickEightFlow_of_nonempty hb

end FiniteGraph

end CycleDoubleCover
