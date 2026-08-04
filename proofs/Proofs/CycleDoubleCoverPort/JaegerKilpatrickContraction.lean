import Proofs.CycleDoubleCoverPort.GeneralGraph
import Mathlib.Algebra.CharP.Two

/-
# Cycle Double Cover port, step 6: edge contraction and two-cut flow lifting

Slice of the port of the openai/cdc-lean development of the Cycle Double Cover
theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery. It
corresponds to the contraction half of upstream `CDCLean/JaegerKilpatrick.lean`
(lines 399-793), plus one lemma vendored from upstream `CDCLean/FlowCount.lean`
(line 366); see #37507 for the porting order and the slices this one builds on.

## Provenance, licensing and attribution

Ported from `openai/cdc-lean`, `CDCLean/JaegerKilpatrick.lean` (lines 399-793),
plus `sum_conservation_eq_cut` and its private helper `sum_endpoint_indicator`
from `CDCLean/FlowCount.lean` (lines 359-381), vendored with adaptation per the
operator decision recorded on #37507 (comment of 2026-08-03). Part of epic
#37507.

`openai/cdc-lean` carries **no license file**, so default copyright applies; the
operator's decision on #37507 is an explicit *risk acceptance*, not a license.
Unlike the earlier slices of this port, which were independent re-derivations,
this file follows upstream's definitions, statements and proof scripts closely,
adapted only where this repository's Mathlib pin required it. Attribution: the
mathematical content and the proof scripts originate with `openai/cdc-lean`.

Upstream's toolchain pin (Lean `v4.31.0`) now matches this repository's, so the
adaptation surface is small. It consists of:

* namespace: upstream `CDCLean.FiniteGraph` becomes `CycleDoubleCover.FiniteGraph`,
  with `FiniteGraph`, `Crosses`, `cut`, `Bridgeless` and `F₂` taken from
  `Proofs/CycleDoubleCover.lean` and `Gamma`, `NowhereZeroFlow`, `IsFlow` from
  `Proofs/CycleDoubleCoverPort/GeneralGraph.lean` (step 1);
* the vendored `sum_conservation_eq_cut`: the merged
  `Proofs/CycleDoubleCoverPort/FlowCount.lean` (step 5b) is an independent
  re-derivation that routes the same computation through its own `divergence` /
  `endSum` primitives and does not export a lemma of this shape, so upstream's
  version is vendored here rather than imported. It is self-contained — only
  `Finset` lemmas and `endAt` — and this file therefore imports step 1 only.

## Mathematical content

The Jaeger–Kilpatrick eight-flow argument reduces a graph that is *not*
three-edge-connected to a smaller one by contracting an edge of a small cut.
This file supplies the contraction machinery and the flow-lifting step across a
two-edge cut.

* **Contraction.** `contractEdgeSetoid e` identifies the two ends of `e`;
  transitivity is where looplessness is used, since the relation is only an
  equivalence because `endAt e 0 ≠ endAt e 1`. `SurvivesContraction e f` says
  that `f` does not become a loop, and `contractEdge e` is the quotient graph on
  the surviving edge objects. Discarding the new loops is what keeps the result
  a `FiniteGraph`, whose `loopless` field forbids them.
* **Cuts are preserved.** `contractionPullback` sends a vertex set of the
  contracted graph back to the original vertices, and `mem_contractEdge_cut_iff`
  identifies the two cuts. Since a non-surviving edge can never cross a
  pullback, cuts of the contraction are exactly the cuts of `H` that avoid the
  contracted class — whence `contractEdge_bridgeless`.
* **Lifting a flow across a two-cut.** `nowhereZeroGammaFlow_of_contractEdge_of_twoCut`
  takes a nowhere-zero `Gamma`-flow on `H.contractEdge e₁`, where `{e₁, e₂}` is a
  two-edge cut, and lifts it to `H`. Every surviving edge keeps its value; the
  discarded edges all receive the common value `a`, namely the value of `e₂` when
  `e₂` survives and the fixed nonzero constant `gammaUnit` when it does not.
  Conservation is immediate away from the two ends of `e₁`
  (`sum_lift_off_contract_endpoints`), and at those two vertices it is forced by
  summing conservation over the shore `S` and over all of `V`: characteristic two
  makes the two cut edges cancel (`gamma_add_self_eq_zero`), so both defects
  vanish. This is where the vendored `sum_conservation_eq_cut` is used, twice.

Characteristic two is what makes the signed conservation law orientation-free:
`gamma_neg_eq_self` turns the signed boundary sum over a vertex set into the
plain sum over its cut (`sum_cut_term_gamma_eq_sum_cut`).

## Deltas from upstream

| upstream | here |
| --- | --- |
| namespace `CDCLean.FiniteGraph` | `CycleDoubleCover.FiniteGraph`; base definitions come from `Proofs/CycleDoubleCover.lean` and step 1 |
| `sum_conservation_eq_cut` imported from `CDCLean/FlowCount.lean` | vendored verbatim into this file (with its private helper), since the merged step-5b `FlowCount.lean` is an independent re-derivation that does not export it |
| file also contains the three-edge-connected construction and the induction (lines 1-398, 795-1223) | out of scope for this slice; they are separate slices of #37507 |

Everything else — the setoid, the three `noncomputable` instances, the
`Fintype.ofFinite` layer inside `contractEdge`, and all 19 statements and proof
scripts — is upstream's, unchanged.

`gamma_neg_eq_self` and `gamma_add_self_eq_zero` restate facts that already exist
in this port under different names (`CycleDoubleCover.neg_gamma` in
`CubicBridge.lean`, `CycleDoubleCover.CubicGraph.gamma_add_self` in `Basic.lean`).
They are kept as upstream wrote them, in the `FiniteGraph` namespace, so that the
remaining Jaeger–Kilpatrick slices port without rewriting; the fully qualified
names do not clash.

## Deliberate omissions

`eq_contractEdge_or_eq_second_of_not_survives_of_twoCut` is unused inside this
segment (upstream uses it in the induction at lines 795-1223); it is ported here
for fidelity with the upstream file layout. This file does not discharge
`CycleDoubleCover.cycleDoubleCover_of_bridgeless`, and it does not prove
Seymour's six-flow theorem.
-/

namespace CycleDoubleCover

namespace FiniteGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (H : FiniteGraph V E)

/-! ### Vendored from upstream `CDCLean/FlowCount.lean`

Summing the conservation defect over a vertex set: all interior terms cancel and
only the signed crossing-edge contributions survive. Vendored (with its private
helper) from upstream `CDCLean/FlowCount.lean` lines 359-381, because the merged
step-5b `FlowCount.lean` in this port is an independent re-derivation that keeps
the same computation inside its `divergence` API and exports no lemma of this
shape. -/

omit [Fintype V] in
private theorem sum_endpoint_indicator
    {A : Type*} [AddCommGroup A] (U : Finset V) (x : V) (a : A) :
    (∑ v ∈ U, if x = v then a else 0) = if x ∈ U then a else 0 := by
  simp

omit [DecidableEq E] in
/-- Summing conservation over a vertex set leaves only the signed crossing-edge terms. -/
theorem sum_conservation_eq_cut
    {A : Type*} [AddCommGroup A] (f : E → A) (U : Finset V) :
    (∑ v ∈ U,
      ((∑ k : E, if H.endAt k 0 = v then f k else 0) -
       (∑ k : E, if H.endAt k 1 = v then f k else 0))) =
      ∑ k : E,
        ((if H.endAt k 0 ∈ U then f k else 0) -
         (if H.endAt k 1 ∈ U then f k else 0)) := by
  have hside (j : Fin 2) :
      (∑ v ∈ U, ∑ k : E, if H.endAt k j = v then f k else 0) =
        ∑ k : E, if H.endAt k j ∈ U then f k else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact sum_endpoint_indicator U (H.endAt k j) (f k)
  rw [Finset.sum_sub_distrib, hside 0, hside 1, ← Finset.sum_sub_distrib]

/-! ### Edge contraction

Ported from upstream `CDCLean/JaegerKilpatrick.lean`, lines 399-793. -/

/-- The equivalence relation obtained by contracting one edge object. -/
def contractEdgeSetoid (e : E) : Setoid V where
  r u v := u = v ∨
    (u = H.endAt e 0 ∧ v = H.endAt e 1) ∨
      (u = H.endAt e 1 ∧ v = H.endAt e 0)
  iseqv := by
    constructor
    · intro u
      exact Or.inl rfl
    · intro u v huv
      rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · intro u v w huv hvw
      rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hvw
      · rcases hvw with rfl | ⟨h, _⟩ | ⟨_, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact (H.loopless e h.symm).elim
        · exact Or.inl rfl
      · rcases hvw with rfl | ⟨_, rfl⟩ | ⟨h, _⟩
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl rfl
        · exact (H.loopless e h).elim

/-- An original edge survives contraction when its two ends do not become equal. -/
def SurvivesContraction (e f : E) : Prop :=
  ¬ (H.contractEdgeSetoid e).r (H.endAt f 0) (H.endAt f 1)

noncomputable instance contractEdgeQuotientDecidableEq (e : E) :
    DecidableEq (Quotient (H.contractEdgeSetoid e)) := Classical.decEq _

noncomputable instance survivesContractionDecidablePred (e : E) :
    DecidablePred (H.SurvivesContraction e) := Classical.decPred _

noncomputable instance survivesContractionFintype (e : E) :
    Fintype {f : E // H.SurvivesContraction e f} :=
  Fintype.ofFinite _

/-- Contract one edge and discard precisely the edge objects that become loops. -/
noncomputable def contractEdge (e : E) :
    FiniteGraph (Quotient (H.contractEdgeSetoid e))
      {f : E // H.SurvivesContraction e f} := by
  classical
  letI : Fintype (Quotient (H.contractEdgeSetoid e)) := Fintype.ofFinite _
  letI : Fintype {f : E // H.SurvivesContraction e f} := Fintype.ofFinite _
  exact
    { endAt := fun f i => Quotient.mk _ (H.endAt f.1 i)
      loopless := by
        intro f h
        exact f.2 (Quotient.eq'.mp h) }

omit [DecidableEq V] [DecidableEq E] in
theorem not_survives_contracted_edge (e : E) :
    ¬ H.SurvivesContraction e e := by
  intro h
  apply h
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Pull a vertex set of a contracted graph back to the original vertices. -/
noncomputable def contractionPullback (e : E)
    (A : Finset (Quotient (H.contractEdgeSetoid e))) : Finset V := by
  classical
  exact Finset.univ.filter fun v => Quotient.mk (H.contractEdgeSetoid e) v ∈ A

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem mem_contractionPullback {e : E}
    {A : Finset (Quotient (H.contractEdgeSetoid e))} {v : V} :
    v ∈ H.contractionPullback e A ↔
      Quotient.mk (H.contractEdgeSetoid e) v ∈ A := by
  classical
  simp [contractionPullback]

omit [DecidableEq V] [DecidableEq E] in
theorem not_crosses_contractionPullback_of_not_survives {e f : E}
    (A : Finset (Quotient (H.contractEdgeSetoid e)))
    (hf : ¬ H.SurvivesContraction e f) :
    ¬ H.Crosses (H.contractionPullback e A) f := by
  classical
  have hrel : (H.contractEdgeSetoid e).r (H.endAt f 0) (H.endAt f 1) :=
    not_not.mp hf
  have hq : Quotient.mk (H.contractEdgeSetoid e) (H.endAt f 0) =
      Quotient.mk (H.contractEdgeSetoid e) (H.endAt f 1) := Quotient.sound hrel
  intro hcross
  unfold Crosses at hcross
  apply hcross
  simp [hq]

omit [DecidableEq V] [DecidableEq E] in
theorem mem_contractEdge_cut_iff {e : E}
    (A : Finset (Quotient (H.contractEdgeSetoid e)))
    (f : {f : E // H.SurvivesContraction e f}) :
    f ∈ (H.contractEdge e).cut A ↔
      f.1 ∈ H.cut (H.contractionPullback e A) := by
  classical
  simp [cut, Crosses, contractEdge]

omit [DecidableEq V] [DecidableEq E] in
/-- Contracting an edge and discarding the resulting loops preserves bridgelessness. -/
theorem contractEdge_bridgeless (e : E) (hb : H.Bridgeless) :
    (H.contractEdge e).Bridgeless := by
  classical
  intro A hcard
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
  let S := H.contractionPullback e A
  have hcut : H.cut S = {f.1} := by
    ext g
    constructor
    · intro hg
      have hcross : H.Crosses S g := (Finset.mem_filter.mp hg).2
      have hsurv : H.SurvivesContraction e g := by
        intro hnot
        exact (H.not_crosses_contractionPullback_of_not_survives A
          (fun hs => hs hnot)) hcross
      let g' : {g : E // H.SurvivesContraction e g} := ⟨g, hsurv⟩
      have hg' : g' ∈ (H.contractEdge e).cut A :=
        (H.mem_contractEdge_cut_iff A g').2 hg
      have hgf : g' = f := by simpa [hf] using hg'
      simpa using congrArg Subtype.val hgf
    · intro hg
      have hgf : g = f.1 := by simpa using hg
      subst g
      have hfmem : f ∈ (H.contractEdge e).cut A := by simp [hf]
      exact (H.mem_contractEdge_cut_iff A f).1 hfmem
  apply hb S
  rw [hcut]
  simp

omit [DecidableEq V] [DecidableEq E] in
theorem quotient_mk_contractEdge_eq_iff_of_ne_endpoints {e : E} {x v : V}
    (hv0 : v ≠ H.endAt e 0) (hv1 : v ≠ H.endAt e 1) :
    Quotient.mk (H.contractEdgeSetoid e) x =
        Quotient.mk (H.contractEdgeSetoid e) v ↔ x = v := by
  constructor
  · intro h
    rcases Quotient.eq'.mp h with h | ⟨_, hv⟩ | ⟨_, hv⟩
    · exact h
    · exact (hv1 hv).elim
    · exact (hv0 hv).elim
  · intro h
    subst x
    rfl

omit [DecidableEq V] in
/-- For a two-edge cut, the only original edges discarded when the first cut edge is
contracted are the two cut edges themselves. -/
theorem eq_contractEdge_or_eq_second_of_not_survives_of_twoCut
    (S : Finset V) {e₁ e₂ f : E}
    (hcut : H.cut S = {e₁, e₂}) (he₁ : e₁ ∈ H.cut S)
    (hf : ¬ H.SurvivesContraction e₁ f) : f = e₁ ∨ f = e₂ := by
  classical
  have hrel : (H.contractEdgeSetoid e₁).r (H.endAt f 0) (H.endAt f 1) :=
    not_not.mp hf
  rcases hrel with hloop | hends | hends
  · exact (H.loopless f hloop).elim
  · have hcross₁ : H.Crosses S e₁ := (Finset.mem_filter.mp he₁).2
    have hcross : H.Crosses S f := by
      unfold Crosses at hcross₁ ⊢
      simpa [hends.1, hends.2] using hcross₁
    have hfcut : f ∈ H.cut S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross⟩
    rw [hcut] at hfcut
    simpa using hfcut
  · have hcross₁ : H.Crosses S e₁ := (Finset.mem_filter.mp he₁).2
    have hcross : H.Crosses S f := by
      unfold Crosses at hcross₁ ⊢
      simpa [hends.1, hends.2] using hcross₁.symm
    have hfcut : f ∈ H.cut S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross⟩
    rw [hcut] at hfcut
    simpa using hfcut

omit [DecidableEq V] [DecidableEq E] in
theorem endAt_ne_of_not_survives_of_ne_contract_endpoints {e f : E} {v : V}
    (hf : ¬ H.SurvivesContraction e f)
    (hv0 : v ≠ H.endAt e 0) (hv1 : v ≠ H.endAt e 1) (j : Fin 2) :
    H.endAt f j ≠ v := by
  have hrel : (H.contractEdgeSetoid e).r (H.endAt f 0) (H.endAt f 1) :=
    not_not.mp hf
  rcases hrel with hloop | hends | hends
  · exact (H.loopless f hloop).elim
  · fin_cases j
    · simpa [hends.1] using hv0.symm
    · simpa [hends.2] using hv1.symm
  · fin_cases j
    · simpa [hends.1] using hv1.symm
    · simpa [hends.2] using hv0.symm

/-- A fixed nonzero element of `Gamma`, used only when both edges of a two-cut become
parallel loops after contraction. -/
def gammaUnit : Gamma := Pi.single 0 1

theorem gammaUnit_ne_zero : gammaUnit ≠ (0 : Gamma) := by
  intro h
  have h0 := congrFun h 0
  simp [gammaUnit] at h0

theorem gamma_neg_eq_self (x : Gamma) : -x = x := by
  funext i
  exact ZMod.neg_eq_self_mod_two _

theorem gamma_add_self_eq_zero (x : Gamma) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

/-- In characteristic two the signed boundary sum over a vertex set is just the sum of
the values on its cut edges. -/
theorem sum_cut_term_gamma_eq_sum_cut (φ : E → Gamma) (S : Finset V) :
    (∑ e : E,
      ((if H.endAt e 0 ∈ S then φ e else 0) -
        (if H.endAt e 1 ∈ S then φ e else 0))) =
      ∑ e ∈ H.cut S, φ e := by
  classical
  calc
    (∑ e : E,
      ((if H.endAt e 0 ∈ S then φ e else 0) -
        (if H.endAt e 1 ∈ S then φ e else 0))) =
        ∑ e : E, if e ∈ H.cut S then φ e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h0 : H.endAt e 0 ∈ S <;> by_cases h1 : H.endAt e 1 ∈ S
      · have hnot : e ∉ H.cut S := by simp [cut, Crosses, h0, h1]
        simp [h0, h1, hnot]
      · have hmem : e ∈ H.cut S := by simp [cut, Crosses, h0, h1]
        simp [h0, h1, hmem]
      · have hmem : e ∈ H.cut S := by simp [cut, Crosses, h0, h1]
        simp [h0, h1, hmem, gamma_neg_eq_self]
      · have hnot : e ∉ H.cut S := by simp [cut, Crosses, h0, h1]
        simp [h0, h1, hnot]
    _ = ∑ e ∈ H.cut S, φ e := by
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp

omit [DecidableEq E] in
theorem sum_lift_off_contract_endpoints {e : E}
    (ψ : (H.contractEdge e).NowhereZeroFlow Gamma) (a : Gamma)
    {v : V} (hv0 : v ≠ H.endAt e 0) (hv1 : v ≠ H.endAt e 1)
    (j : Fin 2) :
    (∑ f : E, if H.endAt f j = v then
        (if hf : H.SurvivesContraction e f then ψ.val ⟨f, hf⟩ else a) else 0) =
      ∑ f : {f : E // H.SurvivesContraction e f},
        if (H.contractEdge e).endAt f j = Quotient.mk _ v then ψ.val f else 0 := by
  classical
  let g : E → Gamma := fun f =>
    if hf : H.SurvivesContraction e f then
      if H.endAt f j = v then ψ.val ⟨f, hf⟩ else 0
    else 0
  calc
    (∑ f : E, if H.endAt f j = v then
        (if hf : H.SurvivesContraction e f then ψ.val ⟨f, hf⟩ else a) else 0) =
        ∑ f : E, g f := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : H.SurvivesContraction e f
      · simp [g, hf]
      · have hfv : H.endAt f j ≠ v :=
          H.endAt_ne_of_not_survives_of_ne_contract_endpoints hf hv0 hv1 j
        simp [g, hf, hfv]
    _ = ∑ f : {f : E // H.SurvivesContraction e f}, g f.1 := by
      calc
        (∑ f : E, g f) =
            ∑ f ∈ (Finset.univ.filter fun f => H.SurvivesContraction e f), g f := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro f _
          by_cases hf : H.SurvivesContraction e f <;> simp [g, hf]
        _ = ∑ f : {f : E // H.SurvivesContraction e f}, g f.1 := by
          symm
          simpa using (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset E))
            (p := fun f => H.SurvivesContraction e f) g)
    _ = ∑ f : {f : E // H.SurvivesContraction e f},
        if (H.contractEdge e).endAt f j = Quotient.mk _ v then ψ.val f else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      have hq : (H.contractEdge e).endAt f j = Quotient.mk _ v ↔
          H.endAt f.1 j = v := by
        change Quotient.mk (H.contractEdgeSetoid e) (H.endAt f.1 j) =
            Quotient.mk (H.contractEdgeSetoid e) v ↔ _
        exact H.quotient_mk_contractEdge_eq_iff_of_ne_endpoints hv0 hv1
      simp [g, f.2, hq]

/-- A `Gamma`-flow on the contraction of one edge of a two-edge cut lifts across that
cut.  The contracted edge receives the value of the other cut edge; if the two cut
edges are parallel and both disappear, they receive the fixed value `gammaUnit`. -/
theorem nowhereZeroGammaFlow_of_contractEdge_of_twoCut
    (S : Finset V) {e₁ e₂ : E}
    (hcut : H.cut S = {e₁, e₂})
    (he₁ : e₁ ∈ H.cut S) (he₁₂ : e₁ ≠ e₂)
    (hψ : Nonempty ((H.contractEdge e₁).NowhereZeroFlow Gamma)) :
    Nonempty (H.NowhereZeroFlow Gamma) := by
  classical
  obtain ⟨ψ⟩ := hψ
  let a : Gamma :=
    if he₂s : H.SurvivesContraction e₁ e₂ then ψ.val ⟨e₂, he₂s⟩ else gammaUnit
  have ha : a ≠ 0 := by
    dsimp [a]
    split
    · exact ψ.nowhereZero _
    · exact gammaUnit_ne_zero
  let φ : E → Gamma := fun e =>
    if he : H.SurvivesContraction e₁ e then ψ.val ⟨e, he⟩ else a
  have hφe₁ : φ e₁ = a := by
    simp [φ, H.not_survives_contracted_edge]
  have hφe₂ : φ e₂ = a := by
    by_cases he₂s : H.SurvivesContraction e₁ e₂
    · simp [φ, a, he₂s]
    · simp [φ, a, he₂s]
  let d : V → Gamma := fun v =>
    (∑ e : E, if H.endAt e 0 = v then φ e else 0) -
      ∑ e : E, if H.endAt e 1 = v then φ e else 0
  have hoff (v : V) (hv0 : v ≠ H.endAt e₁ 0) (hv1 : v ≠ H.endAt e₁ 1) :
      d v = 0 := by
    dsimp [d]
    rw [H.sum_lift_off_contract_endpoints ψ a hv0 hv1 0,
      H.sum_lift_off_contract_endpoints ψ a hv0 hv1 1]
    exact ψ.conservation (Quotient.mk (H.contractEdgeSetoid e₁) v)
  have hsumS : ∑ v ∈ S, d v = 0 := by
    have h := H.sum_conservation_eq_cut φ S
    change (∑ v ∈ S, d v) =
      (∑ e : E,
        ((if H.endAt e 0 ∈ S then φ e else 0) -
          (if H.endAt e 1 ∈ S then φ e else 0))) at h
    rw [H.sum_cut_term_gamma_eq_sum_cut φ S, hcut] at h
    simpa [he₁₂, hφe₁, hφe₂, gamma_add_self_eq_zero] using h
  have hsumUniv : ∑ v : V, d v = 0 := by
    have h := H.sum_conservation_eq_cut φ (Finset.univ : Finset V)
    change (∑ v ∈ (Finset.univ : Finset V), d v) =
      (∑ e : E,
        ((if H.endAt e 0 ∈ (Finset.univ : Finset V) then φ e else 0) -
          (if H.endAt e 1 ∈ (Finset.univ : Finset V) then φ e else 0))) at h
    rw [H.sum_cut_term_gamma_eq_sum_cut φ (Finset.univ : Finset V)] at h
    simpa [cut, Crosses] using h
  have hcross₁ : H.Crosses S e₁ := (Finset.mem_filter.mp he₁).2
  have hendsZero : d (H.endAt e₁ 0) = 0 ∧ d (H.endAt e₁ 1) = 0 := by
    by_cases h0 : H.endAt e₁ 0 ∈ S
    · have h1 : H.endAt e₁ 1 ∉ S := by
        intro h1
        exact hcross₁ (propext ⟨fun _ => h1, fun _ => h0⟩)
      have hd0 : d (H.endAt e₁ 0) = 0 := by
        have hsingle : ∑ v ∈ S, d v = d (H.endAt e₁ 0) := by
          apply Finset.sum_eq_single (H.endAt e₁ 0)
          · intro v hv hvne
            exact hoff v hvne (fun h => h1 (h ▸ hv))
          · intro hnot
            exact (hnot h0).elim
        rw [← hsingle]
        exact hsumS
      have hd1 : d (H.endAt e₁ 1) = 0 := by
        have hsingle : ∑ v : V, d v = d (H.endAt e₁ 1) := by
          apply Fintype.sum_eq_single
          intro v hvne
          by_cases hv0 : v = H.endAt e₁ 0
          · simpa [hv0] using hd0
          · exact hoff v hv0 hvne
        rw [← hsingle]
        exact hsumUniv
      exact ⟨hd0, hd1⟩
    · have h1 : H.endAt e₁ 1 ∈ S := by
        by_contra h1
        exact hcross₁ (propext ⟨fun h => (h0 h).elim, fun h => (h1 h).elim⟩)
      have hd1 : d (H.endAt e₁ 1) = 0 := by
        have hsingle : ∑ v ∈ S, d v = d (H.endAt e₁ 1) := by
          apply Finset.sum_eq_single (H.endAt e₁ 1)
          · intro v hv hvne
            exact hoff v (fun h => h0 (h ▸ hv)) hvne
          · intro hnot
            exact (hnot h1).elim
        rw [← hsingle]
        exact hsumS
      have hd0 : d (H.endAt e₁ 0) = 0 := by
        have hsingle : ∑ v : V, d v = d (H.endAt e₁ 0) := by
          apply Fintype.sum_eq_single
          intro v hvne
          by_cases hv1 : v = H.endAt e₁ 1
          · simpa [hv1] using hd1
          · exact hoff v hvne hv1
        rw [← hsingle]
        exact hsumUniv
      exact ⟨hd0, hd1⟩
  refine ⟨⟨φ, ?_, ?_⟩⟩
  · intro v
    change d v = 0
    by_cases hv0 : v = H.endAt e₁ 0
    · simpa [hv0] using hendsZero.1
    · by_cases hv1 : v = H.endAt e₁ 1
      · simpa [hv1] using hendsZero.2
      · exact hoff v hv0 hv1
  · intro e
    dsimp [φ]
    split
    · exact ψ.nowhereZero _
    · exact ha

end FiniteGraph

end CycleDoubleCover
