import Proofs.CycleDoubleCoverPort.SixFlow
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-
# Cycle Double Cover port, step 5b: Tutte's group-order invariance for flow counts

Slice of the port of the openai/cdc-lean development of the Cycle Double Cover
theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery. It
corresponds to upstream `CDCLean/FlowCount.lean`; see #37507 for the porting
order, #43625 (step 1), #43626 (step 2), #43630 (step 3), #43629 (step 4 part 1)
and #43627 (step 5a, `SixFlow.lean`) for the slices this one builds on.

## Provenance, licensing and attribution

`openai/cdc-lean` carries **no license file**, so default copyright applies.
The operator has recorded an explicit risk acceptance on #37507 (comment of
2026-08-03) permitting vendoring of upstream sources with attribution. This
file nevertheless follows the same posture as the five sibling slices already
merged: it is an *independent re-derivation*. Upstream was consulted for the
mathematical content only — the shapes of the definitions and the statements of
the results — and every proof script here was written from scratch against this
repository's Mathlib pin. Attribution: the definitions and theorem statements
originate with `openai/cdc-lean` (`CDCLean/FlowCount.lean`).

## Mathematical content

Tutte's group-order invariance theorem says that, on a fixed finite incidence
structure, the *number* of nowhere-zero flows depends only on the cardinality of
the finite abelian coefficient group — not on the group itself. Step 5a produced
a nowhere-zero `ZMod 8`-flow from Seymour's integral 6-flow; the labelling stage
needs a nowhere-zero `Gamma = F₂³`-flow. `ZMod 8` and `Gamma` are the two abelian
groups of order eight, and they are *not* isomorphic, so this transfer is a
genuine counting theorem rather than a reindexing.

The argument runs in two independent halves.

* **Inclusion–exclusion.** Counting nowhere-zero flows is counting the flows that
  avoid every "bad" event `f e = 0`. Inclusion–exclusion rewrites that count as
  an alternating sum, over edge subsets `S`, of the number of flows that *vanish*
  on all of `S` (`card_nowhereZeroFlows_eq_sum_zeroOn`). So it suffices to show
  that each `ZeroOnFlows A S` count depends only on `Fintype.card A`.
* **An edge-addition recurrence.** Start from `S = Finset.univ`, where the only
  flow is the zero flow, and remove forbidden edges one at a time. Removing `e`
  from `S` does one of two things:
  - if `e` carries a *cycle correction* — a unit integral circulation through `e`
    supported off `S.erase e` — then the flow count is multiplied by exactly
    `Fintype.card A`, because the value on `e` becomes a free parameter
    (`allowEdgeEquivOf`);
  - if `e` is *forced to zero* — every flow on the larger edge set still vanishes
    on `e` — then the count is unchanged (`allowForcedEdgeEquiv`).
  Both alternatives are visibly group-order-only, so induction along a chain of
  such steps (`FlowReduction`) gives the invariant.

The graph theory is entirely concentrated in the dichotomy "cycle correction or
separating cut" (`IntegralPathCutDichotomy`), which this file keeps as an
interface and `PathCut.lean` discharges for every finite graph.

## Deltas from upstream

| upstream | here |
| --- | --- |
| `divergence` restated ad hoc; `isFlow_add`, `isFlow_int_smul`, `divergence_add`, `divergence_neg` each re-prove the same `if`-splitting sum identity | one primitive `endSum`, identified with a sum over the incidence fibre (`endSum_eq_sum_filter`); additivity, negation and `ℤ`-scaling then fall out of `Finset.sum_add_distrib` / `sum_neg_distrib` / `sum_smul`, and all six flow/divergence lemmas are one-liners on top |
| `IsFlow` and `divergence` related only implicitly | `isFlow_iff_divergence` records `G.IsFlow f ↔ ∀ v, G.divergence f v = 0` |
| `Pi.single k 1` for the one-edge chain | explicit `unitChain`, avoiding `Pi.single` API |
| `GoodFlows`, `BadOnFlows` and four equivalences (`nowhereZeroFlowsEquivGood`, `zeroOnFlowsEquivBad`, plus two more built inside the inclusion–exclusion proof) | dropped; two equivalences (`zeroOnFlowsEquivCoe`, `nowhereZeroFlowsEquivCoe`) go straight to the `Finset` coercion that inclusion–exclusion wants |
| `mem_finset_inf` by `Finset.cons_induction` | `mem_finsetInf` from the lattice adjunction (`Finset.le_inf` / `Finset.inf_le`) |
| `allowEdgeEquiv` opens the existential with `Classical.choose` inside the equivalence | choice-free core `allowEdgeEquivOf` taking the circulation as data, with a one-line `Exists.choose` wrapper |
| `zeroOnFlowsCongr` rewrites the conservation law by hand on both sides | reuses `IsFlow.map` from step 5a |
| `zeroOnFlowsUnivEquiv` inlines `by simp [IsFlow]` | reuses `zero_isFlow` from step 1 |
| `reductions_of_step_classification` inducts on `Finset.univ \ T` | inducts on `Tᶜ`, so `Finset.compl_insert` supplies the `erase` step directly |
| `HasIntegerPath.symm` / `.trans` finish by a four-way `by_cases` on the endpoint indicators | finish by `ring` |
| `Crosses` unfolded inline at each use | named `not_crosses_iff` / `crosses_iff` bridges to the readable `↔` form |

## Deliberate omissions

This file does **not** discharge `CycleDoubleCover.cycleDoubleCover_of_bridgeless`,
and it does not prove Seymour's six-flow theorem: `SeymourSixFlowStatement`
(step 1) remains an explicit hypothesis wherever it is needed. The path/cut
dichotomy is an interface here and is discharged in `PathCut.lean` (same slice).
Upstream's `JaegerKilpatrick.lean`, `CubicTheorem.lean` and `Main.lean` are later
steps.
-/

namespace CycleDoubleCover

namespace FiniteGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-! ### End sums and divergence

Everything algebraic about flows in this file factors through a single
primitive: the total of an edge labelling over the edges whose `j`-th end sits
at a given vertex. -/

/-- The `j`-th **end sum** of an edge labelling at a vertex `v`: the total of `f`
over those edges whose end number `j` is `v`. The flow condition of step 1 is the
statement that the two end sums agree at every vertex. -/
def endSum {A : Type*} [AddCommMonoid A] (j : Fin 2) (f : E → A) (v : V) : A :=
  ∑ k : E, if G.endAt k j = v then f k else 0

omit [DecidableEq E] in
/-- An end sum is an ordinary `Finset` sum over the fibre of the incidence map.
This is the only place the `if`-form is unpacked; all algebraic properties of end
sums below are read off from the standard `Finset.sum` lemmas through it. -/
theorem endSum_eq_sum_filter {A : Type*} [AddCommMonoid A] (j : Fin 2) (f : E → A) (v : V) :
    G.endSum j f v = ∑ k ∈ Finset.univ.filter fun k => G.endAt k j = v, f k :=
  (Finset.sum_filter _ _).symm

omit [DecidableEq E] in
theorem endSum_add {A : Type*} [AddCommMonoid A] (j : Fin 2) (f g : E → A) (v : V) :
    G.endSum j (f + g) v = G.endSum j f v + G.endSum j g v := by
  simp only [endSum_eq_sum_filter, Pi.add_apply, Finset.sum_add_distrib]

omit [DecidableEq E] in
theorem endSum_neg {A : Type*} [AddCommGroup A] (j : Fin 2) (f : E → A) (v : V) :
    G.endSum j (-f) v = -G.endSum j f v := by
  simp only [endSum_eq_sum_filter, Pi.neg_apply, Finset.sum_neg_distrib]

omit [DecidableEq E] in
/-- Evaluating an integral chain at a fixed group element commutes with taking end
sums. -/
theorem endSum_zsmul {A : Type*} [AddCommGroup A] (j : Fin 2) (c : E → ℤ) (x : A) (v : V) :
    G.endSum j (fun k => c k • x) v = G.endSum j c v • x := by
  simp only [endSum_eq_sum_filter, Finset.sum_smul]

/-- Signed boundary of an edge-valued chain at a vertex: the difference of the two
end sums. -/
def divergence {A : Type*} [AddCommGroup A] (f : E → A) (v : V) : A :=
  G.endSum 0 f v - G.endSum 1 f v

omit [DecidableEq E] in
/-- The flow condition of step 1 is exactly the vanishing of the divergence. Both
sides are the same proposition; naming the identification keeps the rest of the
file readable. -/
theorem isFlow_iff_divergence {A : Type*} [AddCommGroup A] (f : E → A) :
    G.IsFlow f ↔ ∀ v : V, G.divergence f v = 0 := Iff.rfl

omit [DecidableEq E] in
theorem divergence_add {A : Type*} [AddCommGroup A] (f g : E → A) (v : V) :
    G.divergence (f + g) v = G.divergence f v + G.divergence g v := by
  simp only [divergence, endSum_add]
  abel

omit [DecidableEq E] in
theorem divergence_neg {A : Type*} [AddCommGroup A] (f : E → A) (v : V) :
    G.divergence (-f) v = -G.divergence f v := by
  simp only [divergence, endSum_neg]
  abel

omit [DecidableEq E] in
theorem divergence_sub {A : Type*} [AddCommGroup A] (f g : E → A) (v : V) :
    G.divergence (f - g) v = G.divergence f v - G.divergence g v := by
  simp only [sub_eq_add_neg, divergence_add, divergence_neg]

omit [DecidableEq E] in
theorem divergence_zsmul {A : Type*} [AddCommGroup A] (c : E → ℤ) (x : A) (v : V) :
    G.divergence (fun k => c k • x) v = G.divergence c v • x := by
  simp only [divergence, endSum_zsmul, sub_smul]

omit [DecidableEq E] in
/-- Pointwise addition preserves the circulation equations. -/
theorem isFlow_add {A : Type*} [AddCommGroup A] {f g : E → A}
    (hf : G.IsFlow f) (hg : G.IsFlow g) : G.IsFlow (f + g) := by
  intro v
  have hf' : G.divergence f v = 0 := hf v
  have hg' : G.divergence g v = 0 := hg v
  show G.divergence (f + g) v = 0
  rw [G.divergence_add, hf', hg', add_zero]

omit [DecidableEq E] in
theorem isFlow_neg {A : Type*} [AddCommGroup A] {f : E → A} (hf : G.IsFlow f) :
    G.IsFlow (-f) := by
  intro v
  have hf' : G.divergence f v = 0 := hf v
  show G.divergence (-f) v = 0
  rw [G.divergence_neg, hf', neg_zero]

omit [DecidableEq E] in
theorem isFlow_sub {A : Type*} [AddCommGroup A] {f g : E → A}
    (hf : G.IsFlow f) (hg : G.IsFlow g) : G.IsFlow (f - g) := by
  simpa only [sub_eq_add_neg] using G.isFlow_add hf (G.isFlow_neg hg)

omit [DecidableEq E] in
/-- An integer circulation can be evaluated at any element of any additive
commutative group, and the result is again a circulation. -/
theorem isFlow_int_smul {A : Type*} [AddCommGroup A] {c : E → ℤ}
    (hc : G.IsFlow c) (x : A) : G.IsFlow fun k => c k • x := by
  intro v
  have hc' : G.divergence c v = 0 := hc v
  show G.divergence (fun k => c k • x) v = 0
  rw [G.divergence_zsmul, hc', zero_smul]

/-! ### The finite types of flows -/

/-- The finite type of nowhere-zero `A`-flows on `G`. -/
def NowhereZeroFlows (A : Type*) [AddCommGroup A] :=
  {f : E → A // G.IsFlow f ∧ IsNowhereZero f}

/-- All `A`-valued flows, zero edge values allowed. This is the ambient finite
universe in which the inclusion–exclusion argument takes place. -/
def Flows (A : Type*) [AddCommGroup A] := {f : E → A // G.IsFlow f}

/-- Flows constrained to vanish on a prescribed set of edges. These are the
objects the edge-addition recurrence counts. -/
def ZeroOnFlows (A : Type*) [AddCommGroup A] (S : Finset E) :=
  {f : E → A // G.IsFlow f ∧ ∀ e ∈ S, f e = 0}

noncomputable instance instFintypeNowhereZeroFlows (A : Type*) [AddCommGroup A] [Fintype A] :
    Fintype (G.NowhereZeroFlows A) := by
  classical
  exact Subtype.fintype _

noncomputable instance instFintypeFlows (A : Type*) [AddCommGroup A] [Fintype A] :
    Fintype (G.Flows A) := by
  classical
  exact Subtype.fintype _

noncomputable instance instFintypeZeroOnFlows (A : Type*) [AddCommGroup A] [Fintype A]
    (S : Finset E) : Fintype (G.ZeroOnFlows A S) := by
  classical
  exact Subtype.fintype _

/-- Base case of the recurrence: if every edge is forced to zero, the zero flow is
the only flow. -/
def zeroOnFlowsUnivEquiv (A : Type*) [AddCommGroup A] :
    G.ZeroOnFlows A (Finset.univ : Finset E) ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨fun _ => 0, G.zero_isFlow, fun _ _ => rfl⟩
  left_inv f := Subtype.ext (funext fun e => (f.2.2 e (Finset.mem_univ e)).symm)
  right_inv _ := rfl

@[simp]
theorem card_zeroOnFlows_univ (A : Type*) [AddCommGroup A] [Fintype A] :
    Fintype.card (G.ZeroOnFlows A (Finset.univ : Finset E)) = 1 := by
  simpa using Fintype.card_congr (G.zeroOnFlowsUnivEquiv A)

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- An additive hom carries a labelling vanishing on `S` to one vanishing on `S`. -/
theorem map_zero_on {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B)
    (S : Finset E) (f : E → A) (hf : ∀ k ∈ S, f k = 0) : ∀ k ∈ S, φ (f k) = 0 :=
  fun k hk => by rw [hf k hk, map_zero]

/-- Coefficient functoriality: an additive equivalence of coefficient groups
transports flows vanishing on `S`. Conservation transports by `IsFlow.map`
(step 5a), which needs only additivity. -/
def zeroOnFlowsCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A ≃+ B) (S : Finset E) : G.ZeroOnFlows A S ≃ G.ZeroOnFlows B S where
  toFun f :=
    ⟨fun k => φ (f.1 k), IsFlow.map G φ.toAddMonoidHom f.2.1,
      map_zero_on φ.toAddMonoidHom S f.1 f.2.2⟩
  invFun f :=
    ⟨fun k => φ.symm (f.1 k), IsFlow.map G φ.symm.toAddMonoidHom f.2.1,
      map_zero_on φ.symm.toAddMonoidHom S f.1 f.2.2⟩
  left_inv _ := Subtype.ext (funext fun _ => φ.symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ => φ.apply_symm_apply _)

theorem card_zeroOnFlows_eq_of_addEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (φ : A ≃+ B) (S : Finset E) :
    Fintype.card (G.ZeroOnFlows A S) = Fintype.card (G.ZeroOnFlows B S) :=
  Fintype.card_congr (G.zeroOnFlowsCongr φ S)

/-! ### Integral paths and cycle corrections -/

/-- The unit integral chain supported on the single edge `k`, oriented from end
`0` to end `1`. -/
def unitChain (k : E) : E → ℤ := fun l => if l = k then 1 else 0

omit [Fintype E] in
theorem unitChain_of_ne {k l : E} (h : l ≠ k) : unitChain k l = 0 := by
  simp [unitChain, h]

theorem endSum_unitChain (j : Fin 2) (k : E) (v : V) :
    G.endSum j (unitChain k) v = if G.endAt k j = v then 1 else 0 := by
  have h : ∀ l : E, l ≠ k → (if G.endAt l j = v then unitChain k l else 0) = 0 := by
    intro l hl
    simp [unitChain_of_ne hl]
  simp only [endSum]
  rw [Fintype.sum_eq_single k h]
  simp [unitChain]

theorem divergence_unitChain (k : E) (w : V) :
    G.divergence (unitChain k) w =
      (if G.endAt k 0 = w then 1 else 0) - (if G.endAt k 1 = w then 1 else 0) := by
  simp only [divergence, G.endSum_unitChain]

/-- An integral chain supported off the forbidden set `S` whose boundary is
`u - v`: the "allowed path" from `u` to `v`. -/
def HasIntegerPath (S : Finset E) (u v : V) : Prop :=
  ∃ c : E → ℤ, (∀ k ∈ S, c k = 0) ∧ ∀ w : V,
    G.divergence c w = (if u = w then 1 else 0) - (if v = w then 1 else 0)

omit [DecidableEq E] in
theorem hasIntegerPath_refl (S : Finset E) (u : V) : G.HasIntegerPath S u u :=
  ⟨fun _ => 0, fun _ _ => rfl, fun w => by simp [divergence, endSum]⟩

/-- Every edge outside the forbidden set is itself an allowed path between its
ends. -/
theorem hasIntegerPath_single (S : Finset E) (k : E) (hk : k ∉ S) :
    G.HasIntegerPath S (G.endAt k 0) (G.endAt k 1) :=
  ⟨unitChain k, fun l hl => unitChain_of_ne fun h => hk (h ▸ hl), G.divergence_unitChain k⟩

omit [DecidableEq E] in
theorem HasIntegerPath.symm {S : Finset E} {u v : V}
    (h : G.HasIntegerPath S u v) : G.HasIntegerPath S v u := by
  obtain ⟨c, hcS, hc⟩ := h
  refine ⟨-c, fun k hk => by simp [hcS k hk], fun w => ?_⟩
  rw [G.divergence_neg, hc w]
  ring

omit [DecidableEq E] in
theorem HasIntegerPath.trans {S : Finset E} {u v w : V}
    (h₁ : G.HasIntegerPath S u v) (h₂ : G.HasIntegerPath S v w) :
    G.HasIntegerPath S u w := by
  obtain ⟨c₁, h₁S, h₁d⟩ := h₁
  obtain ⟨c₂, h₂S, h₂d⟩ := h₂
  refine ⟨c₁ + c₂, fun k hk => by simp [h₁S k hk, h₂S k hk], fun x => ?_⟩
  rw [G.divergence_add, h₁d x, h₂d x]
  ring

/-- A unit integral circulation through `e` supported off `S.erase e`: the
certificate that allows the edge `e` in the recurrence. -/
def HasCycleCorrection (S : Finset E) (e : E) : Prop :=
  ∃ c : E → ℤ, G.IsFlow c ∧ c e = 1 ∧ ∀ k ∈ S.erase e, c k = 0

/-- An allowed path between the ends of `e` closes up with `e` itself into the
required unit circulation. -/
theorem hasCycleCorrection_of_integerPath
    (S : Finset E) (e : E) (he : e ∈ S)
    (hp : G.HasIntegerPath S (G.endAt e 0) (G.endAt e 1)) :
    G.HasCycleCorrection S e := by
  obtain ⟨d, hdS, hd⟩ := hp
  refine ⟨unitChain e - d, fun w => ?_, ?_, fun k hk => ?_⟩
  · show G.divergence (unitChain e - d) w = 0
    rw [G.divergence_sub, G.divergence_unitChain, hd w]
    exact sub_self _
  · have hde : d e = 0 := hdS e he
    simp [unitChain, hde]
  · have hke : k ≠ e := (Finset.mem_erase.mp hk).1
    have hdk : d k = 0 := hdS k (Finset.mem_of_mem_erase hk)
    simp [unitChain, hke, hdk]

/-! ### The edge-addition recurrence -/

omit [Fintype E] [DecidableEq V] in
/-- Adding a multiple of the correction chain keeps a flow vanishing on the
smaller forbidden set. Stated on raw edge labellings so that the equivalence
below needs no subtype bookkeeping. -/
theorem allowEdge_forward_zero {A : Type*} [AddCommGroup A] (S : Finset E) (e : E)
    (c : E → ℤ) (hc0 : ∀ k ∈ S.erase e, c k = 0)
    (f : E → A) (hf : ∀ k ∈ S, f k = 0) (x : A) :
    ∀ k ∈ S.erase e, f k + c k • x = 0 := by
  intro k hk
  rw [hf k (Finset.mem_of_mem_erase hk), hc0 k hk, zero_smul, add_zero]

omit [Fintype E] [DecidableEq V] in
/-- Subtracting the value on `e` along the correction chain restores vanishing on
the larger forbidden set: on `e` itself because `c e = 1`, elsewhere because both
terms already vanish. -/
theorem allowEdge_backward_zero {A : Type*} [AddCommGroup A] (S : Finset E) (e : E)
    (c : E → ℤ) (hce : c e = 1) (hc0 : ∀ k ∈ S.erase e, c k = 0)
    (g : E → A) (hg : ∀ k ∈ S.erase e, g k = 0) :
    ∀ k ∈ S, g k - c k • g e = 0 := by
  intro k hk
  by_cases hke : k = e
  · subst hke
    rw [hce, one_smul, sub_self]
  · have hk' : k ∈ S.erase e := Finset.mem_erase.mpr ⟨hke, hk⟩
    rw [hg k hk', hc0 k hk', zero_smul, sub_zero]

/-- Edge-addition step, with the unit circulation supplied as explicit data.
Allowing an edge equipped with a cycle correction amounts to choosing an old flow
together with one free coefficient-group value: the value on `e`. -/
def allowEdgeEquivOf {A : Type*} [AddCommGroup A] (S : Finset E) (e : E) (he : e ∈ S)
    (c : E → ℤ) (hc : G.IsFlow c) (hce : c e = 1) (hc0 : ∀ k ∈ S.erase e, c k = 0) :
    (G.ZeroOnFlows A S × A) ≃ G.ZeroOnFlows A (S.erase e) where
  toFun p :=
    ⟨fun k => p.1.1 k + c k • p.2,
      G.isFlow_add p.1.2.1 (G.isFlow_int_smul hc p.2),
      allowEdge_forward_zero S e c hc0 p.1.1 p.1.2.2 p.2⟩
  invFun g :=
    (⟨fun k => g.1 k - c k • g.1 e,
      G.isFlow_sub g.2.1 (G.isFlow_int_smul hc (g.1 e)),
      allowEdge_backward_zero S e c hce hc0 g.1 g.2.2⟩,
     g.1 e)
  left_inv p := by
    have hpe : p.1.1 e = 0 := p.1.2.2 e he
    apply Prod.ext
    · apply Subtype.ext
      funext k
      show p.1.1 k + c k • p.2 - c k • (p.1.1 e + c e • p.2) = p.1.1 k
      rw [hpe, hce, one_smul, zero_add, add_sub_cancel_right]
    · show p.1.1 e + c e • p.2 = p.2
      rw [hpe, hce, one_smul, zero_add]
  right_inv g := by
    apply Subtype.ext
    funext k
    show g.1 k - c k • g.1 e + c k • g.1 e = g.1 k
    rw [sub_add_cancel]

/-- The edge-addition step for an edge that merely *has* a cycle correction. -/
noncomputable def allowEdgeEquiv {A : Type*} [AddCommGroup A] (S : Finset E) (e : E) (he : e ∈ S)
    (hcycle : G.HasCycleCorrection S e) :
    (G.ZeroOnFlows A S × A) ≃ G.ZeroOnFlows A (S.erase e) :=
  G.allowEdgeEquivOf S e he hcycle.choose hcycle.choose_spec.1 hcycle.choose_spec.2.1
    hcycle.choose_spec.2.2

/-- Consequently the edge-addition step multiplies the flow count by the group
order — a quantity that sees only `Fintype.card A`. -/
theorem card_zeroOnFlows_erase_of_cycleCorrection
    {A : Type*} [AddCommGroup A] [Fintype A]
    (S : Finset E) (e : E) (he : e ∈ S) (hcycle : G.HasCycleCorrection S e) :
    Fintype.card (G.ZeroOnFlows A (S.erase e)) =
      Fintype.card (G.ZeroOnFlows A S) * Fintype.card A := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr (G.allowEdgeEquiv S e he hcycle)).symm

/-- Abstract form of the bridge case: once `e` is allowed, every flow still
vanishes on it. A separating cut supplies this certificate. -/
def IsForcedZero (S : Finset E) (e : E) : Prop :=
  ∀ (A : Type) [AddCommGroup A], ∀ f : G.ZeroOnFlows A (S.erase e), f.1 e = 0

omit [DecidableEq E] in
/-- Summing the divergence over a vertex set leaves only the signed contributions
of the edges crossing it: the discrete Gauss theorem. -/
theorem sum_divergence_eq_cut {A : Type*} [AddCommGroup A] (f : E → A) (U : Finset V) :
    (∑ v ∈ U, G.divergence f v) =
      ∑ k : E, ((if G.endAt k 0 ∈ U then f k else 0) -
        (if G.endAt k 1 ∈ U then f k else 0)) := by
  have hside : ∀ j : Fin 2,
      (∑ v ∈ U, G.endSum j f v) = ∑ k : E, if G.endAt k j ∈ U then f k else 0 := by
    intro j
    simp only [endSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  simp only [divergence]
  rw [Finset.sum_sub_distrib, hside 0, hside 1, ← Finset.sum_sub_distrib]

omit [DecidableEq V] [DecidableEq E] in
/-- `Crosses` in readable form: an edge fails to cross `U` exactly when its two
ends agree about membership in `U`. -/
theorem not_crosses_iff (U : Finset V) (k : E) :
    ¬ G.Crosses U k ↔ ((G.endAt k 0 ∈ U) ↔ (G.endAt k 1 ∈ U)) := by
  simp only [Crosses, not_ne_iff, eq_iff_iff]

omit [DecidableEq V] [DecidableEq E] in
theorem crosses_iff (U : Finset V) (k : E) :
    G.Crosses U k ↔ ¬ ((G.endAt k 0 ∈ U) ↔ (G.endAt k 1 ∈ U)) := by
  rw [← G.not_crosses_iff U k]
  exact not_not.symm

/-- A vertex cut separating the ends of `e` but crossed by no already-allowed
edge. -/
def HasCutSeparation (S : Finset E) (e : E) : Prop :=
  ∃ U : Finset V, G.Crosses U e ∧ ∀ k ∉ S, ¬ G.Crosses U k

/-- A separating cut forces the value on `e` to be zero. Summing conservation over
the cut side kills every term except the one coming from `e`, because the flow
already vanishes on the other forbidden edges and the allowed edges do not cross
the cut at all. -/
theorem isForcedZero_of_cutSeparation
    (S : Finset E) (e : E) (hcut : G.HasCutSeparation S e) :
    G.IsForcedZero S e := by
  obtain ⟨U, hcross, hallowed⟩ := hcut
  intro A _ f
  have htotal : (∑ k : E, ((if G.endAt k 0 ∈ U then f.1 k else 0) -
      (if G.endAt k 1 ∈ U then f.1 k else 0))) = 0 := by
    rw [← G.sum_divergence_eq_cut f.1 U]
    exact Finset.sum_eq_zero fun v _ => f.2.1 v
  have hsingle : (∑ k : E, ((if G.endAt k 0 ∈ U then f.1 k else 0) -
      (if G.endAt k 1 ∈ U then f.1 k else 0))) =
      (if G.endAt e 0 ∈ U then f.1 e else 0) - (if G.endAt e 1 ∈ U then f.1 e else 0) := by
    refine Fintype.sum_eq_single e fun k hke => ?_
    by_cases hkS : k ∈ S
    · rw [f.2.2 k (Finset.mem_erase.mpr ⟨hke, hkS⟩)]
      simp
    · have hsame := (G.not_crosses_iff U k).1 (hallowed k hkS)
      by_cases hk0 : G.endAt k 0 ∈ U
      · rw [if_pos hk0, if_pos (hsame.1 hk0), sub_self]
      · rw [if_neg hk0, if_neg fun h => hk0 (hsame.2 h), sub_self]
  rw [hsingle] at htotal
  have hcross' := (G.crosses_iff U e).1 hcross
  by_cases he0 : G.endAt e 0 ∈ U
  · have he1 : G.endAt e 1 ∉ U := fun h => hcross' ⟨fun _ => h, fun _ => he0⟩
    rwa [if_pos he0, if_neg he1, sub_zero] at htotal
  · have he1 : G.endAt e 1 ∈ U := by
      by_contra he1
      exact hcross' ⟨fun h => absurd h he0, fun h => absurd h he1⟩
    rw [if_neg he0, if_pos he1, zero_sub, neg_eq_zero] at htotal
    exact htotal

/-- Allowing a forced-zero edge does not change the flow space at all. -/
def allowForcedEdgeEquiv {A : Type} [AddCommGroup A] (S : Finset E) (e : E)
    (hforced : G.IsForcedZero S e) :
    G.ZeroOnFlows A S ≃ G.ZeroOnFlows A (S.erase e) where
  toFun f := ⟨f.1, f.2.1, fun k hk => f.2.2 k (Finset.mem_of_mem_erase hk)⟩
  invFun f :=
    ⟨f.1, f.2.1, fun k hk => by
      by_cases hke : k = e
      · subst hke
        exact hforced A f
      · exact f.2.2 k (Finset.mem_erase.mpr ⟨hke, hk⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_zeroOnFlows_erase_of_forced
    {A : Type} [AddCommGroup A] [Fintype A]
    (S : Finset E) (e : E) (hforced : G.IsForcedZero S e) :
    Fintype.card (G.ZeroOnFlows A (S.erase e)) = Fintype.card (G.ZeroOnFlows A S) :=
  (Fintype.card_congr (G.allowForcedEdgeEquiv S e hforced)).symm

/-- A certificate that the forbidden-edge set `S` can be reached from
`Finset.univ` by erasing one edge at a time, each step justified either by a
cycle correction or by a forced zero. -/
inductive FlowReduction (G : FiniteGraph V E) : Finset E → Prop
  | full : FlowReduction G Finset.univ
  | eraseCycle {S : Finset E} {e : E} : FlowReduction G S → e ∈ S →
      G.HasCycleCorrection S e → FlowReduction G (S.erase e)
  | eraseForced {S : Finset E} {e : E} : FlowReduction G S → e ∈ S →
      G.IsForcedZero S e → FlowReduction G (S.erase e)

/-- Group-order invariance holds for every forbidden-edge set carrying a reduction
certificate: each step of the recurrence either multiplies both counts by the
(equal) group orders or leaves both alone. -/
theorem card_zeroOnFlows_eq_of_reduction
    {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    {S : Finset E} (hred : G.FlowReduction S)
    (hcard : Fintype.card A = Fintype.card B) :
    Fintype.card (G.ZeroOnFlows A S) = Fintype.card (G.ZeroOnFlows B S) := by
  induction hred with
  | full => simp
  | @eraseCycle S e _ he hcycle ih =>
      rw [G.card_zeroOnFlows_erase_of_cycleCorrection (A := A) S e he hcycle,
        G.card_zeroOnFlows_erase_of_cycleCorrection (A := B) S e he hcycle, ih, hcard]
  | @eraseForced S e _ he hforced ih =>
      rw [G.card_zeroOnFlows_erase_of_forced (A := A) S e hforced,
        G.card_zeroOnFlows_erase_of_forced (A := B) S e hforced, ih]

/-! ### Inclusion–exclusion -/

section InclusionExclusion

/-- Membership in a `Finset`-valued `Finset.inf`, from the lattice adjunction:
`s.inf F` is the largest finset contained in every `F i`. -/
private theorem mem_finsetInf {ι α : Type*} [DecidableEq α] [Fintype α]
    (s : Finset ι) (F : ι → Finset α) (x : α) :
    x ∈ s.inf F ↔ ∀ i ∈ s, x ∈ F i := by
  constructor
  · intro hx i hi
    exact Finset.le_iff_subset.mp (Finset.inf_le hi) hx
  · intro h
    have hle : ({x} : Finset α) ≤ s.inf F :=
      Finset.le_inf fun i hi => Finset.le_iff_subset.mpr
        (Finset.singleton_subset_iff.mpr (h i hi))
    exact Finset.singleton_subset_iff.mp (Finset.le_iff_subset.mp hle)

/-- Inclusion–exclusion reduces counting nowhere-zero flows to counting, for each
edge subset `S`, the flows that vanish on all of `S`. This is the interface at
which the edge-addition recurrence attaches. -/
theorem card_nowhereZeroFlows_eq_sum_zeroOn
    (A : Type*) [AddCommGroup A] [Fintype A] :
    (Fintype.card (G.NowhereZeroFlows A) : ℤ) =
      ∑ S ∈ (Finset.univ : Finset E).powerset,
        (-1 : ℤ) ^ S.card * Fintype.card (G.ZeroOnFlows A S) := by
  classical
  -- inside the finite universe of all flows, the "bad" event attached to `e`
  set bad : E → Finset (G.Flows A) :=
    fun e => Finset.univ.filter fun f => f.1 e = 0 with hbaddef
  have hbad : ∀ (e : E) (f : G.Flows A), f ∈ bad e ↔ f.1 e = 0 := by
    intro e f
    simp [hbaddef]
  -- the two translations between subtypes of flows and finsets of flows
  have hzero : ∀ S : Finset E,
      Fintype.card (G.ZeroOnFlows A S) = (S.inf bad).card := by
    intro S
    rw [← Fintype.card_coe (S.inf bad)]
    exact Fintype.card_congr
      { toFun := fun f =>
          ⟨⟨f.1, f.2.1⟩, (mem_finsetInf S bad _).2 fun e he => (hbad e _).2 (f.2.2 e he)⟩
        invFun := fun x =>
          ⟨x.1.1, x.1.2, fun e he => (hbad e _).1 ((mem_finsetInf S bad _).1 x.2 e he)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hgood : Fintype.card (G.NowhereZeroFlows A) =
      ((Finset.univ : Finset E).inf fun e => (bad e)ᶜ).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun f =>
          ⟨⟨f.1, f.2.1⟩, (mem_finsetInf _ _ _).2 fun e _ =>
            Finset.mem_compl.2 fun hc => f.2.2 e ((hbad e _).1 hc)⟩
        invFun := fun x =>
          ⟨x.1.1, x.1.2, fun e hz =>
            Finset.mem_compl.1 ((mem_finsetInf _ _ _).1 x.2 e (Finset.mem_univ e))
              ((hbad e _).2 hz)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hgood, Finset.inclusion_exclusion_card_inf_compl]
  exact Finset.sum_congr rfl fun S _ => by rw [hzero S]

end InclusionExclusion

/-- Equality of all the vanishing-flow counts propagates to the nowhere-zero flow
counts, term by term through the alternating sum. -/
theorem card_nowhereZeroFlows_eq_of_zeroOn
    {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (hzero : ∀ S : Finset E,
      Fintype.card (G.ZeroOnFlows A S) = Fintype.card (G.ZeroOnFlows B S)) :
    Fintype.card (G.NowhereZeroFlows A) = Fintype.card (G.NowhereZeroFlows B) := by
  have hcast : (Fintype.card (G.NowhereZeroFlows A) : ℤ) =
      (Fintype.card (G.NowhereZeroFlows B) : ℤ) := by
    rw [G.card_nowhereZeroFlows_eq_sum_zeroOn A, G.card_nowhereZeroFlows_eq_sum_zeroOn B]
    exact Finset.sum_congr rfl fun S _ => by rw [hzero S]
  exact_mod_cast hcast

/-! ### Assembling the invariance theorem -/

/-- The vanishing-flow form of group-order invariance: for every forbidden edge
set, the number of flows depends only on the coefficient-group order. -/
def ZeroOnCardinalityInvariant : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B],
    Fintype.card A = Fintype.card B → ∀ S : Finset E,
      Fintype.card (G.ZeroOnFlows A S) = Fintype.card (G.ZeroOnFlows B S)

theorem zeroOnCardinalityInvariant_of_reductions
    (hred : ∀ S : Finset E, G.FlowReduction S) : G.ZeroOnCardinalityInvariant :=
  fun _ _ _ _ _ _ hcard S => G.card_zeroOnFlows_eq_of_reduction (hred S) hcard

/-- A per-edge dichotomy upgrades to a reduction certificate for every edge set:
erase the complement of `S` one edge at a time, starting from `Finset.univ`. -/
theorem reductions_of_step_classification
    (hstep : ∀ (S : Finset E) (e : E), e ∈ S →
      G.HasCycleCorrection S e ∨ G.IsForcedZero S e) :
    ∀ S : Finset E, G.FlowReduction S := by
  have aux : ∀ T : Finset E, G.FlowReduction Tᶜ := by
    intro T
    induction T using Finset.induction with
    | empty => simpa using (FlowReduction.full : G.FlowReduction (Finset.univ : Finset E))
    | insert e T heT ih =>
        have heT' : e ∈ (Tᶜ : Finset E) := Finset.mem_compl.mpr heT
        rw [Finset.compl_insert]
        rcases hstep Tᶜ e heT' with hcycle | hforced
        · exact FlowReduction.eraseCycle ih heT' hcycle
        · exact FlowReduction.eraseForced ih heT' hforced
  intro S
  simpa using aux Sᶜ

theorem zeroOnCardinalityInvariant_of_step_classification
    (hstep : ∀ (S : Finset E) (e : E), e ∈ S →
      G.HasCycleCorrection S e ∨ G.IsForcedZero S e) :
    G.ZeroOnCardinalityInvariant :=
  G.zeroOnCardinalityInvariant_of_reductions (G.reductions_of_step_classification hstep)

/-- The purely graph-theoretic input to the whole argument: for every forbidden
edge set `S` and every `e ∈ S`, either `e` carries a unit circulation avoiding
the rest of `S`, or a cut separates the ends of `e` without meeting any allowed
edge. Discharged for every finite graph in `PathCut.lean`. -/
def IntegralPathCutDichotomy : Prop :=
  ∀ (S : Finset E) (e : E), e ∈ S →
    G.HasCycleCorrection S e ∨ G.HasCutSeparation S e

theorem zeroOnCardinalityInvariant_of_pathCut
    (hpc : G.IntegralPathCutDichotomy) : G.ZeroOnCardinalityInvariant := by
  refine G.zeroOnCardinalityInvariant_of_step_classification fun S e he => ?_
  rcases hpc S e he with hcycle | hcut
  · exact Or.inl hcycle
  · exact Or.inr (G.isForcedZero_of_cutSeparation S e hcut)

/-- **Tutte's group-order invariance**, in the exact local form the coefficient
transfer needs: two finite abelian groups of the same cardinality admit the same
number of nowhere-zero flows on `G`. -/
def FlowCardinalityInvariant : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B],
    Fintype.card A = Fintype.card B →
      Fintype.card (G.NowhereZeroFlows A) = Fintype.card (G.NowhereZeroFlows B)

theorem flowCardinalityInvariant_of_zeroOn
    (hzero : G.ZeroOnCardinalityInvariant) : G.FlowCardinalityInvariant :=
  fun A B _ _ _ _ hcard => G.card_nowhereZeroFlows_eq_of_zeroOn (hzero A B hcard)

theorem flowCardinalityInvariant_of_pathCut
    (hpc : G.IntegralPathCutDichotomy) : G.FlowCardinalityInvariant :=
  G.flowCardinalityInvariant_of_zeroOn (G.zeroOnCardinalityInvariant_of_pathCut hpc)

/-! ### Coefficient transfer -/

/-- The structured nowhere-zero flow of step 1 and the element of the finite flow
type are the same data. -/
def nowhereZeroFlowEquiv (A : Type*) [AddCommGroup A] :
    G.NowhereZeroFlow A ≃ G.NowhereZeroFlows A where
  toFun f := ⟨f.val, f.conservation, f.nowhereZero⟩
  invFun f := { val := f.1, conservation := f.2.1, nowhereZero := f.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equal counts transfer existence: this is the only consequence of the counting
theorem that the CDC argument actually uses. -/
theorem transfer_of_cardinality
    (hcount : G.FlowCardinalityInvariant)
    {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (hcard : Fintype.card A = Fintype.card B) :
    Nonempty (G.NowhereZeroFlow A) → Nonempty (G.NowhereZeroFlow B) := by
  intro hA
  have hposA : 0 < Fintype.card (G.NowhereZeroFlows A) :=
    Fintype.card_pos_iff.mpr (hA.map (G.nowhereZeroFlowEquiv A))
  have hposB : 0 < Fintype.card (G.NowhereZeroFlows B) := by
    rwa [← hcount A B hcard]
  exact (Fintype.card_pos_iff.mp hposB).map (G.nowhereZeroFlowEquiv B).symm

/-- `ZMod 8` and `Gamma = F₂³` are the two abelian groups of order eight. They are
not isomorphic, which is exactly why the transfer below needs a counting theorem
rather than a relabelling. -/
theorem card_zmodEight_eq_gamma : Fintype.card (ZMod 8) = Fintype.card Gamma := by
  decide

/-- The coefficient transfer the CDC construction needs, conditional only on the
named instance of Tutte's counting theorem. -/
theorem zmodEight_to_gamma (hcount : G.FlowCardinalityInvariant) :
    Nonempty (G.NowhereZeroFlow (ZMod 8)) → Nonempty (G.NowhereZeroFlow Gamma) :=
  G.transfer_of_cardinality hcount card_zmodEight_eq_gamma

/-- The complete local implication starting from Seymour's integral six-flow
conclusion: reduce mod eight (step 5a), then transfer to `Gamma`. -/
theorem sixFlow_to_gamma (hcount : G.FlowCardinalityInvariant) :
    Nonempty G.SixFlow → Nonempty (G.NowhereZeroFlow Gamma) := fun hSix =>
  G.zmodEight_to_gamma hcount (hSix.map fun sf => sf.toZModEight)

/-- The same implication with the graph-theoretic interface exposed directly. -/
theorem sixFlow_to_gamma_of_pathCut (hpc : G.IntegralPathCutDichotomy) :
    Nonempty G.SixFlow → Nonempty (G.NowhereZeroFlow Gamma) :=
  G.sixFlow_to_gamma (G.flowCardinalityInvariant_of_pathCut hpc)

end FiniteGraph

end CycleDoubleCover
