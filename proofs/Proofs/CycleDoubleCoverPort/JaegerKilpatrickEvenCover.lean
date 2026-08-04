import Proofs.CycleDoubleCoverPort.NashWilliams
import Proofs.CycleDoubleCoverPort.FlowCount
import Mathlib.Algebra.CharP.Two

-- Ported from openai/cdc-lean, JaegerKilpatrick.lean (lines 12-178), vendored with
-- adaptation per operator decision 2026-08-03. Part of epic #37507.

/-!
# Jaeger--Kilpatrick, segment 1: even-cover flows and the spanning-tree superset

This file is the first segment of the port of upstream `JaegerKilpatrick.lean`, which
proves the group-valued form of the eight-flow theorem with coefficient group
`Gamma = (ZMod 2)^3`. A `Gamma`-flow is assembled from three even edge sets, so the
two halves of the argument ported here are:

* **Assembly** (`nowhereZeroGammaFlow_of_evenCover`): three even edge sets that
  together cover every edge give a nowhere-zero `Gamma`-flow, the coordinate `i` of
  the flow being the indicator of the `i`-th set. Evenness is exactly conservation in
  characteristic two, and covering is exactly nowhere-vanishing.

* **Supply** (`exists_even_superset_compl_of_spanningTree`): the complement of a
  spanning tree extends to an even edge set. Each non-tree edge is routed through the
  tree (`hasIntegerPath_of_reachableIn_of_disjoint`), closed into a fundamental cycle
  (`hasCycleCorrection_of_integerPath` from `FlowCount`), and the resulting integral
  circulations are summed (`isFlow_sum_int`) and reduced mod two
  (`isFlow_intCast_f2`); the support of that `F₂` circulation is even
  (`isEvenEdgeSet_support_of_isFlow_f2`) and contains every non-tree edge because the
  fundamental cycle of an edge is the only summand charging it.

Later segments (three-edge-connectivity, the double graph, and the eight-flow theorem
proper) consume these declarations by name, so no upstream name is changed here.
-/

namespace CycleDoubleCover

namespace FiniteGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (H : FiniteGraph V E)

/-- The `Gamma`-valued function encoded by three edge sets. -/
noncomputable def gammaOfEvenCover (F : Fin 3 → Finset E) : E → Gamma :=
  fun e i => if e ∈ F i then 1 else 0

/-- Three even edge sets covering every edge give a nowhere-zero `Gamma`-flow. -/
theorem nowhereZeroGammaFlow_of_evenCover
    (F : Fin 3 → Finset E)
    (hEven : ∀ i, H.IsEvenEdgeSet (F i))
    (hCover : ∀ e : E, ∃ i : Fin 3, e ∈ F i) :
    Nonempty (H.NowhereZeroFlow Gamma) := by
  classical
  refine ⟨⟨gammaOfEvenCover F, ?_, ?_⟩⟩
  · intro v
    funext i
    have hi := hEven i v
    simp only [edgeIncidence] at hi
    rw [Finset.sum_add_distrib] at hi
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply]
    have hsum (j : Fin 2) :
        (∑ e : E,
          (if H.endAt e j = v then gammaOfEvenCover F e else 0) i) =
          ∑ e ∈ F i, if H.endAt e j = v then (1 : F₂) else 0 := by
      calc
        _ = ∑ e : E,
            if e ∈ F i then (if H.endAt e j = v then (1 : F₂) else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro e _
              by_cases he : e ∈ F i <;> by_cases hev : H.endAt e j = v <;>
                simp [gammaOfEvenCover, he, hev]
        _ = _ := by
          simp
    rw [hsum 0, hsum 1]
    simpa [sub_eq_add_neg] using hi
  · intro e he
    obtain ⟨i, hei⟩ := hCover e
    have := congrFun he i
    simp [gammaOfEvenCover, hei] at this

/-- A route using `T` gives an integral path avoiding every edge in a disjoint set `S`. -/
theorem hasIntegerPath_of_reachableIn_of_disjoint
    {S T : Finset E} {u v : V} (hST : Disjoint S T)
    (h : H.ReachableIn T u v) : H.HasIntegerPath S u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact H.hasIntegerPath_refl S _
  | @cons x y z hxy p ih =>
      rw [H.supportGraph_adj_iff T x y] at hxy
      rcases hxy with ⟨_, e, heT, hends | hends⟩
      · have heS : e ∉ S := by
          intro heS
          exact Finset.disjoint_left.mp hST heS heT
        have hstep := H.hasIntegerPath_single S e heS
        have hstep' : H.HasIntegerPath S x y := by
          simpa [hends.1, hends.2] using hstep
        exact FiniteGraph.HasIntegerPath.trans (G := H) hstep' ih
      · have heS : e ∉ S := by
          intro heS
          exact Finset.disjoint_left.mp hST heS heT
        have hstep := (H.hasIntegerPath_single S e heS).symm
        have hstep' : H.HasIntegerPath S x y := by
          simpa [hends.1, hends.2] using hstep
        exact FiniteGraph.HasIntegerPath.trans (G := H) hstep' ih

/-- Finite sums of integer flows are integer flows. -/
theorem isFlow_sum_int (s : Finset E) (c : E → E → ℤ)
    (hc : ∀ e ∈ s, H.IsFlow (c e)) :
    H.IsFlow (∑ e ∈ s, c e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsFlow]
  | @insert e s heS ih =>
      rw [Finset.sum_insert heS]
      exact H.isFlow_add (hc e (by simp))
        (ih (fun f hf => hc f (by simp [hf])))

omit [DecidableEq E] in
/-- Reducing an integer circulation modulo two gives an `F₂` circulation. -/
theorem isFlow_intCast_f2 {c : E → ℤ} (hc : H.IsFlow c) :
    H.IsFlow (fun e => (c e : F₂)) := by
  intro v
  have h := congrArg (fun z : ℤ => (z : F₂)) (hc v)
  simpa only [IsFlow, Int.cast_sub, Int.cast_sum, Int.cast_ite, Int.cast_zero] using h

private theorem f2_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [DecidableEq E] in
/-- The support of an `F₂` circulation is an even edge set. -/
theorem isEvenEdgeSet_support_of_isFlow_f2 (f : E → F₂) (hf : H.IsFlow f) :
    H.IsEvenEdgeSet (Finset.univ.filter fun e => f e = 1) := by
  intro v
  have hv := hf v
  rw [sub_eq_add_neg] at hv
  rw [ZMod.neg_eq_self_mod_two] at hv
  rw [← Finset.sum_add_distrib] at hv
  calc
    ∑ e ∈ Finset.univ.filter (fun e => f e = 1), H.edgeIncidence v e =
        ∑ e : E,
          ((if H.endAt e 0 = v then f e else 0) +
            if H.endAt e 1 = v then f e else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      rcases f2_eq_zero_or_one (f e) with he | he <;>
        simp [edgeIncidence, he]
    _ = 0 := hv

/-- The complement of a spanning tree can be completed to an even edge set.  For every
non-tree edge, route its two ends through the tree and sum the resulting fundamental
cycles modulo two. -/
theorem exists_even_superset_compl_of_spanningTree [Nonempty V]
    (T : Finset E) (hT : H.IsSpanningTree T) :
    ∃ F : Finset E, H.IsEvenEdgeSet F ∧ ∀ e : E, e ∉ T → e ∈ F := by
  classical
  let S : Finset E := Finset.univ \ T
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.2
    intro e heS heT
    exact (Finset.mem_sdiff.mp heS).2 heT
  have hcorr : ∀ e ∈ S, H.HasCycleCorrection S e := by
    intro e heS
    apply H.hasCycleCorrection_of_integerPath S e heS
    apply H.hasIntegerPath_of_reachableIn_of_disjoint hST
    exact hT.1.preconnected _ _
  let c : E → E → ℤ := fun e =>
    if he : e ∈ S then Classical.choose (hcorr e he) else 0
  have hc_spec (e : E) (he : e ∈ S) :
      H.IsFlow (c e) ∧ c e e = 1 ∧ ∀ k ∈ S.erase e, c e k = 0 := by
    dsimp [c]
    rw [dif_pos he]
    exact Classical.choose_spec (hcorr e he)
  let q : E → ℤ := ∑ e ∈ S, c e
  have hqflow : H.IsFlow q := by
    dsimp [q]
    apply H.isFlow_sum_int S c
    intro e he
    exact (hc_spec e he).1
  let f : E → F₂ := fun e => (q e : F₂)
  let F : Finset E := Finset.univ.filter fun e => f e = 1
  refine ⟨F, H.isEvenEdgeSet_support_of_isFlow_f2 f ?_, ?_⟩
  · exact H.isFlow_intCast_f2 hqflow
  · intro e heT
    have heS : e ∈ S := by simp [S, heT]
    have hqe : q e = 1 := by
      dsimp [q]
      rw [Finset.sum_apply]
      calc
        _ = c e e := by
          apply Finset.sum_eq_single e
          · intro b hb hbe
            exact (hc_spec b hb).2.2 e
              (Finset.mem_erase.mpr ⟨Ne.symm hbe, heS⟩)
          · intro he
            exact (he heS).elim
        _ = 1 := (hc_spec e heS).2.1
    simp [F, f, hqe]

end FiniteGraph

end CycleDoubleCover
