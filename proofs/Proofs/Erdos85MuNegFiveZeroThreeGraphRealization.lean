import Proofs.Erdos85MuNegFiveZeroThreeOwnerServiceBridge
import Proofs.Erdos85SizeTwoMuNegFiveAlignedShoreSwitch
import Proofs.Erdos85SizeTwoOwnerVertexDictionary
import Proofs.Erdos85MuNegOneOneFourCodeVertexMap

/-!
# Graph realization of the h503 owner relations

The 72 finite candidates consist of eight fixed antipodal within-shore pairs
and all 64 cross pairs.  This file maps their Nat codes to the two cyclic
shore embeddings and realizes activity/hits by exterior owner vertices.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- Interpret codes `0..7` on the first shore and `8..15` on the second. -/
def muNegFiveZeroThreeCodeVertex
    (u v : ZMod 8 → c.supp) (x : Nat) : V :=
  if x < 8 then (u (x : ZMod 8)).1
  else (v ((x - 8 : Nat) : ZMod 8)).1

theorem muNegFiveZeroThreeCodeVertex_mem_supp
    (u v : ZMod 8 → c.supp) (x : Nat) :
    muNegFiveZeroThreeCodeVertex G c u v x ∈ c.supp := by
  unfold muNegFiveZeroThreeCodeVertex
  split
  · exact (u _).2
  · exact (v _).2

def muNegFiveZeroThreeOwnerEndpoints
    (u v : ZMod 8 → c.supp) (e : Nat) : V × V :=
  let p := muNegFiveZeroThreeOwnerAt e
  (muNegFiveZeroThreeCodeVertex G c u v p.1,
    muNegFiveZeroThreeCodeVertex G c u v p.2)

def MuNegFiveZeroThreeOwnerVertex
    (u v : ZMod 8 → c.supp) (e : Nat) (z : V) : Prop :=
  z ∉ c.supp ∧
    G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).1 z ∧
    G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).2 z

def muNegFiveZeroThreeGraphActive
    (u v : ZMod 8 → c.supp) (e : Fin 72) : Prop :=
  ∃ z : V, MuNegFiveZeroThreeOwnerVertex G c u v e z

def muNegFiveZeroThreeGraphHit
    (u v : ZMod 8 → c.supp) (e f : Fin 72) : Prop :=
  ∃ z w : V,
    MuNegFiveZeroThreeOwnerVertex G c u v e z ∧
    MuNegFiveZeroThreeOwnerVertex G c u v f w ∧ G.Adj z w

def MuNegFiveZeroThreeOwnerAvailability
    (u v : ZMod 8 → c.supp) : Prop :=
  ∀ e : Fin 72,
    muNegFiveZeroThreeOwnerEnabled
      (muNegFiveZeroThreeGraphActive G c u v) e →
      muNegFiveZeroThreeGraphActive G c u v e

def MuNegFiveZeroThreeExteriorOwnerCoverage
    (u v : ZMod 8 → c.supp) : Prop :=
  ∀ z : V, z ∉ c.supp →
    ∃ e : Fin 72, MuNegFiveZeroThreeOwnerVertex G c u v e z

section Shores

variable [DecidableEq (G.induce c.supp).ConnectedComponent]
  (a b : (G.induce c.supp).ConnectedComponent)
  (u v : ZMod 8 → c.supp)

theorem muNegFiveZeroThreeCodeVertex_inj
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ x, x < 16 → ∀ y, y < 16 →
      muNegFiveZeroThreeCodeVertex G c u v x =
        muNegFiveZeroThreeCodeVertex G c u v y → x = y := by
  simpa only [muNegFiveZeroThreeCodeVertex, muNegOneCodeVertex] using
    muNegOneCodeVertex_inj G c a b u v hab huinj hvinj hurange hvrange

theorem muNegFiveZeroThreeCycleAdj_eq_muNegOneGAdj :
    ∀ x, x < 16 → ∀ y, y < 16 →
      eightEightHighCycleAdj x y = muNegOneGAdj x y := by
  native_decide

theorem muNegFiveZeroThreeCodeVertex_adj_iff
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ x, x < 16 → ∀ y, y < 16 →
      (G.Adj (muNegFiveZeroThreeCodeVertex G c u v x)
        (muNegFiveZeroThreeCodeVertex G c u v y) ↔
          eightEightHighCycleAdj x y = true) := by
  intro x hx y hy
  rw [muNegFiveZeroThreeCycleAdj_eq_muNegOneGAdj x hx y hy]
  simpa only [muNegFiveZeroThreeCodeVertex, muNegOneCodeVertex] using
    muNegOneCodeVertex_adj_iff G c a b u v hab huinj hvinj hurange hvrange
      hu hv x hx y hy

theorem muNegFiveZeroThreeOwnerAt_bounds_ne (e : Fin 72) :
    (muNegFiveZeroThreeOwnerAt e).1 < 16 ∧
      (muNegFiveZeroThreeOwnerAt e).2 < 16 ∧
      (muNegFiveZeroThreeOwnerAt e).1 ≠
        (muNegFiveZeroThreeOwnerAt e).2 := by
  revert e
  native_decide

theorem muNegFiveZeroThreeOwnerAt_fst_lt_snd (e : Fin 72) :
    (muNegFiveZeroThreeOwnerAt e).1 <
      (muNegFiveZeroThreeOwnerAt e).2 := by
  revert e
  native_decide

theorem muNegFiveZeroThreeOwnerAt_injective :
    Function.Injective (fun e : Fin 72 => muNegFiveZeroThreeOwnerAt e) := by
  intro e f h
  revert e f
  native_decide

theorem muNegFiveZeroThreeOwnerEndpoints_ne
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (e : Fin 72) :
    (muNegFiveZeroThreeOwnerEndpoints G c u v e).1 ≠
      (muNegFiveZeroThreeOwnerEndpoints G c u v e).2 := by
  intro h
  let p := muNegFiveZeroThreeOwnerAt e
  have hp := muNegFiveZeroThreeOwnerAt_bounds_ne e
  change muNegFiveZeroThreeCodeVertex G c u v p.1 =
    muNegFiveZeroThreeCodeVertex G c u v p.2 at h
  have heq : p.1 = p.2 :=
    muNegFiveZeroThreeCodeVertex_inj G c a b u v hab huinj hvinj
      hurange hvrange p.1 hp.1 p.2 hp.2.1 h
  exact hp.2.2 heq

theorem muNegFiveZeroThreeOwnerVertex_unique
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (e : Fin 72) {z w : V}
    (hz : MuNegFiveZeroThreeOwnerVertex G c u v e z)
    (hw : MuNegFiveZeroThreeOwnerVertex G c u v e w) : z = w :=
  commonServer_unique G hfree
    (muNegFiveZeroThreeOwnerEndpoints_ne G c a b u v hab huinj hvinj
      hurange hvrange e)
    hz.2.1 hz.2.2 hw.2.1 hw.2.2

theorem muNegFiveZeroThreeOwnerVertex_inj
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {e f : Fin 72} {z : V}
    (he : MuNegFiveZeroThreeOwnerVertex G c u v e z)
    (hf : MuNegFiveZeroThreeOwnerVertex G c u v f z) : e = f := by
  have hpair := ownerVertex_pair_eq G hfree (by omega) hreg hcard c hsize
    (muNegFiveZeroThreeOwnerEndpoints_ne G c a b u v hab huinj hvinj
      hurange hvrange e)
    (muNegFiveZeroThreeOwnerEndpoints_ne G c a b u v hab huinj hvinj
      hurange hvrange f)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    he.2.1.symm he.2.2.symm hf.2.1.symm hf.2.2.symm
  simp only [muNegFiveZeroThreeOwnerEndpoints] at hpair
  have heBounds := muNegFiveZeroThreeOwnerAt_bounds_ne e
  have hfBounds := muNegFiveZeroThreeOwnerAt_bounds_ne f
  have heOrder := muNegFiveZeroThreeOwnerAt_fst_lt_snd e
  have hfOrder := muNegFiveZeroThreeOwnerAt_fst_lt_snd f
  have hinj := muNegFiveZeroThreeCodeVertex_inj G c a b u v hab huinj
    hvinj hurange hvrange
  have hf1 :
      muNegFiveZeroThreeCodeVertex G c u v (muNegFiveZeroThreeOwnerAt f).1 ∈
        ({muNegFiveZeroThreeCodeVertex G c u v (muNegFiveZeroThreeOwnerAt e).1,
          muNegFiveZeroThreeCodeVertex G c u v (muNegFiveZeroThreeOwnerAt e).2} :
          Finset V) := by
    rw [hpair]
    exact Finset.mem_insert_self _ _
  have hf2 :
      muNegFiveZeroThreeCodeVertex G c u v (muNegFiveZeroThreeOwnerAt f).2 ∈
        ({muNegFiveZeroThreeCodeVertex G c u v (muNegFiveZeroThreeOwnerAt e).1,
          muNegFiveZeroThreeCodeVertex G c u v (muNegFiveZeroThreeOwnerAt e).2} :
          Finset V) := by
    rw [hpair]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hf1' := Finset.mem_insert.mp hf1
  have hf2' := Finset.mem_insert.mp hf2
  rw [Finset.mem_singleton] at hf1' hf2'
  have hpairs : muNegFiveZeroThreeOwnerAt e =
      muNegFiveZeroThreeOwnerAt f := by
    apply Prod.ext
    · rcases hf1' with h1 | h1
      · exact (hinj _ hfBounds.1 _ heBounds.1 h1).symm
      · have hswap1 := hinj _ hfBounds.1 _ heBounds.2.1 h1
        rcases hf2' with h2 | h2
        · have hsame := hinj _ hfBounds.2.1 _ heBounds.1 h2
          omega
        · have hcontra := hinj _ hfBounds.1 _ hfBounds.2.1
            (h1.trans h2.symm)
          exact (hfBounds.2.2 hcontra).elim
    · rcases hf2' with h2 | h2
      · rcases hf1' with h1 | h1
        · have hcontra := hinj _ hfBounds.1 _ hfBounds.2.1
            (h1.trans h2.symm)
          exact (hfBounds.2.2 hcontra).elim
        · have hswap1 := hinj _ hfBounds.1 _ heBounds.2.1 h1
          have hswap2 := hinj _ hfBounds.2.1 _ heBounds.1 h2
          omega
      · exact (hinj _ hfBounds.2.1 _ heBounds.2.1 h2).symm
  exact muNegFiveZeroThreeOwnerAt_injective hpairs

theorem muNegFiveZeroThreeOwnerVertex_adj_of_contains
    {e : Fin 72} {z : V}
    (hz : MuNegFiveZeroThreeOwnerVertex G c u v e z)
    {s : Fin 16} (hs : muNegFiveZeroThreeOwnerContains e s = true) :
    G.Adj z (muNegFiveZeroThreeCodeVertex G c u v s) := by
  unfold muNegFiveZeroThreeOwnerContains at hs
  simp only [Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with hs | hs
  · simpa only [muNegFiveZeroThreeOwnerEndpoints, hs] using hz.2.1.symm
  · simpa only [muNegFiveZeroThreeOwnerEndpoints, hs] using hz.2.2.symm

theorem muNegFiveZeroThree_no_owner_endpoint_edge
    (hfree : ¬ containsC4 V G)
    {e f : Fin 72} {te tf : V}
    (hte : MuNegFiveZeroThreeOwnerVertex G c u v e te)
    (htf : MuNegFiveZeroThreeOwnerVertex G c u v f tf)
    (hetf : G.Adj te tf)
    {x y : V}
    (hx : x = (muNegFiveZeroThreeOwnerEndpoints G c u v e).1 ∨
      x = (muNegFiveZeroThreeOwnerEndpoints G c u v e).2)
    (hy : y = (muNegFiveZeroThreeOwnerEndpoints G c u v f).1 ∨
      y = (muNegFiveZeroThreeOwnerEndpoints G c u v f).2) :
    ¬ G.Adj x y := by
  intro hxy
  have htex : G.Adj te x := by
    rcases hx with rfl | rfl
    · exact hte.2.1.symm
    · exact hte.2.2.symm
  have htfy : G.Adj tf y := by
    rcases hy with rfl | rfl
    · exact htf.2.1.symm
    · exact htf.2.2.symm
  have hne : te ≠ y := by
    intro h
    apply hte.1
    rw [h]
    rcases hy with rfl | rfl <;>
      exact muNegFiveZeroThreeCodeVertex_mem_supp G c u v _
  have heq := commonServer_unique G hfree hne
    htex hxy.symm hetf htfy.symm
  apply htf.1
  rw [← heq]
  rcases hx with rfl | rfl <;>
    exact muNegFiveZeroThreeCodeVertex_mem_supp G c u v _

theorem muNegFiveZeroThreeOwnerTargetContains_of_adj
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {e f : Fin 72} {te tf : V}
    (hte : MuNegFiveZeroThreeOwnerVertex G c u v e te)
    (htf : MuNegFiveZeroThreeOwnerVertex G c u v f tf)
    (hetf : G.Adj te tf) :
    muNegFiveZeroThreeOwnerTargetContains e
      (muNegFiveZeroThreeOwnerAt f).1 = true ∧
    muNegFiveZeroThreeOwnerTargetContains e
      (muNegFiveZeroThreeOwnerAt f).2 = true := by
  have heBounds := muNegFiveZeroThreeOwnerAt_bounds_ne e
  have hfBounds := muNegFiveZeroThreeOwnerAt_bounds_ne f
  unfold muNegFiveZeroThreeOwnerTargetContains
  simp only [Bool.and_eq_true]
  constructor
  · constructor
    · rw [Bool.not_eq_true_eq_eq_false]
      apply Bool.eq_false_of_not_eq_true
      intro hadj
      exact muNegFiveZeroThree_no_owner_endpoint_edge G c u v hfree hte htf
        hetf (Or.inl rfl) (Or.inl rfl)
        ((muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab huinj hvinj
          hurange hvrange hu hv _ heBounds.1 _ hfBounds.1).mpr hadj)
    · rw [Bool.not_eq_true_eq_eq_false]
      apply Bool.eq_false_of_not_eq_true
      intro hadj
      exact muNegFiveZeroThree_no_owner_endpoint_edge G c u v hfree hte htf
        hetf (Or.inr rfl) (Or.inl rfl)
        ((muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab huinj hvinj
          hurange hvrange hu hv _ heBounds.2.1 _ hfBounds.1).mpr hadj)
  · constructor
    · rw [Bool.not_eq_true_eq_eq_false]
      apply Bool.eq_false_of_not_eq_true
      intro hadj
      exact muNegFiveZeroThree_no_owner_endpoint_edge G c u v hfree hte htf
        hetf (Or.inl rfl) (Or.inr rfl)
        ((muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab huinj hvinj
          hurange hvrange hu hv _ heBounds.1 _ hfBounds.2.1).mpr hadj)
    · rw [Bool.not_eq_true_eq_eq_false]
      apply Bool.eq_false_of_not_eq_true
      intro hadj
      exact muNegFiveZeroThree_no_owner_endpoint_edge G c u v hfree hte htf
        hetf (Or.inr rfl) (Or.inr rfl)
        ((muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab huinj hvinj
          hurange hvrange hu hv _ heBounds.2.1 _ hfBounds.2.1).mpr hadj)

theorem muNegFiveZeroThreeOwnerCompatible_of_graphHit
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {e f : Fin 72}
    (hef : muNegFiveZeroThreeGraphHit G c u v e f) :
    muNegFiveZeroThreeOwnerCompatible e f = true := by
  obtain ⟨te, tf, hte, htf, hetf⟩ := hef
  have hne : e ≠ f := by
    intro h
    subst f
    have heq := muNegFiveZeroThreeOwnerVertex_unique G c a b u v hfree hab
      huinj hvinj hurange hvrange e hte htf
    subst tf
    exact G.loopless.irrefl te hetf
  have hefTargets := muNegFiveZeroThreeOwnerTargetContains_of_adj G c a b u v
    hfree hab huinj hvinj hurange hvrange hu hv hte htf hetf
  have hfeTargets := muNegFiveZeroThreeOwnerTargetContains_of_adj G c a b u v
    hfree hab huinj hvinj hurange hvrange hu hv htf hte hetf.symm
  have hneVal : e.val ≠ f.val := fun h => hne (Fin.ext h)
  unfold muNegFiveZeroThreeOwnerCompatible
  simp only [bne_iff_ne, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hneVal, hefTargets.1⟩, hefTargets.2⟩,
    hfeTargets.1⟩, hfeTargets.2⟩

theorem muNegFiveZeroThreeGraphHit_internal_zero
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ (e : Fin 72) (s : Fin 16) (f : Fin 72),
      muNegFiveZeroThreeOwnerTargetContains e s = false →
      muNegFiveZeroThreeOwnerContains f s = true →
      ¬ muNegFiveZeroThreeGraphHit G c u v e f := by
  intro e s f htarget hcontains hhit
  have hcompat := muNegFiveZeroThreeOwnerCompatible_of_graphHit G c a b u v
    hfree hab huinj hvinj hurange hvrange hu hv hhit
  unfold muNegFiveZeroThreeOwnerCompatible at hcompat
  simp only [Bool.and_eq_true] at hcompat
  rcases hcompat with ⟨⟨⟨⟨_, he1⟩, he2⟩, _⟩, _⟩
  unfold muNegFiveZeroThreeOwnerContains at hcontains
  simp only [Bool.or_eq_true, beq_iff_eq] at hcontains
  rcases hcontains with h | h
  · rw [← h] at htarget
    exact Bool.false_ne_true (htarget.symm.trans he1)
  · rw [← h] at htarget
    exact Bool.false_ne_true (htarget.symm.trans he2)

theorem muNegFiveZeroThreeGraphHit_intersecting_no_common
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ (e f : Fin 72), e ≠ f →
      muNegFiveZeroThreeOwnersIntersect e f = true →
      ∀ k, muNegFiveZeroThreeGraphHit G c u v e k →
        muNegFiveZeroThreeGraphHit G c u v f k → False := by
  intro e f hef hinter k hek hfk
  obtain ⟨te, tk, hte, htk, hetk⟩ := hek
  obtain ⟨tf, tk', htf, htk', hftk⟩ := hfk
  have htkeq : tk' = tk := muNegFiveZeroThreeOwnerVertex_unique G c a b u v
    hfree hab huinj hvinj hurange hvrange k htk' htk
  rw [htkeq] at hftk
  have hetf : te ≠ tf := by
    intro h
    subst tf
    exact hef (muNegFiveZeroThreeOwnerVertex_inj G c a b u v hfree hreg
      hcard hsize hab huinj hvinj hurange hvrange hte htf)
  unfold muNegFiveZeroThreeOwnersIntersect at hinter
  rw [Bool.or_eq_true] at hinter
  obtain ⟨s, hse, hsf⟩ : ∃ s : Fin 16,
      muNegFiveZeroThreeOwnerContains e s = true ∧
        muNegFiveZeroThreeOwnerContains f s = true := by
    rcases hinter with h | h
    · refine ⟨⟨(muNegFiveZeroThreeOwnerAt e).1,
          (muNegFiveZeroThreeOwnerAt_bounds_ne e).1⟩, ?_, ?_⟩
      · unfold muNegFiveZeroThreeOwnerContains
        simp
      · simpa using h
    · refine ⟨⟨(muNegFiveZeroThreeOwnerAt e).2,
          (muNegFiveZeroThreeOwnerAt_bounds_ne e).2.1⟩, ?_, ?_⟩
      · unfold muNegFiveZeroThreeOwnerContains
        simp
      · simpa using h
  have htes := muNegFiveZeroThreeOwnerVertex_adj_of_contains G c u v hte hse
  have htfs := muNegFiveZeroThreeOwnerVertex_adj_of_contains G c u v htf hsf
  have heq : muNegFiveZeroThreeCodeVertex G c u v s = tk :=
    commonServer_unique G hfree hetf htes htfs hetk hftk
  exact htk.1 (heq ▸ muNegFiveZeroThreeCodeVertex_mem_supp G c u v s)

theorem muNegFiveZeroThreeGraphHit_no_two_common
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ (e f : Fin 72), e ≠ f → ∀ (k l : Fin 72), k ≠ l →
      muNegFiveZeroThreeGraphHit G c u v e k →
      muNegFiveZeroThreeGraphHit G c u v f k →
      muNegFiveZeroThreeGraphHit G c u v e l →
      muNegFiveZeroThreeGraphHit G c u v f l → False := by
  intro e f hef k l hkl hek hfk hel hfl
  obtain ⟨te, tk, hte, htk, hetk⟩ := hek
  obtain ⟨tf, tk', htf, htk', hftk⟩ := hfk
  obtain ⟨te', tl, hte', htl, hetl⟩ := hel
  obtain ⟨tf', tl', htf', htl', hftl⟩ := hfl
  have eqTk : tk' = tk := muNegFiveZeroThreeOwnerVertex_unique G c a b u v
    hfree hab huinj hvinj hurange hvrange k htk' htk
  have eqTe : te' = te := muNegFiveZeroThreeOwnerVertex_unique G c a b u v
    hfree hab huinj hvinj hurange hvrange e hte' hte
  have eqTf : tf' = tf := muNegFiveZeroThreeOwnerVertex_unique G c a b u v
    hfree hab huinj hvinj hurange hvrange f htf' htf
  have eqTl : tl' = tl := muNegFiveZeroThreeOwnerVertex_unique G c a b u v
    hfree hab huinj hvinj hurange hvrange l htl' htl
  rw [eqTk] at hftk
  rw [eqTe] at hetl
  rw [eqTf, eqTl] at hftl
  have hetf : te ≠ tf := by
    intro h
    apply hef
    apply muNegFiveZeroThreeOwnerVertex_inj G c a b u v hfree hreg
      hcard hsize hab huinj hvinj hurange hvrange hte
    rw [h]
    exact htf
  have hktl : tk = tl :=
    commonServer_unique G hfree hetf hetk hftk hetl hftl
  apply hkl
  apply muNegFiveZeroThreeOwnerVertex_inj G c a b u v hfree hreg
    hcard hsize hab huinj hvinj hurange hvrange htk
  rw [hktl]
  exact htl

theorem muNegFiveZeroThreeGraphHit_service_unique
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ (e : Fin 72) (s : Fin 16) (f g : Fin 72),
      muNegFiveZeroThreeGraphHit G c u v e f →
      muNegFiveZeroThreeOwnerContains f s = true →
      muNegFiveZeroThreeGraphHit G c u v e g →
      muNegFiveZeroThreeOwnerContains g s = true → f = g := by
  intro e s f g hef hfs heg hgs
  obtain ⟨te, tf, hte, htf, hetf⟩ := hef
  obtain ⟨te', tg, hte', htg, hetg⟩ := heg
  have eqTe : te' = te := muNegFiveZeroThreeOwnerVertex_unique G c a b u v
    hfree hab huinj hvinj hurange hvrange e hte' hte
  rw [eqTe] at hetg
  have htfs := muNegFiveZeroThreeOwnerVertex_adj_of_contains G c u v htf hfs
  have htgs := muNegFiveZeroThreeOwnerVertex_adj_of_contains G c u v htg hgs
  have hne : te ≠ muNegFiveZeroThreeCodeVertex G c u v s := by
    intro h
    apply hte.1
    rw [h]
    exact muNegFiveZeroThreeCodeVertex_mem_supp G c u v s
  have hfg : tf = tg := commonServer_unique G hfree hne
    hetf htfs.symm hetg htgs.symm
  rw [hfg] at htf
  exact muNegFiveZeroThreeOwnerVertex_inj G c a b u v hfree hreg hcard
    hsize hab huinj hvinj hurange hvrange htf htg

theorem muNegFiveZeroThreeGraphHit_service_exists
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (havailable : MuNegFiveZeroThreeOwnerAvailability G c u v)
    (hcover : MuNegFiveZeroThreeExteriorOwnerCoverage G c u v) :
    ∀ (e : Fin 72) (s : Fin 16),
      muNegFiveZeroThreeOwnerEnabled
        (muNegFiveZeroThreeGraphActive G c u v) e →
      muNegFiveZeroThreeOwnerTargetContains e s = true →
      ∃ f, muNegFiveZeroThreeGraphHit G c u v e f ∧
        muNegFiveZeroThreeOwnerContains f s = true := by
  intro e s henabled htarget
  obtain ⟨te, hte⟩ := havailable e henabled
  have hteComp :
      (secondOrderDefectGraph G).connectedComponentMk te ≠ c := by
    intro h
    apply hte.1
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c te).mpr h
  have hsComp : (secondOrderDefectGraph G).connectedComponentMk
      (muNegFiveZeroThreeCodeVertex G c u v s) = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c _).mp
      (muNegFiveZeroThreeCodeVertex_mem_supp G c u v s)
  obtain ⟨tf, ⟨hetf, htfs⟩, _⟩ :=
    binarySquare_regular_sizeTwoPart_exteriorOwner_unique_server
      G hfree (q := 8) (by omega) hreg hcard c hsize hteComp hsComp
  have heBounds := muNegFiveZeroThreeOwnerAt_bounds_ne e
  have htarget' := htarget
  unfold muNegFiveZeroThreeOwnerTargetContains at htarget'
  simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false] at htarget'
  have htfOutside : tf ∉ c.supp := by
    intro htfSupp
    have hmem := sizeTwoPart_server_mem_tile_of_internal G c hetf htfSupp
    have htile := sizeTwoPart_tile_eq_pair G hfree (q := 8) (by omega)
      hreg hcard c hsize
      (muNegFiveZeroThreeOwnerEndpoints_ne G c a b u v hab huinj hvinj
        hurange hvrange e)
      (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
      (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
      hte.2.1.symm hte.2.2.symm
    rw [htile] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · have hadj : G.Adj
          (muNegFiveZeroThreeCodeVertex G c u v
            (muNegFiveZeroThreeOwnerAt e).1)
          (muNegFiveZeroThreeCodeVertex G c u v s) := by
        change tf = muNegFiveZeroThreeCodeVertex G c u v
          (muNegFiveZeroThreeOwnerAt e).1 at h
        rw [← h]
        exact htfs
      have hcycle := (muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab
        huinj hvinj hurange hvrange hu hv _ heBounds.1 _ s.2).mp hadj
      exact Bool.false_ne_true (htarget'.1.symm.trans hcycle)
    · have hadj : G.Adj
          (muNegFiveZeroThreeCodeVertex G c u v
            (muNegFiveZeroThreeOwnerAt e).2)
          (muNegFiveZeroThreeCodeVertex G c u v s) := by
        change tf = muNegFiveZeroThreeCodeVertex G c u v
          (muNegFiveZeroThreeOwnerAt e).2 at h
        rw [← h]
        exact htfs
      have hcycle := (muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab
        huinj hvinj hurange hvrange hu hv _ heBounds.2.1 _ s.2).mp hadj
      exact Bool.false_ne_true (htarget'.2.symm.trans hcycle)
  obtain ⟨f, htf⟩ := hcover tf htfOutside
  have hfBounds := muNegFiveZeroThreeOwnerAt_bounds_ne f
  have hfTile := sizeTwoPart_tile_eq_pair G hfree (q := 8) (by omega)
    hreg hcard c hsize
    (muNegFiveZeroThreeOwnerEndpoints_ne G c a b u v hab huinj hvinj
      hurange hvrange f)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    htf.2.1.symm htf.2.2.symm
  have hsMem := sizeTwoPart_server_mem_tile_of_internal G c htfs
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v s)
  rw [hfTile] at hsMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsMem
  have hcontains : muNegFiveZeroThreeOwnerContains f s = true := by
    unfold muNegFiveZeroThreeOwnerContains
    rcases hsMem with h | h
    · have hs := muNegFiveZeroThreeCodeVertex_inj G c a b u v hab huinj
        hvinj hurange hvrange s s.2 _ hfBounds.1 h
      simp [hs]
    · have hs := muNegFiveZeroThreeCodeVertex_inj G c a b u v hab huinj
        hvinj hurange hvrange s s.2 _ hfBounds.2.1 h
      simp [hs]
  exact ⟨f, ⟨te, tf, hte, htf, hetf⟩, hcontains⟩

theorem muNegFiveZeroThreeGraphServiceSemantics
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (havailable : MuNegFiveZeroThreeOwnerAvailability G c u v)
    (hcover : MuNegFiveZeroThreeExteriorOwnerCoverage G c u v) :
    MuNegFiveZeroThreeOwnerServiceSemantics
      (muNegFiveZeroThreeGraphActive G c u v)
      (muNegFiveZeroThreeGraphHit G c u v) :=
  { service_exists := muNegFiveZeroThreeGraphHit_service_exists G c a b u v
      hfree hreg hcard hsize hab huinj hvinj hurange hvrange hu hv
      havailable hcover
    service_unique := muNegFiveZeroThreeGraphHit_service_unique G c a b u v
      hfree hreg hcard hsize hab huinj hvinj hurange hvrange
    internal_zero := muNegFiveZeroThreeGraphHit_internal_zero G c a b u v
      hfree hab huinj hvinj hurange hvrange hu hv
    intersecting_no_common :=
      muNegFiveZeroThreeGraphHit_intersecting_no_common G c a b u v
        hfree hreg hcard hsize hab huinj hvinj hurange hvrange
    no_two_common := muNegFiveZeroThreeGraphHit_no_two_common G c a b u v
      hfree hreg hcard hsize hab huinj hvinj hurange hvrange }

theorem muNegFiveZeroThreeGraphHit_irrefl
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ e, ¬ muNegFiveZeroThreeGraphHit G c u v e e := by
  intro e
  rintro ⟨z, w, hz, hw, hzw⟩
  have h := muNegFiveZeroThreeOwnerVertex_unique G c a b u v hfree hab
    huinj hvinj hurange hvrange e hz hw
  subst w
  exact G.loopless.irrefl z hzw

end Shores

instance (u v : ZMod 8 → c.supp) :
    DecidablePred (muNegFiveZeroThreeGraphActive G c u v) := by
  intro e
  exact Classical.propDecidable _

instance (u v : ZMod 8 → c.supp) :
    DecidableRel (muNegFiveZeroThreeGraphHit G c u v) := by
  intro e f
  exact Classical.propDecidable _

theorem muNegFiveZeroThreeGraphHit_symm
    (u v : ZMod 8 → c.supp) (e f : Fin 72) :
    muNegFiveZeroThreeGraphHit G c u v e f →
      muNegFiveZeroThreeGraphHit G c u v f e := by
  rintro ⟨z, w, he, hf, hzw⟩
  exact ⟨w, z, hf, he, hzw.symm⟩

theorem muNegFiveZeroThreeGraphHit_ends
    (u v : ZMod 8 → c.supp) (e f : Fin 72) :
    muNegFiveZeroThreeGraphHit G c u v e f →
      muNegFiveZeroThreeGraphActive G c u v e ∧
        muNegFiveZeroThreeGraphActive G c u v f := by
  rintro ⟨z, w, he, hf, _⟩
  exact ⟨⟨z, he⟩, ⟨w, hf⟩⟩

theorem muNegFiveZeroThreeGraphHit_witness
    (u v : ZMod 8 → c.supp) {e f : Fin 72}
    (h : muNegFiveZeroThreeGraphHit G c u v e f) :
    ∃ z w : V, z ∉ c.supp ∧ w ∉ c.supp ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).1 z ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).2 z ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v f).1 w ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v f).2 w ∧
      G.Adj z w := by
  obtain ⟨z, w, he, hf, hzw⟩ := h
  exact ⟨z, w, he.1, hf.1, he.2.1, he.2.2,
    hf.2.1, hf.2.2, hzw⟩

end

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeGraphHit_symm
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_ends
#print axioms Erdos85.muNegFiveZeroThreeCodeVertex_inj
#print axioms Erdos85.muNegFiveZeroThreeOwnerVertex_unique
#print axioms Erdos85.muNegFiveZeroThreeOwnerVertex_inj
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_intersecting_no_common
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_no_two_common
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_service_unique
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_service_exists
#print axioms Erdos85.muNegFiveZeroThreeGraphServiceSemantics
#print axioms Erdos85.muNegFiveZeroThreeOwnerCompatible_of_graphHit
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_internal_zero
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_irrefl
