import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyOwnerServiceBridge
import Proofs.Erdos85MuNegFiveZeroThreeGraphRealization
import Proofs.Erdos85MuNegFiveOneTwoShoreGeometry

/-!
# Graph realization of the corrected cross-only h512 owner universe

The corrected h512 certificate numbers the 64 cross pairs directly.  The
older h503 graph development numbers the same pairs inside its 72-element
table, interleaved with eight fixed same-shore pairs.  This file gives the
checked embedding between those tables and reuses the established graph
owner predicates through it.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Insert the four first-shore fixed h503 owners that precede the cross
table.  In rows `0..3` one new fixed owner has appeared; rows `4..7` retain
the accumulated offset four. -/
def muNegFiveOneTwoCrossOnlyToZeroThree (e : Fin 64) : Fin 72 :=
  ⟨e.val + min (e.val / 8 + 1) 4, by omega⟩

theorem muNegFiveOneTwoCrossOnlyToZeroThree_val (e : Fin 64) :
    (muNegFiveOneTwoCrossOnlyToZeroThree e).val =
      e.val + min (e.val / 8 + 1) 4 := rfl

theorem muNegFiveOneTwoCrossOnlyToZeroThree_injective :
    Function.Injective muNegFiveOneTwoCrossOnlyToZeroThree := by
  intro e f h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [muNegFiveOneTwoCrossOnlyToZeroThree_val] at hval
  revert e f
  native_decide

/-- The embedded old-table entry names exactly the corrected cross-only
entry, including its orientation. -/
theorem muNegFiveOneTwoCrossOnly_ownerAt_embed (e : Fin 64) :
    muNegFiveZeroThreeOwnerAt (muNegFiveOneTwoCrossOnlyToZeroThree e) =
      muNegFiveOneTwoCrossOnlyOwnerAt e := by
  revert e
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownerAt_bounds (e : Fin 64) :
    (muNegFiveOneTwoCrossOnlyOwnerAt e).1 < 8 ∧
      8 ≤ (muNegFiveOneTwoCrossOnlyOwnerAt e).2 ∧
      (muNegFiveOneTwoCrossOnlyOwnerAt e).2 < 16 := by
  revert e
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownerAt_injective :
    Function.Injective (fun e : Fin 64 ↦
      muNegFiveOneTwoCrossOnlyOwnerAt e) := by
  intro e f h
  revert e f
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownerContains_embed
    (e : Fin 64) (x : Fin 16) :
    muNegFiveZeroThreeOwnerContains
        (muNegFiveOneTwoCrossOnlyToZeroThree e) x =
      muNegFiveOneTwoCrossOnlyOwnerContains e x := by
  revert e x
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownerTargetContains_embed
    (e : Fin 64) (x : Fin 16) :
    muNegFiveZeroThreeOwnerTargetContains
        (muNegFiveOneTwoCrossOnlyToZeroThree e) x =
      muNegFiveOneTwoCrossOnlyOwnerTargetContains e x := by
  revert e x
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownerCompatible_embed
    (e f : Fin 64) :
    muNegFiveZeroThreeOwnerCompatible
        (muNegFiveOneTwoCrossOnlyToZeroThree e)
        (muNegFiveOneTwoCrossOnlyToZeroThree f) =
      muNegFiveOneTwoCrossOnlyOwnerCompatible e f := by
  revert e f
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownersIntersect_embed
    (e f : Fin 64) :
    muNegFiveZeroThreeOwnersIntersect
        (muNegFiveOneTwoCrossOnlyToZeroThree e)
        (muNegFiveOneTwoCrossOnlyToZeroThree f) =
      muNegFiveOneTwoCrossOnlyOwnersIntersect e f := by
  revert e f
  native_decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- Corrected h512 owners are the old graph owners at embedded cross
indices. -/
def MuNegFiveOneTwoCrossOnlyOwnerVertex
    (u v : ZMod 8 → c.supp) (e : Fin 64) (z : V) : Prop :=
  MuNegFiveZeroThreeOwnerVertex G c u v
    (muNegFiveOneTwoCrossOnlyToZeroThree e) z

def muNegFiveOneTwoCrossOnlyGraphActive
    (u v : ZMod 8 → c.supp) (e : Fin 64) : Prop :=
  ∃ z : V, MuNegFiveOneTwoCrossOnlyOwnerVertex G c u v e z

def muNegFiveOneTwoCrossOnlyGraphHit
    (u v : ZMod 8 → c.supp) (e f : Fin 64) : Prop :=
  ∃ z w : V,
    MuNegFiveOneTwoCrossOnlyOwnerVertex G c u v e z ∧
    MuNegFiveOneTwoCrossOnlyOwnerVertex G c u v f w ∧ G.Adj z w

def MuNegFiveOneTwoCrossOnlyExteriorOwnerCoverage
    (u v : ZMod 8 → c.supp) : Prop :=
  ∀ z : V, z ∉ c.supp →
    ∃ e : Fin 64, MuNegFiveOneTwoCrossOnlyOwnerVertex G c u v e z

theorem muNegFiveOneTwoCrossOnly_activeVariable_some (e : Fin 64) :
    muNegFiveOneTwoCrossOnlyActiveVariable? e = some (e.val + 1) := by
  revert e
  native_decide

instance (u v : ZMod 8 → c.supp) :
    DecidablePred (muNegFiveOneTwoCrossOnlyGraphActive G c u v) := by
  intro e
  exact Classical.propDecidable _

instance (u v : ZMod 8 → c.supp) :
    DecidableRel (muNegFiveOneTwoCrossOnlyGraphHit G c u v) := by
  intro e f
  exact Classical.propDecidable _

theorem muNegFiveOneTwoCrossOnlyGraphActive_eq_old
    (u v : ZMod 8 → c.supp) (e : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphActive G c u v e ↔
      muNegFiveZeroThreeGraphActive G c u v
        (muNegFiveOneTwoCrossOnlyToZeroThree e) := Iff.rfl

theorem muNegFiveOneTwoCrossOnlyGraphHit_eq_old
    (u v : ZMod 8 → c.supp) (e f : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphHit G c u v e f ↔
      muNegFiveZeroThreeGraphHit G c u v
        (muNegFiveOneTwoCrossOnlyToZeroThree e)
        (muNegFiveOneTwoCrossOnlyToZeroThree f) := Iff.rfl

theorem muNegFiveOneTwoCrossOnlyGraphHit_symm
    (u v : ZMod 8 → c.supp) (e f : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphHit G c u v e f →
      muNegFiveOneTwoCrossOnlyGraphHit G c u v f e := by
  rintro ⟨z, w, he, hf, hzw⟩
  exact ⟨w, z, hf, he, hzw.symm⟩

theorem muNegFiveOneTwoCrossOnlyGraphHit_ends
    (u v : ZMod 8 → c.supp) (e f : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphHit G c u v e f →
      muNegFiveOneTwoCrossOnlyGraphActive G c u v e ∧
        muNegFiveOneTwoCrossOnlyGraphActive G c u v f := by
  rintro ⟨z, w, he, hf, _⟩
  exact ⟨⟨z, he⟩, ⟨w, hf⟩⟩

section Shores

variable [DecidableEq (G.induce c.supp).ConnectedComponent]
  (a b : (G.induce c.supp).ConnectedComponent)
  (u v : ZMod 8 → c.supp)

theorem muNegFiveOneTwoCrossOnlyGraphHit_irrefl
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ e, ¬ muNegFiveOneTwoCrossOnlyGraphHit G c u v e e := by
  intro e
  exact muNegFiveZeroThreeGraphHit_irrefl G c a b u v hfree hab
    huinj hvinj hurange hvrange (muNegFiveOneTwoCrossOnlyToZeroThree e)

theorem muNegFiveOneTwoCrossOnlyOwnerCompatible_of_graphHit
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {e f : Fin 64}
    (hef : muNegFiveOneTwoCrossOnlyGraphHit G c u v e f) :
    muNegFiveOneTwoCrossOnlyOwnerCompatible e f = true := by
  rw [← muNegFiveOneTwoCrossOnly_ownerCompatible_embed]
  exact muNegFiveZeroThreeOwnerCompatible_of_graphHit G c a b u v
    hfree hab huinj hvinj hurange hvrange hu hv hef

theorem muNegFiveOneTwoCrossOnlyGraphHit_service_unique
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ (e : Fin 64) (s : Fin 16) (f g : Fin 64),
      muNegFiveOneTwoCrossOnlyGraphHit G c u v e f →
      muNegFiveOneTwoCrossOnlyOwnerContains f s = true →
      muNegFiveOneTwoCrossOnlyGraphHit G c u v e g →
      muNegFiveOneTwoCrossOnlyOwnerContains g s = true → f = g := by
  intro e s f g hef hfs heg hgs
  apply muNegFiveOneTwoCrossOnlyToZeroThree_injective
  apply muNegFiveZeroThreeGraphHit_service_unique G c a b u v hfree hreg
    hcard hsize hab huinj hvinj hurange hvrange
  · exact hef
  · simpa [muNegFiveOneTwoCrossOnly_ownerContains_embed] using hfs
  · exact heg
  · simpa [muNegFiveOneTwoCrossOnly_ownerContains_embed] using hgs

theorem muNegFiveOneTwoCrossOnlyGraphHit_internal_zero
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ (e : Fin 64) (s : Fin 16) (f : Fin 64),
      muNegFiveOneTwoCrossOnlyOwnerTargetContains e s = false →
      muNegFiveOneTwoCrossOnlyOwnerContains f s = true →
      ¬ muNegFiveOneTwoCrossOnlyGraphHit G c u v e f := by
  intro e s f ht hc
  apply muNegFiveZeroThreeGraphHit_internal_zero G c a b u v hfree hab
    huinj hvinj hurange hvrange hu hv
  · simpa [muNegFiveOneTwoCrossOnly_ownerTargetContains_embed] using ht
  · simpa [muNegFiveOneTwoCrossOnly_ownerContains_embed] using hc

theorem muNegFiveOneTwoCrossOnlyGraphHit_intersecting_no_common
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ (e f : Fin 64), e ≠ f →
      muNegFiveOneTwoCrossOnlyOwnersIntersect e f = true →
      ∀ k, muNegFiveOneTwoCrossOnlyGraphHit G c u v e k →
        muNegFiveOneTwoCrossOnlyGraphHit G c u v f k → False := by
  intro e f hef hinter k hek hfk
  apply muNegFiveZeroThreeGraphHit_intersecting_no_common G c a b u v
    hfree hreg hcard hsize hab huinj hvinj hurange hvrange
      (muNegFiveOneTwoCrossOnlyToZeroThree e)
      (muNegFiveOneTwoCrossOnlyToZeroThree f)
  · exact fun h ↦ hef (muNegFiveOneTwoCrossOnlyToZeroThree_injective h)
  · simpa [muNegFiveOneTwoCrossOnly_ownersIntersect_embed] using hinter
  · exact hek
  · exact hfk

theorem muNegFiveOneTwoCrossOnlyGraphHit_no_two_common
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ (e f : Fin 64), e ≠ f → ∀ (k l : Fin 64), k ≠ l →
      muNegFiveOneTwoCrossOnlyGraphHit G c u v e k →
      muNegFiveOneTwoCrossOnlyGraphHit G c u v f k →
      muNegFiveOneTwoCrossOnlyGraphHit G c u v e l →
      muNegFiveOneTwoCrossOnlyGraphHit G c u v f l → False := by
  intro e f hef k l hkl hek hfk hel hfl
  apply muNegFiveZeroThreeGraphHit_no_two_common G c a b u v hfree hreg
    hcard hsize hab huinj hvinj hurange hvrange
      (muNegFiveOneTwoCrossOnlyToZeroThree e)
      (muNegFiveOneTwoCrossOnlyToZeroThree f)
  · exact fun h ↦ hef (muNegFiveOneTwoCrossOnlyToZeroThree_injective h)
  · exact fun h ↦ hkl (muNegFiveOneTwoCrossOnlyToZeroThree_injective h)
  · exact hek
  · exact hfk
  · exact hel
  · exact hfl

theorem muNegFiveOneTwoCrossOnlyGraphHit_service_exists
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
    (hcover : MuNegFiveOneTwoCrossOnlyExteriorOwnerCoverage G c u v) :
    ∀ (e : Fin 64) (s : Fin 16),
      muNegFiveOneTwoCrossOnlyOwnerEnabled
        (muNegFiveOneTwoCrossOnlyGraphActive G c u v) e →
      muNegFiveOneTwoCrossOnlyOwnerTargetContains e s = true →
      ∃ f, muNegFiveOneTwoCrossOnlyGraphHit G c u v e f ∧
        muNegFiveOneTwoCrossOnlyOwnerContains f s = true := by
  intro e s henabled htarget
  have haid := muNegFiveOneTwoCrossOnly_activeVariable_some e
  have heactive : muNegFiveOneTwoCrossOnlyGraphActive G c u v e := by
    unfold muNegFiveOneTwoCrossOnlyOwnerEnabled at henabled
    rw [haid] at henabled
    exact henabled
  obtain ⟨te, hte⟩ := heactive
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
  let ee := muNegFiveOneTwoCrossOnlyToZeroThree e
  have heBounds := muNegFiveZeroThreeOwnerAt_bounds_ne ee
  have htargetOld : muNegFiveZeroThreeOwnerTargetContains ee s = true := by
    rw [muNegFiveOneTwoCrossOnly_ownerTargetContains_embed]
    exact htarget
  have htarget' := htargetOld
  unfold muNegFiveZeroThreeOwnerTargetContains at htarget'
  simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false] at htarget'
  have htfOutside : tf ∉ c.supp := by
    intro htfSupp
    have hmem := sizeTwoPart_server_mem_tile_of_internal G c hetf htfSupp
    have htile := sizeTwoPart_tile_eq_pair G hfree (q := 8) (by omega)
      hreg hcard c hsize
      (muNegFiveZeroThreeOwnerEndpoints_ne G c a b u v hab huinj hvinj
        hurange hvrange ee)
      (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
      (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
      hte.2.1.symm hte.2.2.symm
    rw [htile] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · have hadj : G.Adj
          (muNegFiveZeroThreeCodeVertex G c u v
            (muNegFiveZeroThreeOwnerAt ee).1)
          (muNegFiveZeroThreeCodeVertex G c u v s) := by
        change tf = muNegFiveZeroThreeCodeVertex G c u v
          (muNegFiveZeroThreeOwnerAt ee).1 at h
        rw [← h]
        exact htfs
      have hcycle := (muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab
        huinj hvinj hurange hvrange hu hv _ heBounds.1 _ s.2).mp hadj
      exact Bool.false_ne_true (htarget'.1.symm.trans hcycle)
    · have hadj : G.Adj
          (muNegFiveZeroThreeCodeVertex G c u v
            (muNegFiveZeroThreeOwnerAt ee).2)
          (muNegFiveZeroThreeCodeVertex G c u v s) := by
        change tf = muNegFiveZeroThreeCodeVertex G c u v
          (muNegFiveZeroThreeOwnerAt ee).2 at h
        rw [← h]
        exact htfs
      have hcycle := (muNegFiveZeroThreeCodeVertex_adj_iff G c a b u v hab
        huinj hvinj hurange hvrange hu hv _ heBounds.2.1 _ s.2).mp hadj
      exact Bool.false_ne_true (htarget'.2.symm.trans hcycle)
  obtain ⟨f, htf⟩ := hcover tf htfOutside
  let ff := muNegFiveOneTwoCrossOnlyToZeroThree f
  have hfBounds := muNegFiveZeroThreeOwnerAt_bounds_ne ff
  have hfTile := sizeTwoPart_tile_eq_pair G hfree (q := 8) (by omega)
    hreg hcard c hsize
    (muNegFiveZeroThreeOwnerEndpoints_ne G c a b u v hab huinj hvinj
      hurange hvrange ff)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v _)
    htf.2.1.symm htf.2.2.symm
  have hsMem := sizeTwoPart_server_mem_tile_of_internal G c htfs
    (muNegFiveZeroThreeCodeVertex_mem_supp G c u v s)
  rw [hfTile] at hsMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsMem
  have hcontainsOld : muNegFiveZeroThreeOwnerContains ff s = true := by
    unfold muNegFiveZeroThreeOwnerContains
    rcases hsMem with h | h
    · have hs := muNegFiveZeroThreeCodeVertex_inj G c a b u v hab huinj
        hvinj hurange hvrange s s.2 _ hfBounds.1 h
      simp [hs]
    · have hs := muNegFiveZeroThreeCodeVertex_inj G c a b u v hab huinj
        hvinj hurange hvrange s s.2 _ hfBounds.2.1 h
      simp [hs]
  refine ⟨f, ⟨te, tf, hte, htf, hetf⟩, ?_⟩
  simpa [ff, muNegFiveOneTwoCrossOnly_ownerContains_embed] using hcontainsOld

theorem muNegFiveOneTwoCrossOnlyGraphServiceSemantics
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
    (hcover : MuNegFiveOneTwoCrossOnlyExteriorOwnerCoverage G c u v) :
    MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics
      (muNegFiveOneTwoCrossOnlyGraphActive G c u v)
      (muNegFiveOneTwoCrossOnlyGraphHit G c u v) :=
  { service_exists :=
      muNegFiveOneTwoCrossOnlyGraphHit_service_exists G c a b u v hfree hreg
        hcard hsize hab huinj hvinj hurange hvrange hu hv hcover
    service_unique :=
      muNegFiveOneTwoCrossOnlyGraphHit_service_unique G c a b u v hfree hreg
        hcard hsize hab huinj hvinj hurange hvrange
    internal_zero :=
      muNegFiveOneTwoCrossOnlyGraphHit_internal_zero G c a b u v hfree hab
        huinj hvinj hurange hvrange hu hv
    intersecting_no_common :=
      muNegFiveOneTwoCrossOnlyGraphHit_intersecting_no_common G c a b u v
        hfree hreg hcard hsize hab huinj hvinj hurange hvrange
    no_two_common :=
      muNegFiveOneTwoCrossOnlyGraphHit_no_two_common G c a b u v hfree hreg
        hcard hsize hab huinj hvinj hurange hvrange }

end Shores

end

end Erdos85

#print axioms Erdos85.muNegFiveOneTwoCrossOnly_ownerAt_embed
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyToZeroThree_injective
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyGraphHit_symm
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyOwnerCompatible_of_graphHit
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyGraphHit_no_two_common
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyGraphServiceSemantics
