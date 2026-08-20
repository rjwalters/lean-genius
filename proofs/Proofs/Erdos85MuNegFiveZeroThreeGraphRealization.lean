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
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_irrefl
