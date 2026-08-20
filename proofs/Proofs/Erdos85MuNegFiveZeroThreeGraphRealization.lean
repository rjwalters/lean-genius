import Proofs.Erdos85MuNegFiveZeroThreeOwnerServiceBridge
import Proofs.Erdos85SizeTwoMuNegFiveAlignedShoreSwitch
import Proofs.Erdos85SizeTwoOwnerVertexDictionary
import Proofs.Erdos85MuNegOneOneFourTableCompleteness

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

def muNegFiveZeroThreeCodeSub
    (u v : ZMod 8 → c.supp) (x : Nat) : c.supp :=
  ⟨muNegFiveZeroThreeCodeVertex G c u v x,
    muNegFiveZeroThreeCodeVertex_mem_supp G c u v x⟩

theorem muNegFiveZeroThreeCodeSub_eq_muNegOneCodeSub
    (u v : ZMod 8 → c.supp) (x : Nat) :
    muNegFiveZeroThreeCodeSub G c u v x = muNegOneCodeSub G c u v x := by
  unfold muNegFiveZeroThreeCodeSub muNegFiveZeroThreeCodeVertex
    muNegOneCodeSub
  split <;> rfl

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

def MuNegFiveZeroThreeOwnerPairComplete
    (u v : ZMod 8 → c.supp) : Prop :=
  ∀ {x y : c.supp}, (exteriorPairGraph G c.supp).Adj x y →
    ∃ e : Fin 72,
      ({(muNegFiveZeroThreeOwnerEndpoints G c u v e).1,
        (muNegFiveZeroThreeOwnerEndpoints G c u v e).2} : Finset V) =
        {x.1, y.1}

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

theorem muNegFiveZeroThreeCodeSub_surjective
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (x : c.supp) :
    ∃ code : Nat, code < 16 ∧ muNegFiveZeroThreeCodeSub G c u v code = x := by
  obtain ⟨code, hcode, heq⟩ := muNegOneCodeSub_surjective G c hsize a b hab
    u v huinj hvinj hurange hvrange x
  exact ⟨code, hcode,
    muNegFiveZeroThreeCodeSub_eq_muNegOneCodeSub G c u v code |>.trans heq⟩

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

theorem muNegFiveZeroThreeCandidatePair_lookup :
    ∀ x, x < 16 → ∀ y, y < 16 →
      (muNegFiveZeroThreeCandidatePair x y = true ∨
        muNegFiveZeroThreeCandidatePair y x = true) →
      ∃ e : Fin 72,
        muNegFiveZeroThreeOwnerAt e = (x, y) ∨
          muNegFiveZeroThreeOwnerAt e = (y, x) := by
  native_decide

theorem muNegFiveZeroThreeCandidatePair_left_of_antipode :
    ∀ x : Nat, x < 8 → ∀ y : Nat, y < 8 →
      ((y : ZMod 8) - (x : ZMod 8) = 4) →
      muNegFiveZeroThreeCandidatePair x y = true ∨
        muNegFiveZeroThreeCandidatePair y x = true := by
  native_decide

theorem muNegFiveZeroThreeCandidatePair_right_of_antipode :
    ∀ x, 8 ≤ x → x < 16 → ∀ y, 8 ≤ y → y < 16 →
      (((y - 8 : Nat) : ZMod 8) - ((x - 8 : Nat) : ZMod 8) = 4) →
      muNegFiveZeroThreeCandidatePair x y = true ∨
        muNegFiveZeroThreeCandidatePair y x = true := by
  native_decide

theorem muNegFiveZeroThreeCandidatePair_cross :
    ∀ x, x < 8 → ∀ y, 8 ≤ y → y < 16 →
      muNegFiveZeroThreeCandidatePair x y = true := by
  native_decide

theorem zmodEight_not_oddOffset_imp_evenOffset :
    ∀ d : ZMod 8,
      ¬ (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7) → ZModEightEvenOffset d := by
  decide

theorem zmodEight_oddOffset_card_four :
    ∀ i : ZMod 8,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7).card = 4 := by
  decide

theorem MuNegFiveExplicitRowParameterLedger.zeroThree_internal_iff_oddOffset
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 3) :
    ∀ i j : ZMod 8, N i j = 1 ↔
      j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7 := by
  intro i
  let A := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N i j = 1
  let O := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7
  have hAcard : A.card = 4 := by
    simpa [A] using L.internal_row i
  have hOcard : O.card = 4 := by
    simpa [O] using zmodEight_oddOffset_card_four i
  have hsub : A ⊆ O := by
    intro j hj
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnotOdd
    have heven := zmodEight_not_oddOffset_imp_evenOffset (j - i) hnotOdd
    have hsignEq := (zmodEight_alternating_sign_eq_iff_evenOffset
      f L.f_sign L.f_flip i j).mpr heven
    have hsameMem : j ∈ ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f i ∧ N i j = 1) := by
      simp [hsignEq, hj]
    have hzero : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f i ∧ N i j = 1) = ∅ :=
      Finset.card_eq_zero.mp (by simpa using L.internal_same i)
    rw [hzero] at hsameMem
    exact Finset.notMem_empty j hsameMem
  have hAO : A = O := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro j
  have := Finset.ext_iff.mp hAO j
  simpa [A, O] using this

theorem MuNegFiveExplicitRowParameterLedger.zeroThree_cycleEntriesOne
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 3) :
    C8CycleEntriesOne N := by
  constructor
  · exact (L.zeroThree_internal_iff_oddOffset 0 (-1)).mpr (by decide)
  · exact (L.zeroThree_internal_iff_oddOffset 0 1).mpr (by decide)

theorem muNegFiveZeroThreeFixedOwner_shape :
    ∀ e : Fin 72, muNegFiveZeroThreeActiveVariable? e = none →
      (((muNegFiveZeroThreeOwnerAt e).1 < 8 ∧
          (muNegFiveZeroThreeOwnerAt e).2 < 8 ∧
          ((muNegFiveZeroThreeOwnerAt e).2 : ZMod 8) -
            ((muNegFiveZeroThreeOwnerAt e).1 : ZMod 8) = 4) ∨
        (8 ≤ (muNegFiveZeroThreeOwnerAt e).1 ∧
          (muNegFiveZeroThreeOwnerAt e).1 < 16 ∧
          8 ≤ (muNegFiveZeroThreeOwnerAt e).2 ∧
          (muNegFiveZeroThreeOwnerAt e).2 < 16 ∧
          (((muNegFiveZeroThreeOwnerAt e).2 - 8 : Nat) : ZMod 8) -
            (((muNegFiveZeroThreeOwnerAt e).1 - 8 : Nat) : ZMod 8) = 4)) := by
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

theorem muNegFiveZeroThreeOwnerAvailability_of_fixedExterior
    (hfree : ¬ containsC4 V G)
    (hfixed : ∀ e : Fin 72,
      muNegFiveZeroThreeActiveVariable? e = none →
      (exteriorPairGraph G c.supp).Adj
        (muNegFiveZeroThreeCodeSub G c u v
          (muNegFiveZeroThreeOwnerAt e).1)
        (muNegFiveZeroThreeCodeSub G c u v
          (muNegFiveZeroThreeOwnerAt e).2)) :
    MuNegFiveZeroThreeOwnerAvailability G c u v := by
  intro e henabled
  unfold muNegFiveZeroThreeOwnerEnabled at henabled
  split at henabled
  · exact henabled
  · next heq =>
    obtain ⟨z, hzout, hz1, hz2, _⟩ := exteriorPairGraph_ownerVertex
      G hfree c.supp (hfixed e heq)
    exact ⟨z, hzout, hz1, hz2⟩

theorem muNegFiveZeroThreeExteriorOwnerCoverage_of_pairComplete
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (hcomplete : MuNegFiveZeroThreeOwnerPairComplete G c u v) :
    MuNegFiveZeroThreeExteriorOwnerCoverage G c u v := by
  intro z hzout
  have htileCard := sizeTwoPart_tile_card_two G hfree (q := 8) (by omega)
    hreg hcard c hsize z
  obtain ⟨x, y, hxy, htile⟩ := Finset.card_eq_two.mp htileCard
  have hxmem : x ∈ componentNeighborFinset G (secondOrderDefectGraph G) c z := by
    rw [htile]
    exact Finset.mem_insert_self _ _
  have hymem : y ∈ componentNeighborFinset G (secondOrderDefectGraph G) c z := by
    rw [htile]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset] at hxmem hymem
  have hxsupp : x ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mpr hxmem.2
  have hysupp : y ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mpr hymem.2
  let xs : c.supp := ⟨x, hxsupp⟩
  let ys : c.supp := ⟨y, hysupp⟩
  have hR : (exteriorPairGraph G c.supp).Adj xs ys := by
    refine ⟨?_, z, hzout, ?_, ?_⟩
    · intro h
      exact hxy (congrArg Subtype.val h)
    · exact hxmem.1.symm
    · exact hymem.1.symm
  obtain ⟨e, hePair⟩ := hcomplete hR
  refine ⟨e, hzout, ?_, ?_⟩
  · have hmem : (muNegFiveZeroThreeOwnerEndpoints G c u v e).1 ∈
        ({x, y} : Finset V) := by
      rw [← hePair]
      exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · rw [h]
      exact hxmem.1.symm
    · rw [h]
      exact hymem.1.symm
  · have hmem : (muNegFiveZeroThreeOwnerEndpoints G c u v e).2 ∈
        ({x, y} : Finset V) := by
      rw [← hePair]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · rw [h]
      exact hxmem.1.symm
    · rw [h]
      exact hymem.1.symm

theorem muNegFiveZeroThreeOwnerPairComplete_of_candidateSupport
    (hsize : c.supp.ncard = 8 * 2)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hsupport : ∀ x, x < 16 → ∀ y, y < 16 →
      (exteriorPairGraph G c.supp).Adj
        (muNegFiveZeroThreeCodeSub G c u v x)
        (muNegFiveZeroThreeCodeSub G c u v y) →
      muNegFiveZeroThreeCandidatePair x y = true ∨
        muNegFiveZeroThreeCandidatePair y x = true) :
    MuNegFiveZeroThreeOwnerPairComplete G c u v := by
  intro x y hR
  obtain ⟨xc, hxc, hxeq⟩ := muNegFiveZeroThreeCodeSub_surjective G c a b
    u v hsize hab huinj hvinj hurange hvrange x
  obtain ⟨yc, hyc, hyeq⟩ := muNegFiveZeroThreeCodeSub_surjective G c a b
    u v hsize hab huinj hvinj hurange hvrange y
  have hRcode : (exteriorPairGraph G c.supp).Adj
      (muNegFiveZeroThreeCodeSub G c u v xc)
      (muNegFiveZeroThreeCodeSub G c u v yc) := by
    rw [hxeq, hyeq]
    exact hR
  have hxval := congrArg Subtype.val hxeq
  have hyval := congrArg Subtype.val hyeq
  change muNegFiveZeroThreeCodeVertex G c u v xc = x.1 at hxval
  change muNegFiveZeroThreeCodeVertex G c u v yc = y.1 at hyval
  obtain ⟨e, he | he⟩ := muNegFiveZeroThreeCandidatePair_lookup
    xc hxc yc hyc (hsupport xc hxc yc hyc hRcode)
  · refine ⟨e, ?_⟩
    simp only [muNegFiveZeroThreeOwnerEndpoints, he, hxval, hyval]
  · refine ⟨e, ?_⟩
    simpa only [muNegFiveZeroThreeOwnerEndpoints, he, hxval, hyval] using
      (Finset.pair_comm y.1 x.1)

theorem muNegFiveZeroThreeCandidateSupport_of_antipode
    (hleft : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (u i) (u j) → j - i = 4)
    (hright : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (v i) (v j) → j - i = 4) :
    ∀ x, x < 16 → ∀ y, y < 16 →
      (exteriorPairGraph G c.supp).Adj
        (muNegFiveZeroThreeCodeSub G c u v x)
        (muNegFiveZeroThreeCodeSub G c u v y) →
      muNegFiveZeroThreeCandidatePair x y = true ∨
        muNegFiveZeroThreeCandidatePair y x = true := by
  intro x hx y hy hR
  by_cases hx8 : x < 8 <;> by_cases hy8 : y < 8
  · apply muNegFiveZeroThreeCandidatePair_left_of_antipode x hx8 y hy8
    apply hleft
    simpa only [muNegFiveZeroThreeCodeSub, muNegFiveZeroThreeCodeVertex,
      if_pos hx8, if_pos hy8] using hR
  · exact Or.inl (muNegFiveZeroThreeCandidatePair_cross x hx8 y (by omega) hy)
  · exact Or.inr (muNegFiveZeroThreeCandidatePair_cross y hy8 x (by omega) hx)
  · apply muNegFiveZeroThreeCandidatePair_right_of_antipode x (by omega) hx y
      (by omega) hy
    apply hright
    simpa only [muNegFiveZeroThreeCodeSub, muNegFiveZeroThreeCodeVertex,
      if_neg hx8, if_neg hy8] using hR

theorem exteriorPairGraph_cycle_iff_antipode_of_odd_defect
    (hfree : ¬ containsC4 V G)
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    (hD : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (w i) (w j) ↔
        j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7) :
    ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (w i) (w j) ↔ j - i = 4 := by
  let H := G.induce c.supp
  intro i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have hcommon (hij : i ≠ j) :
      (∃ z, H.Adj (w i) z ∧ H.Adj (w j) z) ↔
        j - i = 2 ∨ j - i = 6 :=
    zmodEight_cycle_internalCommon_iff_offset_two_six H w hwinj hw i j hij
  constructor
  · rintro ⟨hij, hnotD, hnoCommon⟩
    have hij' : i ≠ j := fun h => hij (congrArg w h)
    have hnotOdd : ¬ (j - i = 1 ∨ j - i = 3 ∨
        j - i = 5 ∨ j - i = 7) := fun h => hnotD ((hD i j).mpr h)
    have hnotCommon : ¬ (j - i = 2 ∨ j - i = 6) := by
      intro h
      apply hnoCommon
      simpa [H] using (hcommon hij').mpr h
    have hnotZero : j - i ≠ 0 := by
      intro h
      exact hij' (sub_eq_zero.mp h).symm
    generalize j - i = d at hnotOdd hnotCommon hnotZero ⊢
    revert d
    decide
  · intro hfour
    have hij' : i ≠ j := by
      intro h
      subst j
      have : ¬ ((0 : ZMod 8) = 4) := by decide
      exact this (by simpa using hfour)
    refine ⟨hwinj.ne hij', ?_, ?_⟩
    · intro hDij
      have hodd := (hD i j).mp (by simpa using hDij)
      rw [hfour] at hodd
      revert hodd
      decide
    · intro hex
      have hc := (hcommon hij').mp (by simpa [H] using hex)
      rw [hfour] at hc
      revert hc
      decide

theorem muNegFiveZeroThreeOwnerGeometry_of_rowLedgers
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
    {M₁ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {fu gu fv gv : ZMod 8 → ℤ}
    (Lu : MuNegFiveExplicitRowParameterLedger
      (fun i j ↦ (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ)
        (u i) (u j)) M₁ fu gu 0 3)
    (Lv : MuNegFiveExplicitRowParameterLedger
      (fun i j ↦ (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ)
        (v i) (v j)) M₂ fv gv 0 3) :
    MuNegFiveZeroThreeOwnerAvailability G c u v ∧
      MuNegFiveZeroThreeExteriorOwnerCoverage G c u v := by
  have hDu : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7 := by
    intro i j
    simpa [SimpleGraph.adjMatrix_apply] using
      (Lu.zeroThree_internal_iff_oddOffset i j)
  have hDv : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7 := by
    intro i j
    simpa [SimpleGraph.adjMatrix_apply] using
      (Lv.zeroThree_internal_iff_oddOffset i j)
  have hRu := exteriorPairGraph_cycle_iff_antipode_of_odd_defect
    G c hfree u huinj hu hDu
  have hRv := exteriorPairGraph_cycle_iff_antipode_of_odd_defect
    G c hfree v hvinj hv hDv
  have hfixed : ∀ e : Fin 72,
      muNegFiveZeroThreeActiveVariable? e = none →
      (exteriorPairGraph G c.supp).Adj
        (muNegFiveZeroThreeCodeSub G c u v
          (muNegFiveZeroThreeOwnerAt e).1)
        (muNegFiveZeroThreeCodeSub G c u v
          (muNegFiveZeroThreeOwnerAt e).2) := by
    intro e he
    rcases muNegFiveZeroThreeFixedOwner_shape e he with hleft | hright
    · simpa only [muNegFiveZeroThreeCodeSub, muNegFiveZeroThreeCodeVertex,
        if_pos hleft.1, if_pos hleft.2.1] using
        (hRu _ _).mpr hleft.2.2
    · simpa only [muNegFiveZeroThreeCodeSub, muNegFiveZeroThreeCodeVertex,
        if_neg (by omega : ¬ (muNegFiveZeroThreeOwnerAt e).1 < 8),
        if_neg (by omega : ¬ (muNegFiveZeroThreeOwnerAt e).2 < 8)] using
        (hRv _ _).mpr hright.2.2.2.2
  have hsupport := muNegFiveZeroThreeCandidateSupport_of_antipode G c u v
    (fun i j h ↦ (hRu i j).mp h) (fun i j h ↦ (hRv i j).mp h)
  have hcomplete : MuNegFiveZeroThreeOwnerPairComplete G c u v :=
    muNegFiveZeroThreeOwnerPairComplete_of_candidateSupport
      G c a b u v hsize hab huinj hvinj hurange hvrange hsupport
  exact ⟨muNegFiveZeroThreeOwnerAvailability_of_fixedExterior G c u v
      hfree hfixed,
    muNegFiveZeroThreeExteriorOwnerCoverage_of_pairComplete G c u v
      hfree hreg hcard hsize hcomplete⟩

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
#print axioms Erdos85.muNegFiveZeroThreeCodeSub_surjective
#print axioms Erdos85.muNegFiveZeroThreeOwnerVertex_unique
#print axioms Erdos85.muNegFiveZeroThreeOwnerVertex_inj
#print axioms Erdos85.muNegFiveZeroThreeOwnerAvailability_of_fixedExterior
#print axioms Erdos85.muNegFiveZeroThreeExteriorOwnerCoverage_of_pairComplete
#print axioms Erdos85.muNegFiveZeroThreeOwnerPairComplete_of_candidateSupport
#print axioms Erdos85.muNegFiveZeroThreeCandidateSupport_of_antipode
#print axioms Erdos85.exteriorPairGraph_cycle_iff_antipode_of_odd_defect
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroThree_internal_iff_oddOffset
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroThree_cycleEntriesOne
#print axioms Erdos85.muNegFiveZeroThreeOwnerGeometry_of_rowLedgers
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_intersecting_no_common
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_no_two_common
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_service_unique
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_service_exists
#print axioms Erdos85.muNegFiveZeroThreeGraphServiceSemantics
#print axioms Erdos85.muNegFiveZeroThreeOwnerCompatible_of_graphHit
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_internal_zero
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_irrefl
