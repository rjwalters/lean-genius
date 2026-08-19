import Proofs.Erdos85SixTenConcreteTerminalAssembly
import Proofs.Erdos85SizeTwoEigenlineCycleCoordinateNormalization

/-! # Phase-normalized cyclic coordinates for the C6+C10 terminal -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The parity sign is the usual power of negative one. -/
theorem sixTenParitySign_eq_negOnePow (k : Nat) :
    sixTenParitySign k = (-1 : ℤ) ^ k := by
  by_cases hk : k % 2 = 0
  · have heven : Even k := Nat.even_iff.mpr hk
    simp [sixTenParitySign, hk, heven.neg_one_pow]
  · have hodd : Odd k := Nat.not_even_iff_odd.mp (Nat.even_iff.not.mpr hk)
    simp [sixTenParitySign, hk, hodd.neg_one_pow]

/-- Reindexing finite cycle coordinates through `Fin n ≃ ZMod n` gives the
neighbor-finset formulation used by the exterior-model theorems. -/
theorem zmodCycleCoordinates_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (m : Nat)
    (c : H.ConnectedComponent)
    (e : Fin (m + 2) ≃ c.supp)
    (he : ∀ i j, (cycleGraph (m + 2)).Adj i j ↔ H.Adj (e i).1 (e j).1) :
    let u : ZMod (m + 2) → V :=
      fun z => (e ((ZMod.finEquiv (m + 2)).symm z)).1
    ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)} := by
  dsimp only
  intro z
  ext y
  rw [H.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hzy
    have hyc : y ∈ c.supp :=
      (ConnectedComponent.mem_supp_congr_adj c hzy).mp
        (e ((ZMod.finEquiv (m + 2)).symm z)).2
    let j : Fin (m + 2) := e.symm ⟨y, hyc⟩
    have hy : (e j).1 = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hyc⟩)
    have hcycle : (cycleGraph (m + 2)).Adj
        ((ZMod.finEquiv (m + 2)).symm z) j := by
      apply (he _ _).mpr
      simpa [hy] using hzy
    have hj : j = (ZMod.finEquiv (m + 2)).symm (z - 1) ∨
        j = (ZMod.finEquiv (m + 2)).symm (z + 1) := by
      have hmem : j ∈ (cycleGraph (m + 2)).neighborFinset
          ((ZMod.finEquiv (m + 2)).symm z) := by
        rw [(cycleGraph (m + 2)).mem_neighborFinset]
        exact hcycle
      rw [cycleGraph_neighborFinset] at hmem
      simpa using hmem
    rcases hj with hj | hj
    · left; rw [← hy, hj]
    · right; rw [← hy, hj]
  · rintro (rfl | rfl)
    · apply (he _ _).mp
      rw [← (cycleGraph (m + 2)).mem_neighborFinset,
        cycleGraph_neighborFinset]
      simp
    · apply (he _ _).mp
      rw [← (cycleGraph (m + 2)).mem_neighborFinset,
        cycleGraph_neighborFinset]
      simp

/-- The normalized data needed from one internal cycle shore. -/
structure NormalizedShoreCoordinates
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (a : H.ConnectedComponent) (s : W → ℤ) (n : Nat) [NeZero n] where
  u : ZMod n → W
  injective : Function.Injective u
  range : Set.range u = a.supp
  neighbor : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)}
  sign : ∀ z, s (u z) = sixTenParitySign ((ZMod.finEquiv n).symm z).val

private theorem finSix_shift_sign (i : Fin 6) :
    (-1 : ℤ) ^ (i + 1).val * (-1) = sixTenParitySign i.val := by
  fin_cases i <;> decide

/-- Every signed six-cycle admits coordinates with positive even phase. -/
theorem exists_normalizedSixShoreCoordinates
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (a : H.ConnectedComponent) (ha : a.supp.ncard = 6)
    (s : W → ℤ)
    (hsign : ∀ x ∈ a.supp, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    Nonempty (NormalizedShoreCoordinates H a s 6) := by
  obtain ⟨e, he, hs⟩ :=
    exists_componentCycleEquiv_sign_normalized H hdeg 3 (by omega) a
      (by simpa using ha) s hflip
  rcases hsign (e 0).1 (e 0).2 with hphase | hphase
  · let shift : Equiv.Perm (Fin 6) := Equiv.addRight 1
    let e' : Fin 6 ≃ a.supp := shift.trans e
    have he' : ∀ i j, (cycleGraph 6).Adj i j ↔
        H.Adj (e' i).1 (e' j).1 := by
      intro i j
      change (cycleGraph 6).Adj i j ↔ H.Adj (e (i + 1)).1 (e (j + 1)).1
      rw [← he]
      simp [cycleGraph_adj]
    let u : ZMod 6 → W := fun z => (e' ((ZMod.finEquiv 6).symm z)).1
    refine ⟨⟨u, ?_, ?_, ?_, ?_⟩⟩
    · intro x y hxy
      apply (ZMod.finEquiv 6).symm.injective
      apply e'.injective
      exact Subtype.ext hxy
    · ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (e' ((ZMod.finEquiv 6).symm z)).2
      · intro hx
        obtain ⟨i, hi⟩ := e'.surjective ⟨x, hx⟩
        exact ⟨ZMod.finEquiv 6 i, congrArg Subtype.val hi⟩
    · exact zmodCycleCoordinates_neighborFinset H 4 a e' he'
    · intro z
      let i := (ZMod.finEquiv 6).symm z
      change s (e (i + 1)).1 = sixTenParitySign i.val
      have hphase' : s (e ⟨0, by omega⟩).1 = -1 := by simpa using hphase
      rw [hs, hphase']
      exact finSix_shift_sign i
  · let u : ZMod 6 → W := fun z => (e ((ZMod.finEquiv 6).symm z)).1
    refine ⟨⟨u, ?_, ?_, ?_, ?_⟩⟩
    · intro x y hxy
      apply (ZMod.finEquiv 6).symm.injective
      apply e.injective
      exact Subtype.ext hxy
    · ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (e ((ZMod.finEquiv 6).symm z)).2
      · intro hx
        obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
        exact ⟨ZMod.finEquiv 6 i, congrArg Subtype.val hi⟩
    · exact zmodCycleCoordinates_neighborFinset H 4 a e he
    · intro z
      have hphase' : s (e ⟨0, by omega⟩).1 = 1 := by simpa using hphase
      rw [hs, hphase', mul_one, sixTenParitySign_eq_negOnePow]

private theorem finTen_shift_sign (i : Fin 10) :
    (-1 : ℤ) ^ (i + 1).val * (-1) = sixTenParitySign i.val := by
  fin_cases i <;> decide

/-- Every signed ten-cycle admits coordinates with positive even phase. -/
theorem exists_normalizedTenShoreCoordinates
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (a : H.ConnectedComponent) (ha : a.supp.ncard = 10)
    (s : W → ℤ)
    (hsign : ∀ x ∈ a.supp, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    Nonempty (NormalizedShoreCoordinates H a s 10) := by
  obtain ⟨e, he, hs⟩ :=
    exists_componentCycleEquiv_sign_normalized H hdeg 5 (by omega) a
      (by simpa using ha) s hflip
  rcases hsign (e 0).1 (e 0).2 with hphase | hphase
  · let shift : Equiv.Perm (Fin 10) := Equiv.addRight 1
    let e' : Fin 10 ≃ a.supp := shift.trans e
    have he' : ∀ i j, (cycleGraph 10).Adj i j ↔
        H.Adj (e' i).1 (e' j).1 := by
      intro i j
      change (cycleGraph 10).Adj i j ↔ H.Adj (e (i + 1)).1 (e (j + 1)).1
      rw [← he]
      simp [cycleGraph_adj]
    let u : ZMod 10 → W := fun z => (e' ((ZMod.finEquiv 10).symm z)).1
    refine ⟨⟨u, ?_, ?_, ?_, ?_⟩⟩
    · intro x y hxy
      apply (ZMod.finEquiv 10).symm.injective
      apply e'.injective
      exact Subtype.ext hxy
    · ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (e' ((ZMod.finEquiv 10).symm z)).2
      · intro hx
        obtain ⟨i, hi⟩ := e'.surjective ⟨x, hx⟩
        exact ⟨ZMod.finEquiv 10 i, congrArg Subtype.val hi⟩
    · exact zmodCycleCoordinates_neighborFinset H 8 a e' he'
    · intro z
      let i := (ZMod.finEquiv 10).symm z
      change s (e (i + 1)).1 = sixTenParitySign i.val
      have hphase' : s (e ⟨0, by omega⟩).1 = -1 := by simpa using hphase
      rw [hs, hphase']
      exact finTen_shift_sign i
  · let u : ZMod 10 → W := fun z => (e ((ZMod.finEquiv 10).symm z)).1
    refine ⟨⟨u, ?_, ?_, ?_, ?_⟩⟩
    · intro x y hxy
      apply (ZMod.finEquiv 10).symm.injective
      apply e.injective
      exact Subtype.ext hxy
    · ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (e ((ZMod.finEquiv 10).symm z)).2
      · intro hx
        obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
        exact ⟨ZMod.finEquiv 10 i, congrArg Subtype.val hi⟩
    · exact zmodCycleCoordinates_neighborFinset H 8 a e he
    · intro z
      have hphase' : s (e ⟨0, by omega⟩).1 = 1 := by simpa using hphase
      rw [hs, hphase', mul_one, sixTenParitySign_eq_negOnePow]

/-- The cyclic parametrizations required by the checked C6+C10 terminal are
automatic from the two internal components and the size-two eigenline. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hVcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (hab : a ≠ b) (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (hpaircard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hpairinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (houtcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedgesNcard : (exteriorPairGraph G c).edgeSet.ncard = 48) : False := by
  let H := G.induce c.supp
  have hdeg : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hVcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) x
  have hflip : ∀ ⦃x y : c.supp⦄,
      H.Adj x y → s x.1 = -s y.1 := by
    intro x y hxy
    have hymem : y.1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c x.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset x.1 y.1).mpr hxy,
        (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
    have hopen := (internal_alternation G hfree (by omega) hreg hVcard
      c hc s hs_in hs_out hA_in x.2).2 y.1 hymem
    linarith
  obtain ⟨cu⟩ := exists_normalizedSixShoreCoordinates
    H hdeg a ha (fun x => s x.1) (fun x _ => hs_in x.1 x.2) hflip
  obtain ⟨cv⟩ := exists_normalizedTenShoreCoordinates
    H hdeg b hb (fun x => s x.1) (fun x _ => hs_in x.1 x.2) hflip
  exact binarySquare_regular_sizeTwoPart_eight_sixTen_false_of_normalized_coordinates
    G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b hab ha hb
      cu.u cv.u cu.injective cv.injective cu.range cv.range
      cu.neighbor cv.neighbor cu.sign cv.sign hpaircard hpairinc
      houtcard hRedgesNcard

end

end Erdos85

#print axioms Erdos85.zmodCycleCoordinates_neighborFinset
#print axioms Erdos85.exists_normalizedSixShoreCoordinates
#print axioms Erdos85.exists_normalizedTenShoreCoordinates
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_false
