import Proofs.Erdos85OrderFortyNineCanonicalTripleSystem
import Proofs.Erdos85OrderFortyNineCanonicalMaskFibers

/-!
# Fiber census of the canonical order-49 profiles

The graph-facing census is proved structurally in
`Erdos85OrderFortyNineCanonicalTripleSystem`.  This file independently
checks that the generated canonical mask arrays have the same universal
description.  Only 18 representatives and 512 supports are involved.
-/

namespace Erdos85

open OrderFortyNineWitnessTable

set_option maxRecDepth 100000

/-- Number of canonical mask entries carrying exactly `S`. -/
def orderFortyNineMaskSupportFiberCount
    (masks : Array Nat) (S : Finset (Fin 9)) : Nat :=
  (Finset.univ.filter fun i : Fin 49 =>
    orderFortyNineMaskSupport masks i = S).card

theorem orderFortyNine_card_maskSupportFiber
    (masks : Array Nat) (S : Finset (Fin 9)) :
    Fintype.card {i : Fin 49 // orderFortyNineMaskSupport masks i = S} =
      orderFortyNineMaskSupportFiberCount masks S := by
  rw [Fintype.card_subtype]
  rfl

/-- The structural multiplicity prescribed by a canonical triple system:
highs and residual lows at the empty support; triple incidence at singletons;
one uncovered-pair block; one listed triple block; nothing larger. -/
def orderFortyNineCanonicalSupportMultiplicity
    (rep : OrderFortyNineH9System) (S : Finset (Fin 9)) : Nat :=
  let N := S.image Fin.val
  let triples := orderFortyNineRepresentativeTripleSet rep
  if S.card = 0 then
    13 - rep.length
  else if S.card = 1 then
    (triples.filter fun T => N ⊆ T).card
  else if S.card = 2 then
    if ∃ T ∈ triples, N ⊆ T then 0 else 1
  else if S.card = 3 then
    if N ∈ triples then 1 else 0
  else
    0

/-- Multiplicity after remembering whether a vertex belongs to the initial
nine high positions.  This separates the nine structural zero masks from the
residual low zero masks. -/
def orderFortyNineCanonicalVertexKeyMultiplicity
    (rep : OrderFortyNineH9System) (key : Bool × Finset (Fin 9)) : Nat :=
  if key.1 then
    if key.2.card = 0 then 9 else 0
  else if key.2.card = 0 then
    4 - rep.length
  else
    orderFortyNineCanonicalSupportMultiplicity rep key.2

def orderFortyNineMaskVertexKey (masks : Array Nat) (i : Fin 49) :
    Bool × Finset (Fin 9) :=
  (decide (i.val < 9), orderFortyNineMaskSupport masks i)

def orderFortyNineMaskVertexKeyFiberCount
    (masks : Array Nat) (key : Bool × Finset (Fin 9)) : Nat :=
  (Finset.univ.filter fun i : Fin 49 =>
    orderFortyNineMaskVertexKey masks i = key).card

theorem orderFortyNine_card_maskVertexKeyFiber
    (masks : Array Nat) (key : Bool × Finset (Fin 9)) :
    Fintype.card {i : Fin 49 // orderFortyNineMaskVertexKey masks i = key} =
      orderFortyNineMaskVertexKeyFiberCount masks key := by
  rw [Fintype.card_subtype]
  rfl

theorem orderFortyNineH9T2_profileFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems) (S : Finset (Fin 9)) :
    orderFortyNineMaskSupportFiberCount
        (orderFortyNineH9ProfileMasks rep) S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  native_decide +revert

theorem orderFortyNineH9T3_profileFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems) (S : Finset (Fin 9)) :
    orderFortyNineMaskSupportFiberCount
        (orderFortyNineH9ProfileMasks rep) S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  native_decide +revert

theorem orderFortyNineH9T4_profileFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems) (S : Finset (Fin 9)) :
    orderFortyNineMaskSupportFiberCount
        (orderFortyNineH9ProfileMasks rep) S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  native_decide +revert

theorem orderFortyNineH9T2_vertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems)
    (key : Bool × Finset (Fin 9)) :
    orderFortyNineMaskVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalVertexKeyMultiplicity rep key := by
  native_decide +revert

theorem orderFortyNineH9T3_vertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems)
    (key : Bool × Finset (Fin 9)) :
    orderFortyNineMaskVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalVertexKeyMultiplicity rep key := by
  native_decide +revert

theorem orderFortyNineH9T4_vertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems)
    (key : Bool × Finset (Fin 9)) :
    orderFortyNineMaskVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalVertexKeyMultiplicity rep key := by
  native_decide +revert

/-- A key that remembers the *identity* of each of the nine high vertices,
not merely membership in the high stratum.  This is the key needed by the
Boolean terminal, where bit `w` must refer to vertex `w`. -/
def orderFortyNineMaskAlignedVertexKey (masks : Array Nat) (i : Fin 49) :
    Option (Fin 9) × Finset (Fin 9) :=
  (if h : i.val < 9 then some ⟨i.val, h⟩ else none,
    orderFortyNineMaskSupport masks i)

def orderFortyNineCanonicalAlignedVertexKeyMultiplicity
    (rep : OrderFortyNineH9System)
    (key : Option (Fin 9) × Finset (Fin 9)) : Nat :=
  match key.1 with
  | some _ => if key.2.card = 0 then 1 else 0
  | none =>
      if key.2.card = 0 then 4 - rep.length
      else orderFortyNineCanonicalSupportMultiplicity rep key.2

def orderFortyNineMaskAlignedVertexKeyFiberCount
    (masks : Array Nat) (key : Option (Fin 9) × Finset (Fin 9)) : Nat :=
  (Finset.univ.filter fun i : Fin 49 =>
    orderFortyNineMaskAlignedVertexKey masks i = key).card

theorem orderFortyNine_card_maskAlignedVertexKeyFiber
    (masks : Array Nat) (key : Option (Fin 9) × Finset (Fin 9)) :
    Fintype.card {i : Fin 49 //
      orderFortyNineMaskAlignedVertexKey masks i = key} =
      orderFortyNineMaskAlignedVertexKeyFiberCount masks key := by
  rw [Fintype.card_subtype]
  rfl

private theorem maskSupport_eq_empty_of_highMasksZero
    (masks : Array Nat) (hzero : OrderFortyNineHighMasksZero masks)
    (i : Fin 49) (hi : i.val < 9) :
    orderFortyNineMaskSupport masks i = ∅ := by
  ext w
  have hiEq : i = orderFortyNineHighVertex ⟨i.val, hi⟩ := by rfl
  rw [hiEq]
  simp only [orderFortyNineMaskSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.notMem_empty, iff_false]
  simpa using hzero ⟨i.val, hi⟩ w

private theorem aligned_some_fiberCount
    (masks : Array Nat) (hzero : OrderFortyNineHighMasksZero masks)
    (w : Fin 9) (S : Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount masks (some w, S) =
      if S.card = 0 then 1 else 0 := by
  by_cases hS : S.card = 0
  · rw [if_pos hS]
    have hSEmpty : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    unfold orderFortyNineMaskAlignedVertexKeyFiberCount
    rw [Finset.card_eq_one]
    refine ⟨orderFortyNineHighVertex w, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hiKey
      have hiSome := congrArg Prod.fst hiKey
      simp only [orderFortyNineMaskAlignedVertexKey] at hiSome
      split at hiSome
      next hi =>
        have hfin : (⟨i.val, hi⟩ : Fin 9) = w := by simpa using hiSome
        apply Fin.ext
        simpa [orderFortyNineHighVertex] using
          congrArg (fun x : Fin 9 => x.val) hfin
      next => simp at hiSome
    · intro hiEq
      subst i
      have hwlt : (orderFortyNineHighVertex w).val < 9 := w.isLt
      change ((if h : (orderFortyNineHighVertex w).val < 9 then
        some ⟨(orderFortyNineHighVertex w).val, h⟩ else none),
          orderFortyNineMaskSupport masks (orderFortyNineHighVertex w)) =
        (some w, ∅)
      rw [dif_pos hwlt]
      apply Prod.ext
      · simp [orderFortyNineHighVertex]
      · exact maskSupport_eq_empty_of_highMasksZero masks hzero _ hwlt
  · rw [if_neg hS]
    unfold orderFortyNineMaskAlignedVertexKeyFiberCount
    rw [Finset.card_eq_zero]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    intro hi
    have hiSome := congrArg Prod.fst hi
    have hiSupport := congrArg Prod.snd hi
    simp only [orderFortyNineMaskAlignedVertexKey] at hiSome hiSupport
    split at hiSome
    next hil =>
      have hz := maskSupport_eq_empty_of_highMasksZero masks hzero i hil
      rw [hz] at hiSupport
      have : S.card = 0 := by simpa using congrArg Finset.card hiSupport.symm
      exact hS this
    next => simp at hiSome

private theorem aligned_none_set_eq_low
    (masks : Array Nat) (S : Finset (Fin 9)) :
    (Finset.univ.filter fun i : Fin 49 =>
      orderFortyNineMaskAlignedVertexKey masks i = (none, S)) =
    ((Finset.univ.filter fun i : Fin 49 =>
      orderFortyNineMaskSupport masks i = S).filter fun i => ¬ i.val < 9) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold orderFortyNineMaskAlignedVertexKey
  split
  next hi =>
    constructor
    · intro h
      have := congrArg Prod.fst h
      simp at this
    · intro h
      exact False.elim (h.2 hi)
  next hi =>
    constructor
    · intro h
      exact ⟨congrArg Prod.snd h, hi⟩
    · intro h
      exact Prod.ext rfl h.1

private theorem high_support_fiberCount
    (masks : Array Nat) (hzero : OrderFortyNineHighMasksZero masks)
    (S : Finset (Fin 9)) :
    (((Finset.univ.filter fun i : Fin 49 =>
      orderFortyNineMaskSupport masks i = S).filter fun i => i.val < 9).card) =
      if S.card = 0 then 9 else 0 := by
  by_cases hS : S.card = 0
  · rw [if_pos hS]
    have hSEmpty : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    have hset :
        ((Finset.univ.filter fun i : Fin 49 =>
          orderFortyNineMaskSupport masks i = ∅).filter fun i => i.val < 9) =
          (Finset.univ.filter fun i : Fin 49 => i.val < 9) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hi
        exact ⟨maskSupport_eq_empty_of_highMasksZero masks hzero i hi, hi⟩
    rw [hset]
    decide
  · rw [if_neg hS, Finset.card_eq_zero]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rintro ⟨hiSupport, hi⟩
    have hz := maskSupport_eq_empty_of_highMasksZero masks hzero i hi
    rw [hz] at hiSupport
    apply hS
    exact Finset.card_eq_zero.mpr hiSupport.symm

private theorem aligned_none_add_high_eq_support
    (masks : Array Nat) (hzero : OrderFortyNineHighMasksZero masks)
    (S : Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount masks (none, S) +
        (if S.card = 0 then 9 else 0) =
      orderFortyNineMaskSupportFiberCount masks S := by
  unfold orderFortyNineMaskAlignedVertexKeyFiberCount
  rw [aligned_none_set_eq_low]
  rw [← high_support_fiberCount masks hzero S]
  unfold orderFortyNineMaskSupportFiberCount
  simpa [Nat.add_comm] using
    Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun i : Fin 49 =>
        orderFortyNineMaskSupport masks i = S)
      (p := fun i => i.val < 9)

private theorem aligned_fiberCount_of_supportFiberCount
    (masks : Array Nat) (rep : OrderFortyNineH9System)
    (hzero : OrderFortyNineHighMasksZero masks)
    (hlen : rep.length ≤ 4)
    (hsupport : ∀ S : Finset (Fin 9),
      orderFortyNineMaskSupportFiberCount masks S =
        orderFortyNineCanonicalSupportMultiplicity rep S)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount masks key =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  rcases key with ⟨ow, S⟩
  cases ow with
  | some w =>
      simpa [orderFortyNineCanonicalAlignedVertexKeyMultiplicity] using
        aligned_some_fiberCount masks hzero w S
  | none =>
      have hsplit := aligned_none_add_high_eq_support masks hzero S
      rw [hsupport S] at hsplit
      change orderFortyNineMaskAlignedVertexKeyFiberCount masks (none, S) =
        if S.card = 0 then 4 - rep.length
        else orderFortyNineCanonicalSupportMultiplicity rep S
      by_cases hS : S.card = 0
      · rw [if_pos hS] at hsplit ⊢
        simp only [orderFortyNineCanonicalSupportMultiplicity, hS, if_pos] at hsplit
        omega
      · rw [if_neg hS] at hsplit ⊢
        simpa using hsplit

private theorem expectedFiber_eq_supportMultiplicity_t2
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems) (S : Finset (Fin 9)) :
    orderFortyNineExpectedFiber rep S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  decide +revert

private theorem expectedFiber_eq_supportMultiplicity_t3
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems) (S : Finset (Fin 9)) :
    orderFortyNineExpectedFiber rep S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  decide +revert

private theorem expectedFiber_eq_supportMultiplicity_t4
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems) (S : Finset (Fin 9)) :
    orderFortyNineExpectedFiber rep S =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  decide +revert

theorem orderFortyNineH9T2_alignedVertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  apply aligned_fiberCount_of_supportFiberCount
  · exact orderFortyNineH9ProfileMasks_high_zero rep
  · decide +revert
  · intro S
    have hall : rep ∈ orderFortyNineAllH9Reps :=
      mem_allH9Reps_of_mem_t2 (by simpa using hrep)
    calc
      orderFortyNineMaskSupportFiberCount
          (orderFortyNineH9ProfileMasks rep) S =
          orderFortyNineMaskFiberCount
            (orderFortyNineH9ProfileMasks rep) S := rfl
      _ = orderFortyNineExpectedFiber rep S :=
        orderFortyNineMaskFiberCount_eq_expected rep hall S
      _ = orderFortyNineCanonicalSupportMultiplicity rep S :=
        expectedFiber_eq_supportMultiplicity_t2 rep hrep S

theorem orderFortyNineH9T3_alignedVertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  apply aligned_fiberCount_of_supportFiberCount
  · exact orderFortyNineH9ProfileMasks_high_zero rep
  · decide +revert
  · intro S
    have hall : rep ∈ orderFortyNineAllH9Reps :=
      mem_allH9Reps_of_mem_t3 (by simpa using hrep)
    calc
      orderFortyNineMaskSupportFiberCount
          (orderFortyNineH9ProfileMasks rep) S =
          orderFortyNineMaskFiberCount
            (orderFortyNineH9ProfileMasks rep) S := rfl
      _ = orderFortyNineExpectedFiber rep S :=
        orderFortyNineMaskFiberCount_eq_expected rep hall S
      _ = orderFortyNineCanonicalSupportMultiplicity rep S :=
        expectedFiber_eq_supportMultiplicity_t3 rep hrep S

theorem orderFortyNineH9T4_alignedVertexKeyFiberCount
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    orderFortyNineMaskAlignedVertexKeyFiberCount
        (orderFortyNineH9ProfileMasks rep) key =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  apply aligned_fiberCount_of_supportFiberCount
  · exact orderFortyNineH9ProfileMasks_high_zero rep
  · decide +revert
  · intro S
    have hall : rep ∈ orderFortyNineAllH9Reps :=
      mem_allH9Reps_of_mem_t4 (by simpa using hrep)
    calc
      orderFortyNineMaskSupportFiberCount
          (orderFortyNineH9ProfileMasks rep) S =
          orderFortyNineMaskFiberCount
            (orderFortyNineH9ProfileMasks rep) S := rfl
      _ = orderFortyNineExpectedFiber rep S :=
        orderFortyNineMaskFiberCount_eq_expected rep hall S
      _ = orderFortyNineCanonicalSupportMultiplicity rep S :=
        expectedFiber_eq_supportMultiplicity_t4 rep hrep S

theorem orderFortyNineH9T2_profileMasks_size
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T2Systems) :
    (orderFortyNineH9ProfileMasks rep).size = 49 := by
  decide +revert

theorem orderFortyNineH9T3_profileMasks_size
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T3Systems) :
    (orderFortyNineH9ProfileMasks rep).size = 49 := by
  decide +revert

theorem orderFortyNineH9T4_profileMasks_size
    (rep : OrderFortyNineH9System)
    (hrep : rep ∈ orderFortyNineH9T4Systems) :
    (orderFortyNineH9ProfileMasks rep).size = 49 := by
  decide +revert

end Erdos85
