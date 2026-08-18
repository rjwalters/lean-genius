import Proofs.Erdos85MuThreeKSymmetryShapeExhaustive

/-! # A fixed 22-slot index for the mu-three K candidates -/

namespace Erdos85

/-- Position indices in each of the ten sector enumerations.  Empty sectors
have a `Fin 0` payload, so the total type contains exactly the 22 surviving
tables without requiring a global reduction of the search enumerators. -/
inductive Mu3KCandidateSlot where
  | c16AllTf (i : Fin 1)
  | c16AllTriangle (i : Fin 3)
  | c88AllTf (i : Fin 1)
  | c88AllTriangle (i : Fin 13)
  | c88FirstTf (i : Fin 1)
  | c88SecondTf (i : Fin 1)
  | c106AllTf (i : Fin 1)
  | c106AllTriangle (i : Fin 0)
  | c106TenTf (i : Fin 0)
  | c106SixTf (i : Fin 1)
  deriving DecidableEq, Fintype

theorem mu3KCandidateSlot_card : Fintype.card Mu3KCandidateSlot = 22 := by
  decide

noncomputable def mu3KCandidateSlotEquivFin : Mu3KCandidateSlot ≃ Fin 22 :=
  Fintype.equivFinOfCardEq mu3KCandidateSlot_card

def Mu3KCandidateSlot.sector : Mu3KCandidateSlot → Mu3KSectorChoice
  | .c16AllTf _ => .c16AllTf
  | .c16AllTriangle _ => .c16AllTriangle
  | .c88AllTf _ => .c88AllTf
  | .c88AllTriangle _ => .c88AllTriangle
  | .c88FirstTf _ => .c88FirstTf
  | .c88SecondTf _ => .c88SecondTf
  | .c106AllTf _ => .c106AllTf
  | .c106AllTriangle _ => .c106AllTriangle
  | .c106TenTf _ => .c106TenTf
  | .c106SixTf _ => .c106SixTf

def Mu3KCandidateSlot.position : Mu3KCandidateSlot → Nat
  | .c16AllTf i | .c16AllTriangle i
  | .c88AllTf i | .c88AllTriangle i
  | .c88FirstTf i | .c88SecondTf i
  | .c106AllTf i | .c106AllTriangle i
  | .c106TenTf i | .c106SixTf i => i.val

def Mu3KCandidateSlot.rows (slot : Mu3KCandidateSlot) : Mu3KRows :=
  (mu3KSectorEnumeration slot.sector.HRows slot.sector.TRows).getD
    slot.position []

theorem List.getD_mem_of_lt {α : Type*} (l : List α) (fallback : α)
    (n : Nat) (hn : n < l.length) : l.getD n fallback ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  exact l.getElem_mem hn

theorem Mu3KCandidateSlot.position_lt (slot : Mu3KCandidateSlot) :
    slot.position <
      (mu3KSectorEnumeration slot.sector.HRows slot.sector.TRows).length := by
  cases slot with
  | c16AllTf i =>
      change i.val < (mu3KSectorEnumeration mu3H16Row mu3H16Row).length
      rw [mu3KSectorEnumeration_H16_allTf_count]; exact i.isLt
  | c16AllTriangle i =>
      change i.val < (mu3KSectorEnumeration mu3H16Row mu3EmptyRows).length
      rw [mu3KSectorEnumeration_H16_allTriangle_count]; exact i.isLt
  | c88AllTf i =>
      change i.val < (mu3KSectorEnumeration mu3H88Row mu3H88Row).length
      rw [mu3KSectorEnumeration_H88_allTf_count]; exact i.isLt
  | c88AllTriangle i =>
      change i.val < (mu3KSectorEnumeration mu3H88Row mu3EmptyRows).length
      rw [mu3KSectorEnumeration_H88_allTriangle_count]; exact i.isLt
  | c88FirstTf i =>
      change i.val < (mu3KSectorEnumeration mu3H88Row mu3H88FirstTfRows).length
      rw [mu3KSectorEnumeration_H88_firstTf_count]; exact i.isLt
  | c88SecondTf i =>
      change i.val < (mu3KSectorEnumeration mu3H88Row mu3H88SecondTfRows).length
      rw [mu3KSectorEnumeration_H88_secondTf_count]; exact i.isLt
  | c106AllTf i =>
      change i.val < (mu3KSectorEnumeration mu3H106Row mu3H106Row).length
      rw [mu3KSectorEnumeration_H106_allTf_count]; exact i.isLt
  | c106AllTriangle i => exact Fin.elim0 i
  | c106TenTf i => exact Fin.elim0 i
  | c106SixTf i =>
      change i.val < (mu3KSectorEnumeration mu3H106Row mu3H106SixTfRows).length
      rw [mu3KSectorEnumeration_H106_sixTf_count]; exact i.isLt

theorem Mu3KCandidateSlot.rows_mem (slot : Mu3KCandidateSlot) :
    slot.rows ∈ mu3KSectorEnumeration slot.sector.HRows slot.sector.TRows := by
  exact List.getD_mem_of_lt _ [] slot.position slot.position_lt

def Mu3KCandidateSlot.toAllSectorIndex
    (slot : Mu3KCandidateSlot) : Mu3AllSectorCandidateIndex :=
  ⟨slot.sector, ⟨slot.rows, slot.rows_mem⟩⟩

def mu3SlotCandidate
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (slot : Mu3KCandidateSlot) (x : X) (y : Y) : Bool :=
  mu3KRowsCandidate slot.rows (row x) (column y)

@[simp] theorem mu3AllSectorCandidate_toAllSectorIndex
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (slot : Mu3KCandidateSlot) (x : X) (y : Y) :
    mu3AllSectorCandidate row column slot.toAllSectorIndex x y =
      mu3SlotCandidate row column slot x y := rfl

theorem exists_fin_getD_eq_of_mem_of_length_eq
    {α : Type*} (l : List α) (x fallback : α) (n : Nat)
    (hx : x ∈ l) (hlen : l.length = n) :
    ∃ i : Fin n, l.getD i.val fallback = x := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hx
  refine ⟨⟨k, by omega⟩, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  simpa using heq

/-- Every subtype-indexed enumerator candidate has a unique-shaped slot
carrying the same concrete row table.  This is the bridge from the exhaustive
provider's convenient membership index to the certificate dispatch index. -/
theorem exists_mu3KCandidateSlot_of_allSectorIndex
    (i : Mu3AllSectorCandidateIndex) :
    ∃ slot : Mu3KCandidateSlot,
      slot.sector = i.1 ∧ slot.rows = i.2.1 := by
  rcases i with ⟨sector, rows, hrows⟩
  cases sector
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 1 hrows mu3KSectorEnumeration_H16_allTf_count
    exact ⟨.c16AllTf j, rfl, hj⟩
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 3 hrows mu3KSectorEnumeration_H16_allTriangle_count
    exact ⟨.c16AllTriangle j, rfl, hj⟩
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 1 hrows mu3KSectorEnumeration_H88_allTf_count
    exact ⟨.c88AllTf j, rfl, hj⟩
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 13 hrows mu3KSectorEnumeration_H88_allTriangle_count
    exact ⟨.c88AllTriangle j, rfl, hj⟩
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 1 hrows mu3KSectorEnumeration_H88_firstTf_count
    exact ⟨.c88FirstTf j, rfl, hj⟩
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 1 hrows mu3KSectorEnumeration_H88_secondTf_count
    exact ⟨.c88SecondTf j, rfl, hj⟩
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 1 hrows mu3KSectorEnumeration_H106_allTf_count
    exact ⟨.c106AllTf j, rfl, hj⟩
  · obtain ⟨j, _⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 0 hrows mu3KSectorEnumeration_H106_allTriangle_count
    exact Fin.elim0 j
  · obtain ⟨j, _⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 0 hrows mu3KSectorEnumeration_H106_tenTf_count
    exact Fin.elim0 j
  · obtain ⟨j, hj⟩ := exists_fin_getD_eq_of_mem_of_length_eq
      _ rows [] 1 hrows mu3KSectorEnumeration_H106_sixTf_count
    exact ⟨.c106SixTf j, rfl, hj⟩

theorem exists_mu3SlotCandidate_of_allSectorCandidate
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (K : X → Y → Prop)
    (h : ∃ i : Mu3AllSectorCandidateIndex,
      ∀ x y, K x y ↔ mu3AllSectorCandidate row column i x y = true) :
    ∃ slot : Mu3KCandidateSlot,
      ∀ x y, K x y ↔ mu3SlotCandidate row column slot x y = true := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨slot, _, hrows⟩ := exists_mu3KCandidateSlot_of_allSectorIndex i
  refine ⟨slot, ?_⟩
  intro x y
  rw [hi x y]
  simp only [mu3AllSectorCandidate, mu3SlotCandidate]
  rw [hrows]

/-- The external contradiction provider consists of three legacy all-TF
terminals and nineteen fixed-K LRAT records. -/
inductive Mu3KCertificateTarget where
  | allTfC16 | allTfC88 | allTfC106
  | fixed (i : Fin 19)
  deriving DecidableEq, Fintype

/-- Exact manifest ordering used by the nineteen fixed-K artifacts:
C16 all-triangle first, then the thirteen C8+C8 all-triangle candidates,
then first-TF, C10+C6 six-TF, and second-TF. -/
def Mu3KCandidateSlot.certificateTarget :
    Mu3KCandidateSlot → Mu3KCertificateTarget
  | .c16AllTf _ => .allTfC16
  | .c16AllTriangle i => .fixed ⟨i.val, by omega⟩
  | .c88AllTf _ => .allTfC88
  | .c88AllTriangle i => .fixed ⟨i.val + 3, by omega⟩
  | .c88FirstTf _ => .fixed 16
  | .c88SecondTf _ => .fixed 18
  | .c106AllTf _ => .allTfC106
  | .c106AllTriangle i => Fin.elim0 i
  | .c106TenTf i => Fin.elim0 i
  | .c106SixTf _ => .fixed 17

/-- Uniform index into the twenty-two native grid certificates.  The original
nineteen fixed survivors retain indices `0` through `18`; the three all-TF
singletons occupy `19` (C16), `20` (C8+C8), and `21` (C10+C6). -/
def Mu3KCandidateSlot.certificateGridIndex
    (slot : Mu3KCandidateSlot) : Fin 22 :=
  match slot.certificateTarget with
  | .fixed i => ⟨i.val, by omega⟩
  | .allTfC16 => 19
  | .allTfC88 => 20
  | .allTfC106 => 21

theorem mu3KCertificateTarget_card :
    Fintype.card Mu3KCertificateTarget = 22 := by decide

theorem Mu3KCandidateSlot.certificateTarget_bijective :
    Function.Bijective Mu3KCandidateSlot.certificateTarget := by
  apply (Fintype.bijective_iff_surjective_and_card
    Mu3KCandidateSlot.certificateTarget).2
  constructor
  · intro target
    cases target with
  | allTfC16 => exact ⟨.c16AllTf 0, rfl⟩
  | allTfC88 => exact ⟨.c88AllTf 0, rfl⟩
  | allTfC106 => exact ⟨.c106AllTf 0, rfl⟩
  | fixed i =>
      fin_cases i
      · exact ⟨.c16AllTriangle 0, rfl⟩
      · exact ⟨.c16AllTriangle 1, rfl⟩
      · exact ⟨.c16AllTriangle 2, rfl⟩
      · exact ⟨.c88AllTriangle 0, rfl⟩
      · exact ⟨.c88AllTriangle 1, rfl⟩
      · exact ⟨.c88AllTriangle 2, rfl⟩
      · exact ⟨.c88AllTriangle 3, rfl⟩
      · exact ⟨.c88AllTriangle 4, rfl⟩
      · exact ⟨.c88AllTriangle 5, rfl⟩
      · exact ⟨.c88AllTriangle 6, rfl⟩
      · exact ⟨.c88AllTriangle 7, rfl⟩
      · exact ⟨.c88AllTriangle 8, rfl⟩
      · exact ⟨.c88AllTriangle 9, rfl⟩
      · exact ⟨.c88AllTriangle 10, rfl⟩
      · exact ⟨.c88AllTriangle 11, rfl⟩
      · exact ⟨.c88AllTriangle 12, rfl⟩
      · exact ⟨.c88FirstTf 0, rfl⟩
      · exact ⟨.c106SixTf 0, rfl⟩
      · exact ⟨.c88SecondTf 0, rfl⟩
  · exact mu3KCandidateSlot_card.trans mu3KCertificateTarget_card.symm

noncomputable def mu3KCandidateSlotEquivCertificateTarget :
    Mu3KCandidateSlot ≃ Mu3KCertificateTarget :=
  Equiv.ofBijective Mu3KCandidateSlot.certificateTarget
    Mu3KCandidateSlot.certificateTarget_bijective

end Erdos85

#print axioms Erdos85.mu3KCandidateSlot_card
#print axioms Erdos85.mu3KCandidateSlotEquivFin
#print axioms Erdos85.exists_mu3KCandidateSlot_of_allSectorIndex
#print axioms Erdos85.Mu3KCandidateSlot.rows_mem
#print axioms Erdos85.mu3AllSectorCandidate_toAllSectorIndex
#print axioms Erdos85.exists_mu3SlotCandidate_of_allSectorCandidate
#print axioms Erdos85.Mu3KCandidateSlot.certificateTarget_bijective
