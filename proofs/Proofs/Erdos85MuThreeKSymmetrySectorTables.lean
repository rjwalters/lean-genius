import Proofs.Erdos85MuThreeKSymmetryNormalizedAdapter

/-! # Validity of the explicit mu-three sector tables -/

namespace Erdos85

def Mu3SectorTableValid (H T : Nat → Mu3KRow) : Prop :=
  (∀ x, T x ⊆ H x) ∧ (∀ x, x < 8 → ∀ n, n ∈ T x → n < 8)

theorem mu3SectorTableValid_empty (H : Nat → Mu3KRow) :
    Mu3SectorTableValid H mu3EmptyRows := by
  constructor <;> simp [mu3EmptyRows]

theorem mu3SectorTableValid_self
    (H : Nat → Mu3KRow)
    (hbound : ∀ x, x < 8 → ∀ n, n ∈ H x → n < 8) :
    Mu3SectorTableValid H H := by
  exact ⟨fun _ => fun _ h => h, hbound⟩

theorem mu3H16Row_bound :
    ∀ x, x < 8 → ∀ n, n ∈ mu3H16Row x → n < 8 := by
  intro x hx n hn
  simp [mu3H16Row] at hn
  omega

theorem mu3H88Row_bound :
    ∀ x, x < 8 → ∀ n, n ∈ mu3H88Row x → n < 8 := by
  intro x hx n hn
  unfold mu3H88Row at hn
  split at hn <;> simp at hn <;> rcases hn with rfl | rfl <;> omega

theorem mu3H106Row_bound :
    ∀ x, x < 8 → ∀ n, n ∈ mu3H106Row x → n < 8 := by
  intro x hx n hn
  unfold mu3H106Row at hn
  split at hn <;> simp at hn <;> rcases hn with rfl | rfl <;> omega

theorem mu3SectorTableValid_H16_self :
    Mu3SectorTableValid mu3H16Row mu3H16Row :=
  mu3SectorTableValid_self _ mu3H16Row_bound

theorem mu3SectorTableValid_H88_self :
    Mu3SectorTableValid mu3H88Row mu3H88Row :=
  mu3SectorTableValid_self _ mu3H88Row_bound

theorem mu3SectorTableValid_H106_self :
    Mu3SectorTableValid mu3H106Row mu3H106Row :=
  mu3SectorTableValid_self _ mu3H106Row_bound

theorem mu3SectorTableValid_H88_firstTf :
    Mu3SectorTableValid mu3H88Row mu3H88FirstTfRows := by
  constructor
  · intro x n hn
    simp [mu3H88FirstTfRows] at hn ⊢
    split at * <;> simp_all [mu3H88Row]
  · intro x hx n hn
    exact mu3H88Row_bound x hx n
      ((show mu3H88FirstTfRows x ⊆ mu3H88Row x by
        intro z hz
        simp [mu3H88FirstTfRows] at hz ⊢
        split at * <;> simp_all [mu3H88Row]) hn)

theorem mu3SectorTableValid_H88_secondTf :
    Mu3SectorTableValid mu3H88Row mu3H88SecondTfRows := by
  constructor
  · intro x n hn
    simp [mu3H88SecondTfRows] at hn ⊢
    split at * <;> simp_all [mu3H88Row]
  · intro x hx n hn
    exact mu3H88Row_bound x hx n
      ((show mu3H88SecondTfRows x ⊆ mu3H88Row x by
        intro z hz
        simp [mu3H88SecondTfRows] at hz ⊢
        split at * <;> simp_all [mu3H88Row]) hn)

theorem mu3SectorTableValid_H106_tenTf :
    Mu3SectorTableValid mu3H106Row mu3H106TenTfRows := by
  constructor
  · intro x n hn
    simp [mu3H106TenTfRows] at hn ⊢
    split at * <;> simp_all [mu3H106Row]
  · intro x hx n hn
    exact mu3H106Row_bound x hx n
      ((show mu3H106TenTfRows x ⊆ mu3H106Row x by
        intro z hz
        simp [mu3H106TenTfRows] at hz ⊢
        split at * <;> simp_all [mu3H106Row]) hn)

theorem mu3SectorTableValid_H106_sixTf :
    Mu3SectorTableValid mu3H106Row mu3H106SixTfRows := by
  constructor
  · intro x n hn
    simp [mu3H106SixTfRows] at hn ⊢
    split at * <;> simp_all [mu3H106Row]
  · intro x hx n hn
    exact mu3H106Row_bound x hx n
      ((show mu3H106SixTfRows x ⊆ mu3H106Row x by
        intro z hz
        simp [mu3H106SixTfRows] at hz ⊢
        split at * <;> simp_all [mu3H106Row]) hn)

end Erdos85

#print axioms Erdos85.mu3SectorTableValid_H88_firstTf
#print axioms Erdos85.mu3SectorTableValid_H106_sixTf
