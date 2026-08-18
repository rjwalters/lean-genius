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

/-- The ten component-colour sectors across the three internal shapes. -/
inductive Mu3KSectorChoice where
  | c16AllTf | c16AllTriangle
  | c88AllTf | c88AllTriangle | c88FirstTf | c88SecondTf
  | c106AllTf | c106AllTriangle | c106TenTf | c106SixTf
  deriving DecidableEq, Repr

def Mu3KSectorChoice.HRows : Mu3KSectorChoice → Nat → Mu3KRow
  | .c16AllTf | .c16AllTriangle => mu3H16Row
  | .c88AllTf | .c88AllTriangle | .c88FirstTf | .c88SecondTf => mu3H88Row
  | .c106AllTf | .c106AllTriangle | .c106TenTf | .c106SixTf => mu3H106Row

def Mu3KSectorChoice.TRows : Mu3KSectorChoice → Nat → Mu3KRow
  | .c16AllTf => mu3H16Row
  | .c16AllTriangle => mu3EmptyRows
  | .c88AllTf => mu3H88Row
  | .c88AllTriangle => mu3EmptyRows
  | .c88FirstTf => mu3H88FirstTfRows
  | .c88SecondTf => mu3H88SecondTfRows
  | .c106AllTf => mu3H106Row
  | .c106AllTriangle => mu3EmptyRows
  | .c106TenTf => mu3H106TenTfRows
  | .c106SixTf => mu3H106SixTfRows

theorem Mu3KSectorChoice.valid (sector : Mu3KSectorChoice) :
    Mu3SectorTableValid sector.HRows sector.TRows := by
  cases sector
  · exact mu3SectorTableValid_H16_self
  · exact mu3SectorTableValid_empty _
  · exact mu3SectorTableValid_H88_self
  · exact mu3SectorTableValid_empty _
  · exact mu3SectorTableValid_H88_firstTf
  · exact mu3SectorTableValid_H88_secondTf
  · exact mu3SectorTableValid_H106_self
  · exact mu3SectorTableValid_empty _
  · exact mu3SectorTableValid_H106_tenTf
  · exact mu3SectorTableValid_H106_sixTf

theorem mu3SectorEquation_of_choice_edge_iff
    (sector : Mu3KSectorChoice)
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hiff : ∀ x y, y.val ∈ sector.HRows x.val →
      (K x y ↔ y.val ∈ sector.TRows x.val))
    (x : Fin 8) :
    ((Finset.univ.filter fun y => K x y).image Fin.val) ∩
        sector.HRows x.val = sector.TRows x.val := by
  exact mu3SectorEquation_of_edge_iff sector.HRows sector.TRows K
    sector.valid.1 sector.valid.2 hiff x

end Erdos85

#print axioms Erdos85.mu3SectorTableValid_H88_firstTf
#print axioms Erdos85.mu3SectorTableValid_H106_sixTf
#print axioms Erdos85.Mu3KSectorChoice.valid
#print axioms Erdos85.mu3SectorEquation_of_choice_edge_iff
