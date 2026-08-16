import Proofs.Erdos85FinEightPairCoordinates
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi

/-! # Canonical form of free involutions on four points -/

namespace Erdos85

def finFourStandardMate : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

theorem finFourStandardMate_involutive :
    Function.Involutive finFourStandardMate := by
  intro i
  decide +revert

theorem finFourStandardMate_ne (i : Fin 4) :
    finFourStandardMate i ≠ i := by
  decide +revert

/-- Every fixed-point-free involution on four points is conjugate to the
standard matching `(01)(23)`.  The closed check ranges over only `4! = 24`
permutations. -/
theorem exists_finFour_perm_intertwining_free_involution
    (mate : Equiv.Perm (Fin 4))
    (hinv : Function.Involutive mate)
    (hfix : ∀ i, mate i ≠ i) :
    ∃ e : Equiv.Perm (Fin 4), ∀ i,
      e (mate i) = finFourStandardMate (e i) := by
  have hfinite : ∀ m : Fin 4 → Fin 4,
      (∀ i, m (m i) = i) → (∀ i, m i ≠ i) →
        ∃ e : Fin 4 → Fin 4,
          (∀ x y, e x = e y → x = y) ∧
          (∀ y, ∃ x, e x = y) ∧ ∀ i,
          e (m i) = finFourStandardMate (e i) := by
    set_option maxRecDepth 10000 in
      decide +revert
  obtain ⟨e, hinj, hsurj, hintertwine⟩ := hfinite mate hinv hfix
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, hintertwine⟩

end Erdos85
