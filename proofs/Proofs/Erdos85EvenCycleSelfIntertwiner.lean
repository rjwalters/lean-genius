import Proofs.Erdos85CycleCoverRigidity

/-!
# The circulant sector of an even-cycle self-intertwiner

For odd cycles, a symmetric zero-diagonal self-intertwiner is completely
circulant.  The proof only uses oddness to solve `2t = x-y`.  This file
extracts the stronger pointwise statement valid at every cycle length:
translation invariance holds whenever the displacement lies in the image of
doubling.  Thus on an even cycle only the other parity class can support the
reverse-circulant obstruction.
-/

namespace Erdos85

/-- A symmetric zero-diagonal cycle self-intertwiner is invariant under
simultaneous translation at every pair whose coordinate difference has a
half. -/
theorem selfIntertwiner_translationInvariant_of_exists_add_self
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hdiag : ∀ x, H x x = 0)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (x y : ZMod r) (hhalf : ∃ t : ZMod r, t + t = x - y) :
    H (x + 1) (y + 1) = H x y := by
  let Δ : ZMod r → ZMod r → ℤ :=
    fun a b ↦ H (a + 1) (b + 1) - H a b
  have hstep (a b : ZMod r) : Δ a b = Δ (a - 1) (b + 1) := by
    dsimp only [Δ]
    have h := hinter a (b + 1)
    rw [show b + 1 - 1 = b by ring] at h
    have hb2 : b + 1 + 1 = b + 2 := by ring
    rw [hb2] at h
    rw [show a - 1 + 1 = a by ring, hb2]
    linear_combination h
  have hiter (a b : ZMod r) : ∀ m : ℕ,
      Δ a b = Δ (a - (m : ZMod r)) (b + (m : ZMod r)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          Δ a b = Δ (a - (m : ZMod r)) (b + (m : ZMod r)) := ih
          _ = Δ ((a - (m : ZMod r)) - 1)
              ((b + (m : ZMod r)) + 1) := hstep _ _
          _ = Δ (a - ((m + 1 : ℕ) : ZMod r))
              (b + ((m + 1 : ℕ) : ZMod r)) := by
                simp only [Nat.cast_add, Nat.cast_one]
                congr 1 <;> ring
  obtain ⟨t, ht⟩ := hhalf
  have hend : x - t = y + t := by
    rw [sub_eq_iff_eq_add]
    calc
      x = (x - y) + y := by abel
      _ = (t + t) + y := by rw [← ht]
      _ = y + t + t := by abel
  have hit := hiter x y t.val
  rw [ZMod.natCast_zmod_val] at hit
  have hzero : Δ (x - t) (y + t) = 0 := by
    rw [← hend]
    simp [Δ, hdiag]
  exact sub_eq_zero.mp (hit.trans hzero)

/-- Equivalent doubling-image formulation of the circulant sector. -/
theorem selfIntertwiner_translationInvariant_of_mem_range_two_mul
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hdiag : ∀ x, H x x = 0)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (x y : ZMod r)
    (hmem : x - y ∈ Set.range (fun t : ZMod r ↦ 2 * t)) :
    H (x + 1) (y + 1) = H x y := by
  obtain ⟨t, ht⟩ := hmem
  apply selfIntertwiner_translationInvariant_of_exists_add_self
    H hdiag hinter x y
  exact ⟨t, by simpa [two_mul] using ht⟩

end Erdos85
