import Proofs.Erdos85CycleCoverRigidity

/-!
# Length divisibility for cyclic covers

The local orientation theorem for a one-neighbor cycle block immediately
forces the target cycle length to divide the source cycle length.  This file
packages that deck-theoretic conclusion for use by the saturated
minimum-layer defect covering.
-/

namespace Erdos85

/-- A locally cycle-intertwining map from an `n`-cycle to an `r`-cycle can
close after `n` steps only when `r ∣ n`. -/
theorem cycleMap_length_dvd
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (f : ZMod n → ZMod r)
    (hpair : ∀ y, ({f (y - 1), f (y + 1)} : Set (ZMod r)) =
      {f y - 1, f y + 1}) :
    r ∣ n := by
  rcases cycleMap_global_orientation hr f hpair with hforward | hreverse
  · have hiter : ∀ m : ℕ,
        f (m : ZMod n) = f 0 + (m : ZMod r) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          calc
            f ((m + 1 : ℕ) : ZMod n) = f ((m : ZMod n) + 1) := by
              rw [Nat.cast_add, Nat.cast_one]
            _ = f (m : ZMod n) + 1 := hforward _
            _ = f 0 + ((m : ZMod r) + 1) := by rw [ih]; ring
            _ = f 0 + ((m + 1 : ℕ) : ZMod r) := by
              rw [Nat.cast_add, Nat.cast_one]
    have hn := hiter n
    have hncast : (n : ZMod r) = 0 := by
      have hnzero : (n : ZMod n) = 0 := ZMod.natCast_self n
      rw [hnzero] at hn
      have hcancel : f 0 + (n : ZMod r) = f 0 + 0 := by
        simpa using hn.symm
      exact add_left_cancel hcancel
    exact (ZMod.natCast_eq_zero_iff n r).mp hncast
  · have hiter : ∀ m : ℕ,
        f (m : ZMod n) = f 0 - (m : ZMod r) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          calc
            f ((m + 1 : ℕ) : ZMod n) = f ((m : ZMod n) + 1) := by
              rw [Nat.cast_add, Nat.cast_one]
            _ = f (m : ZMod n) - 1 := hreverse _
            _ = f 0 - ((m : ZMod r) + 1) := by rw [ih]; ring
            _ = f 0 - ((m + 1 : ℕ) : ZMod r) := by
              rw [Nat.cast_add, Nat.cast_one]
    have hn := hiter n
    have hncast : (n : ZMod r) = 0 := by
      have hnzero : (n : ZMod n) = 0 := ZMod.natCast_self n
      rw [hnzero] at hn
      have : f 0 - (n : ZMod r) = f 0 := hn.symm
      exact sub_eq_self.mp this
    exact (ZMod.natCast_eq_zero_iff n r).mp hncast

end Erdos85
