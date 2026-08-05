import Proofs.Erdos85DefectCycleBlock

/-!
# Local rigidity of a one-neighbour cycle block

Suppose a rectangular `0/1` block intertwines two cycle adjacency
operators and every column contains exactly one `1`.  Writing `f(y)` for
the row containing that `1`, the intertwining equation says that the two
neighbours of `f(y)` are precisely `f(y-1)` and `f(y+1)`.  Hence the map is
locally either orientation preserving or orientation reversing.

This is the first step in replacing parameter-by-parameter resolvent
calculations by a uniform cyclic-cover description of unequal component
blocks.
-/

namespace Erdos85

/-- Equality of the two unordered neighbour pairs gives the two possible
local orientations.  The lower bound excludes the degenerate cycles of
orders one and two, in which predecessor and successor coincide. -/
theorem cycleMap_local_orientation
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (f : ZMod n → ZMod r) (y : ZMod n)
    (hpair : ({f (y - 1), f (y + 1)} : Set (ZMod r)) =
      {f y - 1, f y + 1}) :
    (f (y - 1) = f y - 1 ∧ f (y + 1) = f y + 1) ∨
      (f (y - 1) = f y + 1 ∧ f (y + 1) = f y - 1) := by
  rw [Set.pair_eq_pair_iff] at hpair
  exact hpair

/-- Consecutive local orientations cannot flip.  This is the elementary
rigidity behind the fact that a one-neighbour intertwining block is a cyclic
covering map rather than an arbitrary balanced map. -/
theorem cycleMap_orientation_cannot_flip
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (f : ZMod n → ZMod r) (y : ZMod n)
    (hy : f (y + 1) = f y + 1)
    (hflip : f y = f (y + 1) + 1) : False := by
  have htwo : (2 : ZMod r) = 0 := by
    have heq : f (y + 1) = f (y + 1) + 2 := by
      calc
        f (y + 1) = f y + 1 := hy
        _ = (f (y + 1) + 1) + 1 := by rw [hflip]
        _ = f (y + 1) + 2 := by ring
    calc
      (2 : ZMod r) = (f (y + 1) + 2) - f (y + 1) := by ring
      _ = 0 := by rw [← heq]; simp
  have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp htwo
  have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- Once a locally intertwining map takes one forward step, the next step is
also forward.  Iteration will give the global cyclic covering normal form. -/
theorem cycleMap_forward_step_propagates
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (f : ZMod n → ZMod r)
    (hpair : ∀ y, ({f (y - 1), f (y + 1)} : Set (ZMod r)) =
      {f y - 1, f y + 1})
    (y : ZMod n) (hy : f (y + 1) = f y + 1) :
    f ((y + 1) + 1) = f (y + 1) + 1 := by
  rcases cycleMap_local_orientation hr f (y + 1) (hpair (y + 1)) with h | h
  · exact h.2
  · exfalso
    apply cycleMap_orientation_cannot_flip hr f y hy
    simpa only [add_sub_cancel_right] using h.1

/-- The analogous propagation for the reverse orientation. -/
theorem cycleMap_reverse_step_propagates
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (f : ZMod n → ZMod r)
    (hpair : ∀ y, ({f (y - 1), f (y + 1)} : Set (ZMod r)) =
      {f y - 1, f y + 1})
    (y : ZMod n) (hy : f (y + 1) = f y - 1) :
    f ((y + 1) + 1) = f (y + 1) - 1 := by
  rcases cycleMap_local_orientation hr f (y + 1) (hpair (y + 1)) with h | h
  · have htwo : (2 : ZMod r) = 0 := by
      have hback : f y = f (y + 1) - 1 := by
        simpa only [add_sub_cancel_right] using h.1
      have heq : f y = f y - 2 := by
        calc
          f y = f (y + 1) - 1 := hback
          _ = (f y - 1) - 1 := by rw [hy]
          _ = f y - 2 := by ring
      calc
        (2 : ZMod r) = f y - (f y - 2) := by ring
        _ = 0 := by rw [← heq]; simp
    have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp htwo
    have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · exact h.2

/-- A locally cycle-intertwining map has one global orientation.  This is the
coordinate-free core of the cyclic-cover normal form; summing the displayed
step relation gives `f(y)=f(0)±y`. -/
theorem cycleMap_global_orientation
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (f : ZMod n → ZMod r)
    (hpair : ∀ y, ({f (y - 1), f (y + 1)} : Set (ZMod r)) =
      {f y - 1, f y + 1}) :
    (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1) := by
  rcases cycleMap_local_orientation hr f 0 (hpair 0) with hforward | hreverse
  · left
    have hnat : ∀ m : ℕ,
        f ((m : ZMod n) + 1) = f (m : ZMod n) + 1 := by
      intro m
      induction m with
      | zero => simpa using hforward.2
      | succ m ih =>
          have hp := cycleMap_forward_step_propagates hr f hpair
            (m : ZMod n) ih
          simpa [Nat.cast_succ] using hp
    intro y
    simpa only [ZMod.natCast_zmod_val] using hnat y.val
  · right
    have hnat : ∀ m : ℕ,
        f ((m : ZMod n) + 1) = f (m : ZMod n) - 1 := by
      intro m
      induction m with
      | zero => simpa using hreverse.2
      | succ m ih =>
          have hp := cycleMap_reverse_step_propagates hr f hpair
            (m : ZMod n) ih
          simpa [Nat.cast_succ] using hp
    intro y
    simpa only [ZMod.natCast_zmod_val] using hnat y.val

/-! ## Odd-cycle self-blocks -/

/-- A symmetric zero-diagonal matrix commuting entrywise with an odd cycle
is invariant under simultaneous cyclic translation of its two coordinates.
Consequently it is a circulant matrix.  The zero diagonal kills the possible
Hankel (reflection) part of the commutant; oddness ensures that every
anti-diagonal orbit meets the diagonal. -/
theorem oddCycle_selfIntertwiner_is_translationInvariant
    {r : ℕ} [NeZero r] (hr : Odd r)
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hsymm : ∀ x y, H x y = H y x)
    (hdiag : ∀ x, H x x = 0)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1)) :
    ∀ x y, H (x + 1) (y + 1) = H x y := by
  let Δ : ZMod r → ZMod r → ℤ :=
    fun x y ↦ H (x + 1) (y + 1) - H x y
  have hstep (x y : ZMod r) : Δ x y = Δ (x - 1) (y + 1) := by
    dsimp only [Δ]
    have h := hinter x (y + 1)
    rw [show y + 1 - 1 = y by ring] at h
    have htwo : (2 : ZMod r) = 1 + 1 := by norm_num
    have hy2 : y + 1 + 1 = y + 2 := by
      calc
        y + 1 + 1 = y + (1 + 1) := add_assoc _ _ _
        _ = y + 2 := by rw [← htwo]
    rw [hy2] at h
    rw [show x - 1 + 1 = x by ring, hy2] at ⊢
    linear_combination h
  have hiter (x y : ZMod r) : ∀ m : ℕ,
      Δ x y = Δ (x - (m : ZMod r)) (y + (m : ZMod r)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          Δ x y = Δ (x - (m : ZMod r)) (y + (m : ZMod r)) := ih
          _ = Δ ((x - (m : ZMod r)) - 1)
              ((y + (m : ZMod r)) + 1) := hstep _ _
          _ = Δ (x - ((m + 1 : ℕ) : ZMod r))
              (y + ((m + 1 : ℕ) : ZMod r)) := by
                simp only [Nat.cast_add, Nat.cast_one]
                congr 1 <;> ring
  intro x y
  have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
  have hunit : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr hcop
  have hbij : Function.Bijective (fun z : ZMod r ↦ 2 * z) :=
    Finite.injective_iff_bijective.mp hunit.mul_right_injective
  obtain ⟨t, ht⟩ := hbij.surjective (x - y)
  have ht' : t + t = x - y := by simpa [two_mul] using ht
  have hend : x - t = y + t := by
    rw [sub_eq_iff_eq_add]
    calc
      x = (x - y) + y := by abel
      _ = (t + t) + y := by rw [← ht']
      _ = y + t + t := by abel
  have hit := hiter x y t.val
  rw [ZMod.natCast_zmod_val] at hit
  have hzero : Δ (x - t) (y + t) = 0 := by
    rw [← hend]
    simp [Δ, hdiag]
  have : Δ x y = 0 := hit.trans hzero
  exact sub_eq_zero.mp this

end Erdos85
