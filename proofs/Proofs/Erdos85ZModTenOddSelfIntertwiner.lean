import Proofs.Erdos85ZModTenSameParityIntertwiner

/-!
# Odd-difference invariance for C10 self-intertwiners

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The usual loopless self-intertwiner theorem controls the doubling-image
(even-difference) checkerboard.  If the cycle superdiagonal also vanishes,
shift the second matrix coordinate by one.  The shifted matrix is loopless,
so the same theorem controls the complementary odd-difference checkerboard.
-/

namespace Erdos85

/-- A C10 self-intertwiner whose cycle superdiagonal vanishes depends only on
coordinate difference also on the odd checkerboard. -/
theorem zmodTen_selfIntertwiner_eq_of_sub_eq_of_odd_of_superdiag_zero
    (H : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hsuper : ∀ x, H x (x + 1) = 0)
    {x y x' y' : ZMod 10}
    (hodd : ¬ ZModTenEvenOffset (y - x))
    (hsub : y - x = y' - x') :
    H x y = H x' y' := by
  let H' : Matrix (ZMod 10) (ZMod 10) ℤ := fun i j => H i (j + 1)
  have hdiag' : ∀ z, H' z z = 0 := by
    intro z
    exact hsuper z
  have hinter' : ∀ i j,
      H' (i - 1) j + H' (i + 1) j =
        H' i (j + 1) + H' i (j - 1) := by
    intro i j
    dsimp [H']
    simpa only [show j - 1 + 1 = j by ring,
      show j + 1 + 1 = (j + 1) + 1 by ring,
      show j + 1 - 1 = j by ring] using hinter i (j + 1)
  have hoddHalf : ∀ z : ZMod 10, ¬ ZModTenEvenOffset z →
      z - 1 ∈ Set.range (fun t : ZMod 10 => 2 * t) := by
    decide
  have hhalf : (y - 1) - x ∈ Set.range (fun t : ZMod 10 => 2 * t) := by
    have := hoddHalf (y - x) hodd
    simpa only [show (y - x) - 1 = (y - 1) - x by ring] using this
  have hsub' : (y - 1) - x = (y' - 1) - x' := by
    linear_combination hsub
  have heq := selfIntertwiner_eq_of_sub_eq_of_mem_range_two
    H' hdiag' hinter' hhalf hsub'
  change H x ((y - 1) + 1) = H x' ((y' - 1) + 1) at heq
  simpa using heq

end Erdos85

#print axioms Erdos85.zmodTen_selfIntertwiner_eq_of_sub_eq_of_odd_of_superdiag_zero
