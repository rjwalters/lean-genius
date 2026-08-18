import Mathlib

/-! # Two four-cycles leave room for at most one triangle -/

namespace Erdos85

/-- Four distinct parts of sizes `4,4,3,3` cannot occur in a partition of
sixteen whose remaining parts all have size at least three.  The four named
parts consume fourteen points, leaving an impossible remainder of two. -/
theorem orderSixteen_partition_false_of_two_four_two_three
    {I : Type*} [Fintype I] [DecidableEq I]
    (size : I → ℕ)
    (hsum : ∑ i, size i = 16)
    (hmin : ∀ i, 3 ≤ size i)
    {a b c d : I}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : size a = 4) (hb : size b = 4)
    (hc : size c = 3) (hd : size d = 3) : False := by
  classical
  let S : Finset I := {a, b, c, d}
  let R : Finset I := Finset.univ \ S
  have hSsum : ∑ i ∈ S, size i = 14 := by
    simp [S, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd]
  have hsplit : (∑ i ∈ R, size i) + (∑ i ∈ S, size i) = ∑ i, size i := by
    simpa [R] using Finset.sum_sdiff (f := size) (Finset.subset_univ S)
  have hRsum : ∑ i ∈ R, size i = 2 := by
    rw [hSsum, hsum] at hsplit
    omega
  by_cases hR : R.Nonempty
  · obtain ⟨e, he⟩ := hR
    have hle : size e ≤ ∑ i ∈ R, size i := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) he
    have hemin := hmin e
    rw [hRsum] at hle
    omega
  · have : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    rw [this] at hRsum
    simp at hRsum

end Erdos85
