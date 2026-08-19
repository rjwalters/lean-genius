import Proofs.Erdos85ZModEightSameParitySingleIntertwiner

/-!
# Excluding a mixed-parity row-two self-intertwiner on C8

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The residual odd perfect matching left after removing a same-parity
half-turn cannot have either cyclic orientation: the forward orientation is
incompatible with symmetry, while every odd reverse matching contains a
cycle edge.
-/

namespace Erdos85

/-- A symmetric odd-parity perfect matching on `ZMod 8`, avoiding the two
cycle neighbors, cannot have either of the two cyclic orientations. -/
theorem zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    (f : ZMod 8 → ZMod 8)
    (hinvol : ∀ x, f (f x) = x)
    (hodd : ∀ x, ¬ ZModEightEvenOffset (f x - x))
    (havoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1)
    (horient : (∀ x, f (x + 1) = f x + 1) ∨
      (∀ x, f (x + 1) = f x - 1)) : False := by
  rcases horient with hfor | hrev
  · have hformula : ∀ y : ZMod 8, f y = f 0 + y := by
      intro y
      have hind : ∀ n : ℕ,
          f (n : ZMod 8) = f 0 + (n : ZMod 8) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Nat.cast_succ, hfor, ih]
            ring
      simpa only [ZMod.natCast_zmod_val] using hind y.val
    have hdouble : f 0 + f 0 = 0 := by
      have hi := hinvol 0
      rw [hformula] at hi
      simpa using hi
    have heven : ZModEightEvenOffset (f 0) := by
      have hfinite : ∀ z : ZMod 8,
          z + z = 0 → ZModEightEvenOffset z := by decide
      exact hfinite (f 0) hdouble
    exact (hodd 0) (by simpa using heven)
  · have hformula : ∀ y : ZMod 8, f y = f 0 - y := by
      intro y
      have hind : ∀ n : ℕ,
          f (n : ZMod 8) = f 0 - (n : ZMod 8) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Nat.cast_succ, hrev, ih]
            ring
      simpa only [ZMod.natCast_zmod_val] using hind y.val
    have hf0odd : ¬ ZModEightEvenOffset (f 0) := by
      simpa using hodd 0
    have hex : ∃ x : ZMod 8, f 0 - x = x - 1 ∨ f 0 - x = x + 1 := by
      have hfinite : ∀ z : ZMod 8, ¬ ZModEightEvenOffset z →
          ∃ x : ZMod 8, z - x = x - 1 ∨ z - x = x + 1 := by decide
      exact hfinite (f 0) hf0odd
    obtain ⟨x, hx | hx⟩ := hex
    · exact (havoid x).1 (by rw [hformula]; exact hx)
    · exact (havoid x).2 (by rw [hformula]; exact hx)

end Erdos85

#print axioms Erdos85.zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
