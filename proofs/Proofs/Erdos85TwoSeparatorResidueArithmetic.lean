import Proofs.Erdos85DefectMaxEdgeConnectivity

/-!
# Two-separator residue arithmetic

For two complementary shores left after deleting two vertices, the total
order is `q^2 - 2`. If minimum-cut arithmetic gives each shore residue
`+1` or `-1`, only the pair of `-1` residues is compatible when `q >= 8`.
-/

namespace Erdos85

theorem twoSeparator_both_residue_sub_one (q s t : ℕ) (hq : 8 ≤ q)
    (hsum : s + t = q * q - 2)
    (hs : s % q = 1 ∨ s % q = q - 1)
    (ht : t % q = 1 ∨ t % q = q - 1) :
    s % q = q - 1 ∧ t % q = q - 1 := by
  have hqpos : 0 < q := by omega
  have htwo : 2 ≤ q * q := by nlinarith
  have hmod : (s % q + t % q) % q = q - 2 := by
    calc
      (s % q + t % q) % q = (s + t) % q := by
        exact (Nat.add_mod s t q).symm
      _ = (q * q - 2) % q := by rw [hsum]
      _ = q - 2 := by
        have hqle : q ≤ q * q := by
          calc
            q = q * 1 := by simp
            _ ≤ q * q := Nat.mul_le_mul_left q (by omega)
        have hdecomp : q * q - 2 = q * (q - 1) + (q - 2) := by
          calc
            q * q - 2 = (q * q - q) + (q - 2) := by omega
            _ = q * (q - 1) + (q - 2) := by
              rw [Nat.mul_sub_left_distrib]
              simp
        rw [hdecomp, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (by omega : q - 2 < q)]
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · rw [hs, ht] at hmod
    have : (1 + 1) % q = 2 := Nat.mod_eq_of_lt (by omega)
    rw [this] at hmod
    omega
  · rw [hs, ht] at hmod
    have : (1 + (q - 1)) % q = 0 := by
      rw [show 1 + (q - 1) = q by omega, Nat.mod_self]
    rw [this] at hmod
    omega
  · rw [hs, ht] at hmod
    have : ((q - 1) + 1) % q = 0 := by
      rw [show (q - 1) + 1 = q by omega, Nat.mod_self]
    rw [this] at hmod
    omega
  · exact ⟨hs, ht⟩


#print axioms twoSeparator_both_residue_sub_one

end Erdos85
