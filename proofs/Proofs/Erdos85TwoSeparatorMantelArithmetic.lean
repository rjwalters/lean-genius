import Proofs.Erdos85TwoSeparatorMinimumCutResidue

/-!
# Two-separator near-Mantel arithmetic

The low set attached to either minimum-cut shore has a split-coclique upper
bound `e <= p(q-1-p)`. For even `q`, this is at most `(q^2-2q)/4`, which
is strictly below the minimum-cut near-Mantel lower `(q^2-4)/4` for `q>=8`.
-/

namespace Erdos85

theorem four_mul_splitProduct_le_even_pred_square_int (q p m : ℤ) (hq : q=2*m) :
  4*p*(q-1-p) ≤ q*q-2*q := by
  have hne : 2*p-(q-1) ≠ 0 := by
    intro h
    have heq : 2*p = q-1 := sub_eq_zero.mp h
    omega
  have hs : (1:ℤ) ≤ (2*p-(q-1))^2 :=
    (one_le_sq_iff_one_le_abs _).2 (Int.one_le_abs hne)
  nlinarith

theorem false_of_even_split_edge_upper_and_nearMantel_lower_int (q p e m : ℤ) (hq : 8≤q) (heven:q=2*m)
 (hu:e≤p*(q-1-p)) (hl:q*q-4≤4*e) : False := by
  have hb := four_mul_splitProduct_le_even_pred_square_int q p m heven
  nlinarith

theorem false_of_even_split_edge_upper_and_nearMantel_lower (q p e : ℕ) (hq:8≤q) (heven:Even q)
 (hp:p≤q-1) (hu:e≤p*(q-1-p)) (hl:q*q-4≤4*e) : False := by
  obtain ⟨m, hm⟩ := heven
  have hqZ : (8:ℤ) ≤ q := by exact_mod_cast hq
  have hmZ : (q:ℤ) = (m:ℤ) + m := by exact_mod_cast hm
  have hevenZ : (q:ℤ) = 2*(m:ℤ) := by rw [hmZ]; ring
  have huZ : (e:ℤ) ≤ p * (q-1-p) := by
    calc
      (e:ℤ) ≤ ((p * (q-1-p) : ℕ) : ℤ) := by exact_mod_cast hu
      _ = (p:ℤ) * (q-1-p) := by
        rw [Nat.cast_mul, Nat.cast_sub hp,
          Nat.cast_sub (by omega : 1 ≤ q)]
        norm_num
  have hlZ : (q:ℤ)*(q:ℤ)-4 ≤ 4*(e:ℤ) := by
    have hfour : 4 ≤ q*q := by nlinarith
    exact_mod_cast hl
  exact false_of_even_split_edge_upper_and_nearMantel_lower_int
    q p e m hqZ hevenZ huZ hlZ


#print axioms four_mul_splitProduct_le_even_pred_square_int
#print axioms false_of_even_split_edge_upper_and_nearMantel_lower_int
#print axioms false_of_even_split_edge_upper_and_nearMantel_lower

end Erdos85
