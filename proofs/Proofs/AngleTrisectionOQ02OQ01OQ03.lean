/-
  Angle Trisection - OQ-02 / sub-01 / sub-03:
  The p-group Galois → power-of-p degree criterion (general prime)

  The parent `AngleTrisectionOQ02OQ01` proves, for the prime `2`, that a
  2-group Galois group forces the minimal-polynomial degree to be a power
  of 2 — the algebraic core of the impossibility of angle trisection.

  The argument never used anything special about `2`: it rests only on
  `natDegree ∣ |Gal|` together with `IsPGroup.iff_card`.  This file lifts
  the result to an **arbitrary prime `p`**:

      Gal(minpoly ℚ α) is a p-group  ⟹  natDegree(minpoly ℚ α) = p^k,

  and records the contrapositive non-constructibility criterion plus the
  concrete degree-3 obstruction behind the 60° trisection (cos 20° has
  minimal degree 3, which is not a power of 2).

  Parent: AngleTrisectionOQ02OQ01.lean (natDegree_dvd_card_gal, reused here)
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ01

open Polynomial AngleTrisectionOQ02OQ01

namespace AngleTrisectionOQ02OQ01OQ03

/-- **p-group Galois ⟹ degree divides a power of p.**
    Generalizes `galois_2group_implies_degree_pow2` to any prime `p`:
    `natDegree ∣ |Gal| = p^n`. -/
theorem galois_pgroup_implies_degree_pow_p (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime) (hGal : IsPGroup p (minpoly ℚ α).Gal) :
    ∃ n : ℕ, (minpoly ℚ α).natDegree ∣ p ^ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hirr := minpoly.irreducible hα
  have hdvd := natDegree_dvd_card_gal hirr
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hGal
  exact ⟨n, hn ▸ hdvd⟩

/-- **p-group Galois ⟹ degree IS a power of p.**
    Strengthens the divisibility to an equality via `Nat.dvd_prime_pow`. -/
theorem galois_pgroup_implies_degree_is_pow_p (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime) (hGal : IsPGroup p (minpoly ℚ α).Gal) :
    ∃ k : ℕ, (minpoly ℚ α).natDegree = p ^ k := by
  obtain ⟨n, hdvd⟩ := galois_pgroup_implies_degree_pow_p α hα hp hGal
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨m, hm⟩

/-- **Non-constructibility criterion (contrapositive).**
    If the minimal-polynomial degree of `α` is not a power of the prime `p`,
    then `Gal(minpoly ℚ α)` is not a p-group. -/
theorem not_pgroup_of_degree_ne_pow_p (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime)
    (h : ∀ k : ℕ, (minpoly ℚ α).natDegree ≠ p ^ k) :
    ¬ IsPGroup p (minpoly ℚ α).Gal := by
  intro hGal
  obtain ⟨k, hk⟩ := galois_pgroup_implies_degree_is_pow_p α hα hp hGal
  exact h k hk

/-- **The degree-3 obstruction.**
    An algebraic real whose minimal polynomial has degree `3` cannot have a
    2-group Galois group — this is precisely the obstruction making the 60°
    angle impossible to trisect (`cos 20°` has minimal degree `3`, and `3`
    is not a power of `2`). -/
theorem degree_three_not_2group (α : ℝ) (hα : IsIntegral ℚ α)
    (h3 : (minpoly ℚ α).natDegree = 3) :
    ¬ IsPGroup 2 (minpoly ℚ α).Gal := by
  refine not_pgroup_of_degree_ne_pow_p α hα Nat.prime_two (fun k hk => ?_)
  rw [h3] at hk
  -- `3 = 2 ^ k` is impossible: `2^0 = 1`, `2^1 = 2`, and `2^k ≥ 4` for `k ≥ 2`.
  have h2k : 2 ^ k ≠ 3 := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k <;> decide
    · have : 4 ≤ 2 ^ k := by
        calc (4 : ℕ) = 2 ^ 2 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
      omega
  exact h2k hk.symm

end AngleTrisectionOQ02OQ01OQ03
