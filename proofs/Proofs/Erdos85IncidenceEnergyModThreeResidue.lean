import Mathlib

/-!
# Strict incidence energy from the mod-three excess residue

If every closed-star cut has size `q + 2e_x`, then total cut energy is
`q^3 + 2 Σe_x`.  The triangle double count gives `Σe_x ≡ q (mod 3)`;
the two possible nonzero binary residues force one or two units of excess.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Sum the pointwise decomposition `δ_x=q+2e_x` at square order. -/
theorem sum_eq_cube_add_two_mul_sum_of_pointwise_excess
    {V : Type*} [Fintype V] (q : ℕ) (δ e : V → ℕ)
    (hcard : Fintype.card V = q * q)
    (hδ : ∀ x, δ x = q + 2 * e x) :
    ∑ x, δ x = q * q * q + 2 * ∑ x, e x := by
  simp_rw [hδ]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [hcard, mul_assoc, mul_comm, mul_left_comm]

/-- Residue one forces at least one unit of total excess. -/
theorem one_le_of_modEq_three_of_mod_eq_one
    {s q : ℕ} (hmod : Nat.ModEq 3 s q) (hq : q % 3 = 1) :
    1 ≤ s := by
  change s % 3 = q % 3 at hmod
  rw [hq] at hmod
  omega

/-- Residue two forces at least two units of total excess. -/
theorem two_le_of_modEq_three_of_mod_eq_two
    {s q : ℕ} (hmod : Nat.ModEq 3 s q) (hq : q % 3 = 2) :
    2 ≤ s := by
  change s % 3 = q % 3 at hmod
  rw [hq] at hmod
  omega

/-- If `q ≡ 1 (mod 3)`, the mod-three excess makes the cubic energy bound
strict by at least two. -/
theorem cube_add_two_le_sum_of_pointwise_excess_mod_one
    {V : Type*} [Fintype V] (q : ℕ) (δ e : V → ℕ)
    (hcard : Fintype.card V = q * q)
    (hδ : ∀ x, δ x = q + 2 * e x)
    (hmod : Nat.ModEq 3 (∑ x, e x) q)
    (hqmod : q % 3 = 1) :
    q * q * q + 2 ≤ ∑ x, δ x := by
  rw [sum_eq_cube_add_two_mul_sum_of_pointwise_excess
    q δ e hcard hδ]
  have hpos := one_le_of_modEq_three_of_mod_eq_one hmod hqmod
  omega

/-- If `q ≡ 2 (mod 3)`, the mod-three excess makes the cubic energy bound
strict by at least four. -/
theorem cube_add_four_le_sum_of_pointwise_excess_mod_two
    {V : Type*} [Fintype V] (q : ℕ) (δ e : V → ℕ)
    (hcard : Fintype.card V = q * q)
    (hδ : ∀ x, δ x = q + 2 * e x)
    (hmod : Nat.ModEq 3 (∑ x, e x) q)
    (hqmod : q % 3 = 2) :
    q * q * q + 4 ≤ ∑ x, δ x := by
  rw [sum_eq_cube_add_two_mul_sum_of_pointwise_excess
    q δ e hcard hδ]
  have hpos := two_le_of_modEq_three_of_mod_eq_two hmod hqmod
  omega

end

end Erdos85

#print axioms Erdos85.sum_eq_cube_add_two_mul_sum_of_pointwise_excess
#print axioms Erdos85.cube_add_two_le_sum_of_pointwise_excess_mod_one
#print axioms Erdos85.cube_add_four_le_sum_of_pointwise_excess_mod_two
