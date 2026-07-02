/-
  The Converse of Lagrange's Theorem Fails: A₄ Has No Subgroup of Order 6
  (lagrange-theorem-oq-08-oq-01)

  Lagrange's theorem says the order of every subgroup divides the order of the
  group. Its parent entry (lagrange-theorem-oq-08) records the *partial converse*
  supplied by Cauchy's theorem: for every **prime** divisor `p` of `|G|` there is
  a subgroup of order `p`. This file supplies the canonical *sharpness witness*
  showing the converse genuinely fails for composite divisors:

    **The alternating group A₄ = alternatingGroup (Fin 4) has order 12, the
    number 6 divides 12, yet A₄ has no subgroup of order 6.**

  This is the standard textbook counterexample to the naive converse of Lagrange.

  ## Proof

  Suppose `H ≤ A₄` had `Nat.card H = 6`. Since `|A₄| = 12`, `H` has index
  `12 / 6 = 2`. An index-two subgroup contains every square (`sq_mem_of_index_two`).
  Every 3-cycle `g` has order 3, so `g = g⁴ = (g²)²` is a square, hence lies in `H`.
  There are exactly `2!·C(4,3) = 8` three-cycles in A₄
  (`AlternatingGroup.card_of_cycleType_singleton`). All 8 must lie in `H`, forcing
  `Nat.card H ≥ 8 > 6` — a contradiction.

  ## Main results

  * `card_A4` — `Nat.card (alternatingGroup (Fin 4)) = 12`.
  * `no_subgroup_card_six` — no subgroup of A₄ has order 6.
  * `six_dvd_card_A4` — 6 divides `|A₄|`.
  * `converse_lagrange_fails` — there is a divisor of `|A₄|` that is not the order
    of any subgroup (the negation of the naive converse of Lagrange).

  Verified, 0 axioms (beyond Lean's foundational propext/Classical.choice/Quot.sound).
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

namespace LagrangeTheoremOQ08OQ01

open Equiv Equiv.Perm
open scoped Finset

/-- The alternating group on four letters has order 12. -/
theorem card_A4 : Nat.card (alternatingGroup (Fin 4)) = 12 :=
  alternatingGroup.card_of_card_eq_four (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])

/-- There are exactly eight 3-cycles in A₄ (`2! · C(4,3) = 8`). -/
theorem card_threeCycles :
    #{g : alternatingGroup (Fin 4) | (g.val).cycleType = ({3} : Multiset ℕ)} = 8 := by
  rw [AlternatingGroup.card_of_cycleType_singleton (by decide) (by decide), Fintype.card_fin]
  decide

/-- **The converse of Lagrange's theorem fails.** The alternating group A₄ has
order 12 and `6 ∣ 12`, but A₄ has no subgroup of order 6. -/
theorem no_subgroup_card_six (H : Subgroup (alternatingGroup (Fin 4))) :
    Nat.card H ≠ 6 := by
  intro hHcard
  -- `H` has index two, since `|A₄| = |H| · index = 12`.
  have hindex2 : H.index = 2 := by
    have hmul := Subgroup.card_mul_index H
    rw [hHcard, card_A4] at hmul
    omega
  -- Every 3-cycle lies in `H`: it has order 3, so it is the square `(g²)²`, and
  -- squares live in the index-two subgroup `H`.
  have hbound : 8 ≤ Nat.card H := by
    classical
    rw [← card_threeCycles, Nat.card_eq_fintype_card, Fintype.card_subtype (· ∈ H)]
    apply Finset.card_le_card
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    -- `hg : g.val.cycleType = {3}`; goal `g ∈ H`.
    have hord : orderOf (g.val) = 3 := by
      rw [← Equiv.Perm.lcm_cycleType, hg]; decide
    have h1 : (g.val) ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have hg3 : g ^ 3 = 1 := by
      rw [← SetLike.coe_eq_coe]; push_cast; exact h1
    have hg2 : g ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hindex2 g
    have hval : (g ^ 2) ^ 2 = g := by
      calc (g ^ 2) ^ 2 = g ^ 3 * g := by rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ]
        _ = 1 * g := by rw [hg3]
        _ = g := one_mul g
    exact hval ▸ pow_mem hg2 2
  rw [hHcard] at hbound
  omega

/-- 6 divides the order of A₄. -/
theorem six_dvd_card_A4 : 6 ∣ Nat.card (alternatingGroup (Fin 4)) := by
  rw [card_A4]; norm_num

/-- **Naive converse of Lagrange is false.** There is a divisor of `|A₄|` that is
not the order of any subgroup of A₄. -/
theorem converse_lagrange_fails :
    ∃ d : ℕ, d ∣ Nat.card (alternatingGroup (Fin 4)) ∧
      ¬ ∃ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H = d :=
  ⟨6, six_dvd_card_A4, fun ⟨H, hH⟩ => no_subgroup_card_six H hH⟩

end LagrangeTheoremOQ08OQ01
