import Mathlib

/-!
# Endpoint-deletion double count for the switch Gram defect

For a finite bipartite switch incidence census `J`, summing the number of
other switches available at the leaf endpoint of every occurrence counts
twice the leaf collision mass.  The analogous center sum counts twice the
center collision mass.  Their difference is therefore exactly twice the
row/column Gram defect `Delta_J`.

This formalizes `(73rnz_ao)` and supplies the concrete provenance of the
collision term used by the four-leaf `omega_Q` bridge.
-/

namespace Erdos85

/-- Leaf-side degree in a finite bipartite switch census. -/
def switchLeftDegree {L G : Type*} [DecidableEq L] [DecidableEq G]
    (J : Finset (L × G)) (l : L) : ℕ :=
  (J.filter fun e => e.1 = l).card

/-- Residual-center-side degree in a finite bipartite switch census. -/
def switchRightDegree {L G : Type*} [DecidableEq L] [DecidableEq G]
    (J : Finset (L × G)) (g : G) : ℕ :=
  (J.filter fun e => e.2 = g).card

private theorem two_dvd_mul_pred (m : ℕ) : 2 ∣ m * (m - 1) := by
  rcases Nat.even_or_odd m with he | ho
  · exact Dvd.dvd.mul_right he.two_dvd _
  · exact Dvd.dvd.mul_left (Nat.Odd.sub_odd ho odd_one).two_dvd _

private theorem two_mul_choose_two (m : ℕ) :
    2 * Nat.choose m 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (two_dvd_mul_pred m)

/-- Leaf endpoint deletion counts twice the leaf-side unordered switch
collisions. -/
theorem sum_switchLeftDeletion_eq_two_mul_sum_choose
    {L G : Type*} [Fintype L] [DecidableEq L] [DecidableEq G]
    (J : Finset (L × G)) :
    (∑ e ∈ J, (switchLeftDegree J e.1 - 1)) =
      2 * ∑ l : L, Nat.choose (switchLeftDegree J l) 2 := by
  have hmaps : ∀ e ∈ J, e.1 ∈ (Finset.univ : Finset L) := by simp
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    hmaps (fun l : L => switchLeftDegree J l - 1)
  calc
    (∑ e ∈ J, (switchLeftDegree J e.1 - 1)) =
        ∑ l : L, ∑ _e ∈ J.filter (fun e => e.1 = l),
          (switchLeftDegree J l - 1) := by
      simpa using hfiber.symm
    _ = ∑ l : L,
        switchLeftDegree J l * (switchLeftDegree J l - 1) := by
      apply Finset.sum_congr rfl
      intro l _hl
      simp [switchLeftDegree]
    _ = ∑ l : L, 2 * Nat.choose (switchLeftDegree J l) 2 := by
      apply Finset.sum_congr rfl
      intro l _hl
      exact (two_mul_choose_two (switchLeftDegree J l)).symm
    _ = 2 * ∑ l : L, Nat.choose (switchLeftDegree J l) 2 := by
      rw [Finset.mul_sum]

/-- Center endpoint deletion counts twice the center-side unordered switch
collisions. -/
theorem sum_switchRightDeletion_eq_two_mul_sum_choose
    {L G : Type*} [Fintype G] [DecidableEq L] [DecidableEq G]
    (J : Finset (L × G)) :
    (∑ e ∈ J, (switchRightDegree J e.2 - 1)) =
      2 * ∑ g : G, Nat.choose (switchRightDegree J g) 2 := by
  have hmaps : ∀ e ∈ J, e.2 ∈ (Finset.univ : Finset G) := by simp
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    hmaps (fun g : G => switchRightDegree J g - 1)
  calc
    (∑ e ∈ J, (switchRightDegree J e.2 - 1)) =
        ∑ g : G, ∑ _e ∈ J.filter (fun e => e.2 = g),
          (switchRightDegree J g - 1) := by
      simpa using hfiber.symm
    _ = ∑ g : G,
        switchRightDegree J g * (switchRightDegree J g - 1) := by
      apply Finset.sum_congr rfl
      intro g _hg
      simp [switchRightDegree]
    _ = ∑ g : G, 2 * Nat.choose (switchRightDegree J g) 2 := by
      apply Finset.sum_congr rfl
      intro g _hg
      exact (two_mul_choose_two (switchRightDegree J g)).symm
    _ = 2 * ∑ g : G, Nat.choose (switchRightDegree J g) 2 := by
      rw [Finset.mul_sum]

/-- **Exact endpoint-deletion Gram identity (`73rnz_ao`).**  The integer
oriented endpoint-deletion census is twice the leaf-minus-center collision
defect. -/
theorem switchEndpointDeletion_eq_two_mul_gramDelta
    {L G : Type*} [Fintype L] [Fintype G]
    [DecidableEq L] [DecidableEq G] (J : Finset (L × G)) :
    (∑ e ∈ J, (((switchLeftDegree J e.1 - 1 : ℕ) : ℤ) -
        ((switchRightDegree J e.2 - 1 : ℕ) : ℤ))) =
      2 * ((∑ l : L, (Nat.choose (switchLeftDegree J l) 2 : ℕ) : ℤ) -
        ∑ g : G, (Nat.choose (switchRightDegree J g) 2 : ℕ) : ℤ) := by
  rw [Finset.sum_sub_distrib]
  have hleft :
      (∑ e ∈ J, ((switchLeftDegree J e.1 - 1 : ℕ) : ℤ)) =
        2 * ∑ l : L, ((Nat.choose (switchLeftDegree J l) 2 : ℕ) : ℤ) := by
    norm_cast
    exact sum_switchLeftDeletion_eq_two_mul_sum_choose J
  have hright :
      (∑ e ∈ J, ((switchRightDegree J e.2 - 1 : ℕ) : ℤ)) =
        2 * ∑ g : G, ((Nat.choose (switchRightDegree J g) 2 : ℕ) : ℤ) := by
    norm_cast
    exact sum_switchRightDeletion_eq_two_mul_sum_choose J
  rw [hleft, hright]
  push_cast
  ring

/-- Over `F₂`, the row-minus-column Gram defect is the sum of its leaf and
center collision masses. -/
theorem switchGramDelta_f2_eq_leaf_add_centerCollision
    {L G : Type*} [Fintype L] [Fintype G]
    [DecidableEq L] [DecidableEq G] (J : Finset (L × G)) :
    ((∑ l : L, Nat.choose (switchLeftDegree J l) 2 : ℕ) : ZMod 2) -
        ((∑ g : G, Nat.choose (switchRightDegree J g) 2 : ℕ) : ZMod 2) =
      ((∑ l : L, Nat.choose (switchLeftDegree J l) 2 : ℕ) : ZMod 2) +
        ((∑ g : G, Nat.choose (switchRightDegree J g) 2 : ℕ) : ZMod 2) := by
  have hneg (x : ZMod 2) : -x = x := by
    have hnegOne : -(1 : ZMod 2) = 1 := by decide
    calc
      -x = (-1) * x := by rw [neg_one_mul]
      _ = 1 * x := by rw [hnegOne]
      _ = x := one_mul x
  rw [sub_eq_add_neg, hneg]

end Erdos85

#print axioms Erdos85.sum_switchLeftDeletion_eq_two_mul_sum_choose
#print axioms Erdos85.sum_switchRightDeletion_eq_two_mul_sum_choose
#print axioms Erdos85.switchEndpointDeletion_eq_two_mul_gramDelta
#print axioms Erdos85.switchGramDelta_f2_eq_leaf_add_centerCollision
