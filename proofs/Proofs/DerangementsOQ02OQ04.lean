import Mathlib
import Proofs.DerangementsOQ02

/-
  Low-Codimension Fixed-Point Counts (derangements-oq-02-oq-04)

  The parent `derangements-oq-02` proved the partial-derangement count
    S(n,k) = C(n,k) · D(n−k)
  (permutations of `Fin n` with exactly `k` fixed points), together with the two
  extreme "high-codimension" cases:
    S(n,n)   = 1        (`permsWithAllFixed_card_eq_one`, the identity)
    S(n,n−1) = 0        (`permsWithNMinus1Fixed_eq_zero`, impossible).

  This entry continues the table downward, evaluating the next two cases in closed
  form by specialising the main formula at `D(2)=1` and `D(3)=2`:

    S(n,n−2) = C(n,2)        — exactly the transpositions: choose the 2 moved
                               points (C(n,2) ways), and there is a unique
                               derangement of 2 points (the swap);
    S(n,n−3) = 2·C(n,3)      — choose the 3 moved points (C(n,3) ways), each with
                               D(3)=2 derangements (the two 3-cycles).

  Together with the parent this gives the complete top of the fixed-point
  distribution: counts `1, 0, C(n,2), 2·C(n,3), …` for `k = n, n−1, n−2, n−3, …`.
  Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound`; the two
  `decide`s evaluate `D(2)`, `D(3)` by kernel reduction) and `sorry`-free.
-/

namespace DerangementsOQ02OQ04

open Finset Nat PartialDerangements

/-- `D(2) = 1`: the unique derangement of two points is the transposition. -/
theorem numDerangements_two : numDerangements 2 = 1 := by decide

/-- `D(3) = 2`: the two derangements of three points are the two 3-cycles. -/
theorem numDerangements_three : numDerangements 3 = 2 := by decide

/-- **Permutations with exactly `n−2` fixed points are the transpositions.**
`S(n,n−2) = C(n,2)` for `n ≥ 2`: choose the two moved points (`C(n,2)` ways);
the unique derangement of two points (`D(2)=1`) is the swap. -/
theorem card_perms_n_minus_two_fixed {n : ℕ} (hn : 2 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter (fun x => σ x = x)).card = n - 2)).card = n.choose 2 := by
  rw [card_perms_with_kfixed n (n - 2) (Nat.sub_le n 2)]
  have h1 : n - (n - 2) = 2 := by omega
  rw [h1, numDerangements_two, mul_one, Nat.choose_symm hn]

/-- **Permutations with exactly `n−3` fixed points: `S(n,n−3) = 2·C(n,3)` for
`n ≥ 3`.** Choose the three moved points (`C(n,3)` ways); each admits `D(3)=2`
derangements (the two 3-cycles). -/
theorem card_perms_n_minus_three_fixed {n : ℕ} (hn : 3 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter (fun x => σ x = x)).card = n - 3)).card = 2 * n.choose 3 := by
  rw [card_perms_with_kfixed n (n - 3) (Nat.sub_le n 3)]
  have h1 : n - (n - 3) = 3 := by omega
  rw [h1, numDerangements_three, Nat.choose_symm hn, Nat.mul_comm]

end DerangementsOQ02OQ04
