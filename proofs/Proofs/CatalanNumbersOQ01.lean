/-
Catalan numbers: the linear (two-term) recurrence  (n+2)·Cₙ₊₁ = 2(2n+1)·Cₙ

Source: Open question from the catalan-numbers gallery family
Status: VERIFIED (0 axioms, 0 sorries)

`Nat.catalan n` is the `n`-th Catalan number, counting (among many things) the
binary trees with `n` internal nodes, the Dyck paths of length `2n`, and the
triangulations of an `(n+2)`-gon.

Mathlib (`Mathlib/Combinatorics/Enumerative/Catalan.lean`) records:

  * `catalan_succ'`                  — the quadratic Segner *convolution* recurrence
                                       Cₙ₊₁ = Σ_{i≤n} Cᵢ·C_{n−i};
  * `catalan_eq_centralBinom_div`    — the closed form Cₙ = C(2n,n)/(n+1);
  * `succ_mul_catalan_eq_centralBinom`— the bridge (n+1)·Cₙ = C(2n,n).

What Mathlib does *not* state is the classical **linear** recurrence

      (n+2)·Cₙ₊₁ = 2·(2n+1)·Cₙ,

which computes each Catalan number from its immediate predecessor in O(1) work,
in contrast to the O(n) Segner convolution `catalan_succ'`. We fill that gap.

The proof bridges through the central binomial coefficients, combining the two
Mathlib identities

  (n+1)·Cₙ              = C(2n,n)                     (`succ_mul_catalan_eq_centralBinom`)
  (n+1)·C(2(n+1),n+1)   = 2(2n+1)·C(2n,n)             (`Nat.succ_mul_centralBinom_succ`)

and cancelling the common factor `n+1`.

We prove:
1. `centralBinom_succ_eq`        — the bridge C(2(n+1),n+1) = 2(2n+1)·Cₙ
2. `catalan_linear_recurrence`   — the headline linear recurrence
and demonstrate it computing C₄ = 14 and C₅ = 42 from their predecessors alone.
-/

import Mathlib

open Nat

namespace CatalanNumbersOQ01

/-- **Bridge.** The central binomial coefficient at `n+1` equals `2(2n+1)` times
the `n`-th Catalan number:

  `C(2(n+1), n+1) = 2·(2n+1)·Cₙ`.

This is the key step turning the central-binomial recurrence into a Catalan
recurrence. We prove it by cancelling the factor `n+1` from
`Nat.succ_mul_centralBinom_succ`. -/
theorem centralBinom_succ_eq (n : ℕ) :
    (n + 1).centralBinom = 2 * (2 * n + 1) * catalan n := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 from n.succ_pos)
  -- Goal: (n+1)·C(2(n+1),n+1) = (n+1)·(2(2n+1)·Cₙ).
  -- LHS is 2(2n+1)·C(2n,n); rewriting C(2n,n) = (n+1)·Cₙ matches the RHS.
  rw [Nat.succ_mul_centralBinom_succ, ← succ_mul_catalan_eq_centralBinom]
  ring

/-- **Catalan linear recurrence.** Each Catalan number is determined by its
immediate predecessor:

  `(n+2)·Cₙ₊₁ = 2·(2n+1)·Cₙ`.

Unlike the Segner convolution `catalan_succ'` (which sums over all earlier
Catalan numbers), this two-term recurrence advances the sequence in O(1) work
per step. -/
theorem catalan_linear_recurrence (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  rw [h, centralBinom_succ_eq]

/-- The recurrence computes `C₄ = 14` from `C₃ = 5` alone (no convolution). -/
example : catalan 4 = 14 := by
  have h := catalan_linear_recurrence 3
  norm_num [catalan_three] at h
  omega

/-- One more step: `C₅ = 42` from `C₄ = 14`. -/
example : catalan 5 = 42 := by
  have h4 : catalan 4 = 14 := by
    have h := catalan_linear_recurrence 3
    norm_num [catalan_three] at h
    omega
  have h := catalan_linear_recurrence 4
  norm_num [h4] at h
  omega

end CatalanNumbersOQ01
