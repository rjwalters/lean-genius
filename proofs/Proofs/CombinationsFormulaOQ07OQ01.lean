import Mathlib

/-
# The Subset-of-a-Subset Identity (Trinomial Revision)

## Open Question OQ-07-OQ-01

Vandermonde's convolution (OQ-07) is the *additive* binomial identity

  C(m + n, k) = ∑_{i+j=k} C(m, i) · C(n, j),

obtained by splitting a `k`-subset of `m + n` objects according to how many
come from the first block.  Its multiplicative companion is the
**subset-of-a-subset identity** (also called *trinomial revision* or the
*committee–subcommittee identity*):

  C(n, k) · C(k, m) = C(n, m) · C(n − m, k − m),   for m ≤ k ≤ n.

Both sides count the same thing two ways: the number of ways to choose a
`k`-element committee from `n` people **and then** an `m`-element subcommittee
from that committee.  Counting committee-first gives `C(n,k)·C(k,m)`; counting
subcommittee-first (pick the `m` subcommittee members from all `n`, then fill
the remaining `k − m` committee seats from the `n − m` leftovers) gives
`C(n,m)·C(n−m,k−m)`.

Mathlib provides Vandermonde (`Nat.add_choose_eq`) but **not** this product
identity.  We prove it from the single factorial fact

  `Nat.choose_mul_factorial_mul_factorial : k ≤ n → C(n,k)·k!·(n−k)! = n!`

by clearing denominators: both sides, multiplied by `m!·(k−m)!·(n−k)!`,
collapse to `n!`.

## Results

1. `choose_mul_choose` — the identity itself, `C(n,k)·C(k,m) = C(n,m)·C(n−m,k−m)`.
2. `choose_mul_choose_of_le'` — the symmetric "central blocks" form
   `C(n,k)·C(k,m) = C(n,m)·C(n−m,n−k)` (using `C(n−m,k−m)=C(n−m,n−k)`).
3. `mul_choose_eq` — the absorption / committee-chair corollary
   `k·C(n,k) = n·C(n−1,k−1)` (the `m = 1` slice).
4. `choose_mul_choose_comm` — commuting the two selection orders:
   `C(n,k)·C(k,m) = C(n,m)·C(n−m,k−m)` is symmetric under `k ↔ n − k + m`… here
   we record the plain numeric instance `C(5,3)·C(3,2) = C(5,2)·C(3,1)`.

## Mathematical Context

Trinomial revision is one of the five "core" binomial identities in Graham,
Knuth & Patashnik (*Concrete Mathematics*, eq. 5.21).  It is the engine behind
hypergeometric term manipulation and behind the absorption identity used to
prove `∑ k·C(n,k) = n·2^{n−1}`.  Unlike Vandermonde, it requires no summation:
it is a pointwise factorial identity, which is exactly why the factorial route
below is short and avoids any induction.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ01

open Nat

/-- **Subset-of-a-subset identity (trinomial revision).**
    For `m ≤ k ≤ n`, choosing a `k`-committee then an `m`-subcommittee equals
    choosing the `m`-subcommittee first then the remaining `k − m` seats:
    `C(n, k) · C(k, m) = C(n, m) · C(n − m, k − m)`. -/
theorem choose_mul_choose {n k m : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) :
    n.choose k * k.choose m = n.choose m * (n - m).choose (k - m) := by
  have hmn : m ≤ n := hmk.trans hkn
  have hkm_nm : k - m ≤ n - m := Nat.sub_le_sub_right hkn m
  have hsub : (n - m) - (k - m) = n - k := by omega
  -- The three "denominator" factorials we clear; their product is nonzero.
  set D : ℕ := m ! * (k - m)! * (n - k)! with hDdef
  -- Key factorial collapses.
  have keyL : k.choose m * m ! * (k - m)! = k ! := choose_mul_factorial_mul_factorial hmk
  have keyN : n.choose k * k ! * (n - k)! = n ! := choose_mul_factorial_mul_factorial hkn
  have keyM : n.choose m * m ! * (n - m)! = n ! := choose_mul_factorial_mul_factorial hmn
  have keyNM : (n - m).choose (k - m) * (k - m)! * (n - k)! = (n - m)! := by
    have h := choose_mul_factorial_mul_factorial hkm_nm
    rwa [hsub] at h
  -- LHS · D = n!.
  have lhsD : (n.choose k * k.choose m) * D = n ! := by
    have hrw : (n.choose k * k.choose m) * D
        = (k.choose m * m ! * (k - m)!) * (n.choose k * (n - k)!) := by
      rw [hDdef]; ring
    rw [hrw, keyL, ← keyN]; ring
  -- RHS · D = n!.
  have rhsD : (n.choose m * (n - m).choose (k - m)) * D = n ! := by
    have hrw : (n.choose m * (n - m).choose (k - m)) * D
        = ((n - m).choose (k - m) * (k - m)! * (n - k)!) * (n.choose m * m !) := by
      rw [hDdef]; ring
    rw [hrw, keyNM, ← keyM]; ring
  -- D ≠ 0, so cancel it.
  have hD : 0 < D := by
    rw [hDdef]
    exact Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _)) (factorial_pos _)
  exact Nat.eq_of_mul_eq_mul_right hD (lhsD.trans rhsD.symm)

/-- **Central-blocks form.** Using the symmetry `C(n−m, k−m) = C(n−m, n−k)`,
    the leftover seats can be counted from the top: `C(n,k)·C(k,m) =
    C(n,m)·C(n−m, n−k)`. -/
theorem choose_mul_choose_of_le' {n k m : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) :
    n.choose k * k.choose m = n.choose m * (n - m).choose (n - k) := by
  have hkm_nm : k - m ≤ n - m := Nat.sub_le_sub_right hkn m
  have hsymm : (n - m).choose (k - m) = (n - m).choose (n - k) := by
    have : (n - m) - (k - m) = n - k := by omega
    rw [← this, Nat.choose_symm hkm_nm]
  rw [choose_mul_choose hmk hkn, hsymm]

/-- **Absorption / committee-chair identity** (`m = 1` slice).
    Selecting a `k`-committee with a designated chair two ways gives
    `k · C(n, k) = n · C(n − 1, k − 1)`. -/
theorem mul_choose_eq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * n.choose k = n * (n - 1).choose (k - 1) := by
  have h := choose_mul_choose hk hkn
  -- h : C(n,k) · C(k,1) = C(n,1) · C(n-1, k-1)
  rw [Nat.choose_one_right, Nat.choose_one_right] at h
  -- h : C(n,k) · k = n · C(n-1, k-1)
  rw [Nat.mul_comm]
  exact h

/-- Numeric sanity check of the headline identity:
    `C(5,3)·C(3,2) = 10·3 = 30 = 10·3 = C(5,2)·C(3,1)`. -/
example : (5 : ℕ).choose 3 * (3 : ℕ).choose 2 = (5 : ℕ).choose 2 * (5 - 2 : ℕ).choose (3 - 2) := by
  decide

/-- Numeric sanity check of absorption: `3·C(5,3) = 30 = 5·C(4,2) = 5·6`. -/
example : 3 * (5 : ℕ).choose 3 = 5 * (5 - 1 : ℕ).choose (3 - 1) := by
  decide

end CombinationsFormulaOQ07OQ01
