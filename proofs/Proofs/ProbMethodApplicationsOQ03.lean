/-
  Probabilistic Method Applications — OQ-03
  Explicit Erdős 1947 exponential lower bound for the diagonal Ramsey number.

  The sibling file `RamseyFirstMoment.lean` proves the first-moment (union-bound)
  Ramsey criterion in *hypothesis form*:

      2 · C(n,k) < 2^(C(k,2))   ⟹   R(k,k) > n

  (`ProbMethod.RamseyFirstMoment.first_moment_ramsey`), together with the single
  concrete instance `R(4,4) > 6`.

  What was still missing — and what the gallery's `erdos_ramsey_lower_bound`
  only stated as a *trivial existence witness* (`∃ n, n ≥ 2^(k/2)` with
  `n := 2^(k/2)`, which says nothing about Ramsey numbers) — is the genuine
  Erdős 1947 conclusion: the diagonal Ramsey number grows **exponentially**.

  This file discharges the counting hypothesis for the clean even-index family
  `k = 2m`, `n = 2^m`, giving the honest theorem

      R(2m, 2m) > 2^m        for all m ≥ 2,

  i.e. an exponential lower bound `R(k,k) > 2^{k/2}` along even `k`.  The proof is
  fully finite and integer-only (no real exponents, no floors): the engine is the
  bound `C(n,k)·k! ≤ n^k` (descending-factorial) against the factorial growth
  `(2m)! > 2^{m+1}`.

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib
import Proofs.RamseyFirstMoment

namespace ProbMethod.ApplicationsOQ03

open Nat Finset

/-! ### Arithmetic building blocks -/

/-- For `m ≥ 2`, the clique size `2m` is at most the vertex count `2^m`. This is the
    side condition `k ≤ n` of the first-moment criterion. -/
theorem two_mul_le_two_pow (m : ℕ) (hm : 2 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hge : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * (n + 1) = 2 * n + 2 := by ring
      _ ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

/-- Factorial growth: `(2m)! > 2^{m+1}` for `m ≥ 2`. This is the slack that beats the
    crude `C(n,k) ≤ n^k` bound and produces the exponential Ramsey lower bound. -/
theorem two_pow_lt_factorial (m : ℕ) (hm : 2 ≤ m) : 2 ^ (m + 1) < (2 * m).factorial := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hstep : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [h1, Nat.factorial_succ, Nat.factorial_succ]; ring_nf
    rw [hstep]
    have hp : 0 < (2 * m + 2) * (2 * m + 1) := by positivity
    have h2 : 2 ≤ (2 * m + 2) * (2 * m + 1) := by nlinarith
    calc 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
      _ ≤ (2 * m + 2) * (2 * m + 1) * 2 ^ (m + 1) := Nat.mul_le_mul_right _ h2
      _ < (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := Nat.mul_lt_mul_of_pos_left ih hp

/-- `C(n,k) · k! ≤ n^k`: the falling factorial `n·(n-1)···(n-k+1)` is at most `n^k`. -/
theorem choose_mul_factorial_le_pow (n k : ℕ) : n.choose k * k.factorial ≤ n ^ k := by
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow n k

/-- Exponent bookkeeping: `C(2m,2) + (m+1) = 2m² + 1`. (`C(2m,2) = 2m² − m`.) -/
theorem choose_two_two_mul (m : ℕ) : (2 * m).choose 2 + (m + 1) = 2 * m * m + 1 := by
  rw [Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; decide
  · have he : 2 * m * (2 * m - 1) = 2 * (m * (2 * m - 1)) := by ring
    rw [he, Nat.mul_div_cancel_left _ (by norm_num)]
    have hsub : 2 * m - 1 + 1 = 2 * m := by omega
    nlinarith [hsub]

/-! ### The first-moment counting hypothesis for `k = 2m`, `n = 2^m` -/

/-- The Erdős counting inequality `2·C(2^m, 2m) < 2^{C(2m,2)}` holds for every `m ≥ 2`.
    This is exactly the hypothesis of `first_moment_ramsey`, here discharged in closed
    form rather than assumed. -/
theorem ramsey_count_bound (m : ℕ) (hm : 2 ≤ m) :
    2 * (2 ^ m).choose (2 * m) < 2 ^ ((2 * m).choose 2) := by
  -- power identity: (2^m)^(2m) = 2^(2 m²)
  have hNK : (2 ^ m) ^ (2 * m) = 2 ^ (2 * m * m) := by
    rw [← pow_mul]; congr 1; ring
  have hfact := two_pow_lt_factorial m hm
  have hA := choose_mul_factorial_le_pow (2 ^ m) (2 * m)
  -- compare both sides after multiplying through by (2m)!
  have key : (2 * (2 ^ m).choose (2 * m)) * (2 * m).factorial
      < 2 ^ ((2 * m).choose 2) * (2 * m).factorial := by
    have hL : (2 * (2 ^ m).choose (2 * m)) * (2 * m).factorial ≤ 2 ^ (2 * m * m + 1) := by
      calc (2 * (2 ^ m).choose (2 * m)) * (2 * m).factorial
          = 2 * ((2 ^ m).choose (2 * m) * (2 * m).factorial) := by ring
        _ ≤ 2 * (2 ^ m) ^ (2 * m) := by gcongr
        _ = 2 * 2 ^ (2 * m * m) := by rw [hNK]
        _ = 2 ^ (2 * m * m + 1) := by rw [pow_succ]; ring
    have hR : 2 ^ (2 * m * m + 1) < 2 ^ ((2 * m).choose 2) * (2 * m).factorial := by
      calc 2 ^ (2 * m * m + 1)
          = 2 ^ ((2 * m).choose 2 + (m + 1)) := by rw [← choose_two_two_mul]
        _ = 2 ^ ((2 * m).choose 2) * 2 ^ (m + 1) := by rw [pow_add]
        _ < 2 ^ ((2 * m).choose 2) * (2 * m).factorial :=
            Nat.mul_lt_mul_of_pos_left hfact (by positivity)
    exact lt_of_le_of_lt hL hR
  exact lt_of_mul_lt_mul_right key (Nat.zero_le _)

/-! ### Explicit exponential Ramsey lower bound -/

open ProbMethod.RamseyFirstMoment in
/-- **Erdős 1947 (explicit, even index).**  For every `m ≥ 2` there is a 2-coloring of the
    edges of the complete graph `K_{2^m}` containing **no** monochromatic clique on `2m`
    vertices.  Equivalently, the diagonal Ramsey number satisfies

        R(2m, 2m) > 2^m,

    an exponential lower bound `R(k,k) > 2^{k/2}` along even `k`.  Unlike the previous
    trivial-witness placeholder, this genuinely certifies that diagonal Ramsey numbers grow
    exponentially. -/
theorem ramsey_exponential_lower_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ c : Coloring (2 ^ m), ∀ K : Finset (Fin (2 ^ m)), K.card = 2 * m → ¬ Mono c K :=
  first_moment_ramsey (by omega) (two_mul_le_two_pow m hm) (ramsey_count_bound m hm)

open ProbMethod.RamseyFirstMoment in
/-- Concrete instance `m = 2`: `R(4,4) > 4`.  (The sibling file's `ramsey_four_gt_six`
    gives the sharper `R(4,4) > 6` by hand; this is the value produced uniformly by the
    exponential family.) -/
theorem ramsey_four_gt_four :
    ∃ c : Coloring (2 ^ 2), ∀ K : Finset (Fin (2 ^ 2)), K.card = 2 * 2 → ¬ Mono c K :=
  ramsey_exponential_lower_bound 2 (by norm_num)

end ProbMethod.ApplicationsOQ03
