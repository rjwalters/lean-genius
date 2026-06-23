/-
  The Closed-Form Exponential Diagonal Ramsey Lower Bound (First Moment)

  Open question (prob-method-expectation-oq-02-oq-01):
    "Derive the explicit asymptotic R(k,k) > ... by estimating C(n,k) and choosing n
     optimally, showing the first moment method recovers the classical 2^(k/2) growth."

  The parent entry (prob-method-expectation-oq-02, `RamseyFirstMoment.lean`) proves the
  *implication* form of the Erdős (1947) union bound:

        2 · C(n,k) < 2^(C(k,2))   ⟹   R(k,k) > n,

  but only instantiates it at one numeric point (R(4,4) > 6).  This file closes the gap:
  it turns that criterion into the recognisable closed-form *growth* statement

        n ≤ 2^((k-1)/2)   ⟹   R(k,k) > n,

  kept entirely over ℕ by writing the threshold in its squared, fraction-free form
  `n^2 ≤ 2^(k-1)` (which is exactly `n ≤ 2^((k-1)/2)`).  The arithmetic core is the
  standard estimate

        2 · C(n,k)  <  k! · C(n,k)  =  n^(k underbar)  ≤  n^k  ≤  2^(C(k,2)),

  where the first step uses `2 < k!` (valid for `k ≥ 3`) and `C(n,k) ≥ 1`, the equality is
  `descFactorial = k! · choose`, and the last step squares `n^2 ≤ 2^(k-1)` and uses
  `2 · C(k,2) = k(k-1)`.

  From this we extract the headline exponential growth of the diagonal Ramsey number:

        for j ≥ 3,   R(2j+1, 2j+1) > 2^j,

  i.e. `R(k,k)` grows at least like `(√2)^k`, the classical Erdős lower order — recovered
  purely from the first moment method, with no probability measure.  (We prove the
  exponential *order*; the sharper `(1+o(1))·(k/e)·2^(k/2)` constant is not addressed here.)

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib
import Proofs.RamseyFirstMoment

namespace ProbMethod.RamseyDiagonalGrowth

open Finset ProbMethod.RamseyFirstMoment

variable {n k : ℕ}

/-- `2 · C(k,2) = k · (k-1)`: twice the second binomial coefficient is the falling
    factorial `k(k-1)`.  Proved through `descFactorial`. -/
theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  have h1 : k.descFactorial 2 = 2 * k.choose 2 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; rfl
  have h2 : k.descFactorial 2 = (k - 1) * k := by
    simp [Nat.descFactorial]
  rw [← h1, h2, Nat.mul_comm]

/-- **Arithmetic core.**  The fraction-free `2^((k-1)/2)` threshold `n^2 ≤ 2^(k-1)`
    implies the first-moment Ramsey criterion `2·C(n,k) < 2^(C(k,2))`, for `k ≥ 3` and
    `k ≤ n`.  This is the estimation step the parent entry left open. -/
theorem firstMoment_hyp_of_sq (hk : 3 ≤ k) (hkn : k ≤ n) (hsq : n ^ 2 ≤ 2 ^ (k - 1)) :
    2 * n.choose k < 2 ^ (k.choose 2) := by
  -- `C(n,k) ≥ 1` since `k ≤ n`
  have hcpos : 0 < n.choose k := Nat.choose_pos hkn
  -- `2 < k!` since `k ≥ 3`
  have hfact : 2 < k.factorial := by
    have h6 : (3 : ℕ).factorial ≤ k.factorial := Nat.factorial_le hk
    have h3 : (3 : ℕ).factorial = 6 := by decide
    omega
  -- `2·C(n,k) < k!·C(n,k)`
  have step1 : 2 * n.choose k < k.factorial * n.choose k :=
    Nat.mul_lt_mul_of_pos_right hfact hcpos
  -- `k!·C(n,k) = n^(k underbar) ≤ n^k`
  have hdesc : k.factorial * n.choose k = n.descFactorial k :=
    (Nat.descFactorial_eq_factorial_mul_choose n k).symm
  have hpow : n.descFactorial k ≤ n ^ k := Nat.descFactorial_le_pow n k
  -- `n^k ≤ 2^(C(k,2))`, obtained by squaring `n^2 ≤ 2^(k-1)`
  have hsq2 : (n ^ k) ^ 2 ≤ (2 ^ (k.choose 2)) ^ 2 := by
    calc (n ^ k) ^ 2
        = n ^ (k * 2) := (pow_mul n k 2).symm
      _ = n ^ (2 * k) := by rw [Nat.mul_comm]
      _ = (n ^ 2) ^ k := pow_mul n 2 k
      _ ≤ (2 ^ (k - 1)) ^ k := Nat.pow_le_pow_left hsq k
      _ = 2 ^ ((k - 1) * k) := (pow_mul 2 (k - 1) k).symm
      _ = 2 ^ (2 * k.choose 2) := by
            rw [show (k - 1) * k = 2 * k.choose 2 from by rw [two_mul_choose_two]; ring]
      _ = 2 ^ (k.choose 2 * 2) := by rw [Nat.mul_comm]
      _ = (2 ^ (k.choose 2)) ^ 2 := pow_mul 2 (k.choose 2) 2
  have hnk : n ^ k ≤ 2 ^ (k.choose 2) := by
    by_contra hcon
    push_neg at hcon
    have := Nat.pow_lt_pow_left hcon (show (2 : ℕ) ≠ 0 by norm_num)
    omega
  calc 2 * n.choose k
      < k.factorial * n.choose k := step1
    _ = n.descFactorial k := hdesc
    _ ≤ n ^ k := hpow
    _ ≤ 2 ^ (k.choose 2) := hnk

/-- **Closed-form first-moment Ramsey lower bound.**  If `k ≥ 3`, `k ≤ n` and
    `n^2 ≤ 2^(k-1)` (i.e. `n ≤ 2^((k-1)/2)`), then `K_n` has a 2-coloring with no
    monochromatic `K_k`; equivalently `R(k,k) > n`. -/
theorem ramsey_no_mono_of_sq (hk : 3 ≤ k) (hkn : k ≤ n) (hsq : n ^ 2 ≤ 2 ^ (k - 1)) :
    ∃ c : Coloring n, ∀ K : Finset (Fin n), K.card = k → ¬ Mono c K :=
  first_moment_ramsey (by omega) hkn (firstMoment_hyp_of_sq hk hkn hsq)

/-- For `j ≥ 3`, `2j + 1 ≤ 2^j`: the clique size stays below the vertex count, so the
    closed-form bound applies along the odd diagonal. -/
theorem two_mul_add_one_le_pow (j : ℕ) (hj : 3 ≤ j) : 2 * j + 1 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have h2m : (2 : ℕ) ≤ 2 ^ m := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hsplit : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
      omega

/-- **Exponential growth of the diagonal Ramsey number.**  For every `j ≥ 3`,
    `R(2j+1, 2j+1) > 2^j`: there is a 2-coloring of `K_{2^j}` with no monochromatic
    `K_{2j+1}`.  Writing `k = 2j+1` this is `R(k,k) > 2^((k-1)/2) = (√2)^(k-1)`, so the
    first moment method alone forces `R(k,k)` to grow at least like `(√2)^k`. -/
theorem ramsey_diagonal_growth (j : ℕ) (hj : 3 ≤ j) :
    ∃ c : Coloring (2 ^ j),
      ∀ K : Finset (Fin (2 ^ j)), K.card = 2 * j + 1 → ¬ Mono c K := by
  apply ramsey_no_mono_of_sq
  · omega
  · exact two_mul_add_one_le_pow j hj
  · have heq : (2 ^ j) ^ 2 = 2 ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
    rw [Nat.add_sub_cancel]
    exact le_of_eq heq

/-- Concrete instance of the growth bound: `R(7,7) > 8`.  The first moment method
    produces a 2-coloring of `K_8` with no monochromatic `K_7`
    (here `8^2 = 64 = 2^6 = 2^(7-1)`, the threshold met with equality). -/
theorem ramsey_seven_gt_eight :
    ∃ c : Coloring 8, ∀ K : Finset (Fin 8), K.card = 7 → ¬ Mono c K :=
  ramsey_no_mono_of_sq (by norm_num) (by norm_num) (by decide)

end ProbMethod.RamseyDiagonalGrowth
