/-
# Chebyshev's lower bound: explicit linear bounds c₁·n ≤ ψ(n) ≤ c₂·n (OQ-02-OQ-01)

The parent file `ChebyshevBoundsOQ02` develops the second Chebyshev function
`ψ(n) = ∑_{m ≤ n} Λ(m)` in von Mangoldt form and proves **Legendre's identity**
`log(n!) = ∑_{d ≤ n} Λ(d)·⌊n/d⌋`, together with the easy estimate `ψ(n) ≤ log(n!)`
(which is only `O(n log n)`).  Legendre's identity is the elementary engine behind the
two-sided Chebyshev estimate `ψ(n) = Θ(n)`, but the parent stops short of the explicit
linear bounds.

This file proves the **lower bound** `c₁·n ≤ ψ(n)`, the harder half of Chebyshev's
theorem and an explicit `TODO` in Mathlib's own `Mathlib/NumberTheory/Chebyshev.lean`
("Prove Chebyshev's lower bound").  The argument is the classical one via the central
binomial coefficient `C(n) = (2n choose n)`:

* `log_centralBinom_eq_sum`:  `log C(n) = ∑_{d≤2n} Λ(d)·(⌊2n/d⌋ − 2⌊n/d⌋)`, obtained by
  applying Legendre's identity to `(2n)! = C(n)·(n!)²`.
* `centralBinom_log_le_psi`:  `log C(n) ≤ ψ(2n)`.  Each Legendre coefficient
  `⌊2n/d⌋ − 2⌊n/d⌋` lies in `{0,1}`, so each summand is at most `Λ(d)`.
* Combined with Mathlib's `Nat.four_pow_le_two_mul_self_mul_centralBinom` (`4ⁿ ≤ 2n·C(n)`):
  `psi_two_mul_ge_sub_log`:  `n·log 4 − log(2n) ≤ ψ(2n)`, and after absorbing the
  logarithm (`2n ≤ 2ⁿ`):  `psi_two_mul_ge_linear`:  `n·log 2 ≤ ψ(2n)`.
* `chebyshevPsi_lower_linear`:  for `m ≥ 2`,  `(log 2 / 3)·m ≤ ψ(m)`.

Bridging the parent's `chebyshevPsi` to Mathlib's `Chebyshev.psi`
(`chebyshevPsi_eq_psi`) imports the matching **upper** bound `ψ(n) ≤ (log 4 + 4)·n`
(`Chebyshev.psi_le_const_mul_self`), giving the full two-sided explicit estimate
`chebyshev_psi_bounds`:  `(log 2 / 3)·m ≤ ψ(m) ≤ (log 4 + 4)·m` for `m ≥ 2`.

`#print axioms chebyshev_psi_bounds` lists only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib
import Proofs.ChebyshevBoundsOQ02

open Finset ArithmeticFunction

namespace ChebyshevBoundsOQ02OQ01

open ChebyshevBoundsOQ02

/-- **Floor identity** `⌊2n/d⌋ ≤ 2⌊n/d⌋ + 1` (natural-number division), the arithmetic
core of the central-binomial argument: the Legendre coefficient `⌊2n/d⌋ − 2⌊n/d⌋` never
exceeds `1`. -/
theorem two_mul_div_le (n d : ℕ) : 2 * n / d ≤ 2 * (n / d) + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hlt : 2 * n < d * (2 * (n / d) + 2) := by
      have h := Nat.div_add_mod n d
      have h2 := Nat.mod_lt n hd
      nlinarith [h, h2]
    have := Nat.div_lt_of_lt_mul hlt
    omega

/-- **Legendre expansion of the central binomial coefficient.**
`log C(n) = ∑_{d=1}^{2n} Λ(d)·(⌊2n/d⌋ − 2⌊n/d⌋)`, from `(2n)! = C(n)·(n!)²` and Legendre's
identity for `log(2n)!` and `log(n!)`. -/
theorem log_centralBinom_eq_sum (n : ℕ) :
    Real.log (Nat.centralBinom n) =
      ∑ d ∈ Finset.Icc 1 (2 * n),
        Λ d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by
  -- (2n)! = C(n) · n! · n!
  have hfact : (Nat.centralBinom n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) =
      (Nat.factorial (2 * n) : ℝ) := by
    have hnat : Nat.centralBinom n * Nat.factorial n * Nat.factorial n = Nat.factorial (2 * n) := by
      have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
      rw [show 2 * n - n = n by omega] at h
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact h
    exact_mod_cast hnat
  -- log C(n) = log (2n)! − 2·log n!
  have hlogcb : Real.log (Nat.centralBinom n) =
      Real.log (Nat.factorial (2 * n) : ℝ) - 2 * Real.log (Nat.factorial n : ℝ) := by
    have hpf : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hpc : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
    rw [← hfact, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hlogcb, log_factorial_eq_sum (2 * n)]
  -- extend Legendre for n! to the range Icc 1 (2n) (the extra terms vanish: n/d = 0)
  have hLn : Real.log (Nat.factorial n : ℝ) =
      ∑ d ∈ Finset.Icc 1 (2 * n), Λ d * ((n / d : ℕ) : ℝ) := by
    rw [log_factorial_eq_sum n]
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx hx'
      rw [Finset.mem_Icc] at hx
      simp only [Finset.mem_Icc, not_and, not_le] at hx'
      have hlt : n < x := hx' hx.1
      rw [Nat.div_eq_of_lt hlt]; simp
  rw [hLn, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **Key inequality:** `log C(n) ≤ ψ(2n)`.  Every Legendre coefficient
`⌊2n/d⌋ − 2⌊n/d⌋` is `0` or `1`, so each summand is at most `Λ(d)`, and the sum of `Λ(d)`
over `d ≤ 2n` is exactly `ψ(2n)`. -/
theorem centralBinom_log_le_psi (n : ℕ) :
    Real.log (Nat.centralBinom n) ≤ chebyshevPsi (2 * n) := by
  rw [log_centralBinom_eq_sum, chebyshevPsi]
  refine Finset.sum_le_sum fun d _ => ?_
  have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
  have hcoeff : ((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ) ≤ 1 := by
    have hcast : ((2 * n / d : ℕ) : ℝ) ≤ 2 * ((n / d : ℕ) : ℝ) + 1 := by
      exact_mod_cast two_mul_div_le n d
    linarith
  nlinarith [mul_nonneg hΛ
    (by linarith : (0 : ℝ) ≤ 1 - (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)))]

/-- `n·log 4 − log(2n) ≤ ψ(2n)` for `n ≥ 1`, from `4ⁿ ≤ 2n·C(n)`. -/
theorem psi_two_mul_ge_sub_log {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n) ≤ chebyshevPsi (2 * n) := by
  have hcb : (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2n0 : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hcb0 : (Nat.centralBinom n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos n).ne'
  have hpos2 : (0 : ℝ) < 2 * (n : ℝ) * (Nat.centralBinom n : ℝ) := by
    have : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
    positivity
  have hlog : Real.log ((4 : ℝ) ^ n) ≤ Real.log (2 * (n : ℝ) * (Nat.centralBinom n : ℝ)) :=
    (Real.log_le_log_iff (by positivity) hpos2).mpr hcb
  rw [Real.log_pow, Real.log_mul h2n0 hcb0] at hlog
  have hcbpsi := centralBinom_log_le_psi n
  linarith

/-- Helper: `2m ≤ 2ᵐ` for `m ≥ 1`. -/
theorem two_mul_le_two_pow {m : ℕ} (hm : 1 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have hik := ih hk
      have h2k : 2 ≤ 2 ^ k := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [pow_succ]; omega

/-- `log(2n) ≤ n·log 2` for `n ≥ 1` (since `2n ≤ 2ⁿ`). -/
theorem log_two_mul_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (2 * n) ≤ (n : ℝ) * Real.log 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h : (2 * (n : ℝ)) ≤ (2 : ℝ) ^ n := by exact_mod_cast two_mul_le_two_pow hn
  calc Real.log (2 * n) ≤ Real.log ((2 : ℝ) ^ n) :=
        (Real.log_le_log_iff (mul_pos (by norm_num) hnpos) (by positivity)).mpr h
    _ = (n : ℝ) * Real.log 2 := Real.log_pow 2 n

/-- **Chebyshev's lower bound, even case:** `n·log 2 ≤ ψ(2n)` for `n ≥ 1`. -/
theorem psi_two_mul_ge_linear {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log 2 ≤ chebyshevPsi (2 * n) := by
  have h1 := psi_two_mul_ge_sub_log hn
  have h2 := log_two_mul_le hn
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have key : (n : ℝ) * Real.log 4 = 2 * ((n : ℝ) * Real.log 2) := by rw [hlog4]; ring
  rw [key] at h1
  linarith

/-- **Chebyshev's lower bound:** `(log 2 / 3)·m ≤ ψ(m)` for `m ≥ 2`.  The constant
`log 2 / 3 ≈ 0.231` is explicit; the odd/even split costs only the factor `3` in the
denominator. -/
theorem chebyshevPsi_lower_linear {m : ℕ} (hm : 2 ≤ m) :
    Real.log 2 / 3 * (m : ℝ) ≤ chebyshevPsi m := by
  have hmono : chebyshevPsi (2 * (m / 2)) ≤ chebyshevPsi m := chebyshevPsi_mono (by omega)
  have hlin := psi_two_mul_ge_linear (n := m / 2) (by omega)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hm3 : (m : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) := by
    have : m ≤ 3 * (m / 2) := by omega
    exact_mod_cast this
  have step : Real.log 2 / 3 * (m : ℝ) ≤ ((m / 2 : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [mul_nonneg hlog2 (by linarith : (0 : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) - m), hlog2, hm3]
  linarith

/-- Bridge: the parent's `chebyshevPsi n` equals Mathlib's `Chebyshev.psi n`. -/
theorem chebyshevPsi_eq_psi (n : ℕ) : chebyshevPsi n = Chebyshev.psi (n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, chebyshevPsi]
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  · intro x hx hx'
    rw [Finset.mem_Icc] at hx
    simp only [Finset.mem_Icc, not_and, not_le] at hx'
    have : x = 0 := by omega
    rw [this]; simp

/-- **Chebyshev's upper bound** (imported from Mathlib): `ψ(n) ≤ (log 4 + 4)·n`. -/
theorem chebyshevPsi_le_linear (n : ℕ) :
    chebyshevPsi n ≤ (Real.log 4 + 4) * (n : ℝ) := by
  rw [chebyshevPsi_eq_psi]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

/-- **Two-sided explicit Chebyshev bounds:**
`(log 2 / 3)·m ≤ ψ(m) ≤ (log 4 + 4)·m` for `m ≥ 2` — the elementary `ψ(m) = Θ(m)`, with
both constants explicit. -/
theorem chebyshev_psi_bounds {m : ℕ} (hm : 2 ≤ m) :
    Real.log 2 / 3 * (m : ℝ) ≤ chebyshevPsi m ∧
      chebyshevPsi m ≤ (Real.log 4 + 4) * (m : ℝ) :=
  ⟨chebyshevPsi_lower_linear hm, chebyshevPsi_le_linear m⟩

end ChebyshevBoundsOQ02OQ01
