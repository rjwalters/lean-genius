/-
# Cube Root of 2 OQ-05: the n-th root of a prime is irrational

## Open Question
Generalize the irrationality of ∛2 (and √2) to: for every prime `p` and every degree
`n ≥ 2`, the real n-th root `p ^ (1/n)` is irrational. The base entry proves the single
case `p = 2, n = 3`; this entry proves the whole two-parameter family at once.

## Approach
The engine is Mathlib's `irrational_nrt_of_n_not_dvd_multiplicity`: if `x ^ n = m` (an
integer) and `n ∤ multiplicity p m`, then `x` is irrational. Take `x = p ^ (1/n)` and
`m = p`. Then:
  * `x ^ n = p` because `(p ^ (1/n)) ^ n = p ^ (n⁻¹ · n) = p ^ 1 = p` (real rpow, `p ≥ 0`).
  * `multiplicity (p:ℤ) (p:ℤ) = 1` (`multiplicity_self`), and `1 % n = 1 ≠ 0` whenever
    `n ≥ 2`, so `n` does not divide the multiplicity.
Hence `p ^ (1/n)` is irrational. Specializing `n = 3` recovers ∛p irrational for every
prime — in particular ∛2, the base entry — and `n = 2` recovers `Nat.Prime.irrational_sqrt`.
Specializing `p = 2` gives the irrationality of every n-th root of 2.

Mathlib has `Nat.Prime.irrational_sqrt` (square roots only) but no n-th-root analogue;
this fills that gap.

Sorry-free and axiom-free.
-/
import Mathlib

namespace CubeRoot2IrrationalOQ05

open Real

/-- **The n-th root of a prime is irrational.** For a prime `p` and any degree `n ≥ 2`,
`p ^ (1/n)` is not rational. This is the two-parameter generalization of both
`irrational_sqrt_two` (`p = 2, n = 2`) and the gallery's ∛2 result (`p = 2, n = 3`).

Proof: with `x = p ^ (n⁻¹)` we have `x ^ n = p` (rpow composition, `p ≥ 0`), and
`multiplicity (p:ℤ) (p:ℤ) = 1` is not divisible by `n ≥ 2`, so
`irrational_nrt_of_n_not_dvd_multiplicity` applies. -/
theorem irrational_rpow_inv_prime {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    Irrational ((p : ℝ) ^ ((n : ℝ)⁻¹)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  -- x ^ n = p, as a real equal to the integer cast of p
  have hxr : ((p : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = ((p : ℤ) : ℝ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul hp0,
      inv_mul_cancel₀ hn0, Real.rpow_one]
    push_cast
    ring
  -- multiplicity p p = 1, and 1 % n = 1 ≠ 0 since n ≥ 2
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine irrational_nrt_of_n_not_dvd_multiplicity n hpz p hxr ?_
  rw [multiplicity_self, Nat.one_mod_eq_one.mpr (by omega)]
  exact one_ne_zero

/-- **The cube root of a prime is irrational** (`n = 3`). The direct generalization of the
base entry: ∛p is irrational for every prime `p`, not just `p = 2`. -/
theorem irrational_cbrt_prime {p : ℕ} (hp : p.Prime) :
    Irrational ((p : ℝ) ^ ((3 : ℝ)⁻¹)) :=
  irrational_rpow_inv_prime hp (by norm_num)

/-- **∛2 is irrational** — the base entry recovered as the `p = 2` case of
`irrational_cbrt_prime`. -/
theorem irrational_cbrt_two : Irrational ((2 : ℝ) ^ ((3 : ℝ)⁻¹)) := by
  have := irrational_cbrt_prime (p := 2) (by norm_num)
  simpa using this

/-- **∛3 is irrational.** -/
theorem irrational_cbrt_three : Irrational ((3 : ℝ) ^ ((3 : ℝ)⁻¹)) := by
  have := irrational_cbrt_prime (p := 3) (by norm_num)
  simpa using this

/-- **Every n-th root of 2 (n ≥ 2) is irrational** — the `p = 2` slice of the family. -/
theorem irrational_rpow_inv_two {n : ℕ} (hn : 2 ≤ n) :
    Irrational ((2 : ℝ) ^ ((n : ℝ)⁻¹)) := by
  have := irrational_rpow_inv_prime (p := 2) (by norm_num) hn
  simpa using this

end CubeRoot2IrrationalOQ05
