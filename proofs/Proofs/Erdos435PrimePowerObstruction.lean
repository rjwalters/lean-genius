/-
Erdős Problem #435 — Prime-Power Obstruction (companion to Erdos435Problem.lean)

This file formalizes the number-theoretic fact underlying the restriction in
Erdős #435 to integers `n` that are NOT prime powers (Parts V and VI of the
main file `Erdos435Problem.lean`, previously recorded only as prose).

For `n = p^k` a prime power, every "middle" binomial coefficient `C(n, j)`
(`1 ≤ j < n`) is divisible by `p`. Hence the gcd of the generators
`{C(n,1), …, C(n,n-1)}` is divisible by `p`, so it is ≠ 1, the numerical
semigroup they generate is not cofinite, and no Frobenius number exists.
This is exactly why the Hwang–Song formula (`hwang_song_theorem`) is stated
only for non-prime-powers.

Status: build-pending — the gallery build environment was unavailable this
session (circular `.lake` symlink → OOM; Aristotle MCP returning "Resource not
found"). The proof relies only on Mathlib's Kummer-type identity
`Nat.factorization_choose_prime_pow` and standard `ordProj` divisibility, both
present in the pinned Mathlib v4.26.0.
-/
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Erdos435.PrimePowerObstruction

/-- **Prime-power obstruction (core lemma).**
If `p` is prime and `1 ≤ j < p^k`, then `p ∣ C(p^k, j)`.

By Kummer's identity the `p`-adic valuation of `C(p^k, j)` equals
`k - v_p(j)`; since `0 < j < p^k` we have `v_p(j) < k`, so the valuation is
positive and `p` divides the coefficient. -/
theorem prime_pow_dvd_choose {p k j : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hj : 1 ≤ j) (hjn : j < p ^ k) : p ∣ (p ^ k).choose j := by
  have hj0 : j ≠ 0 := by omega
  have hjle : j ≤ p ^ k := le_of_lt hjn
  -- Kummer: v_p(C(p^k, j)) = k - v_p(j)
  have hfact : ((p ^ k).choose j).factorization p = k - j.factorization p :=
    Nat.factorization_choose_prime_pow hp.prime hjle hj0
  -- v_p(j) < k, otherwise p^k ∣ j would contradict j < p^k
  have hjfact_lt : j.factorization p < k := by
    by_contra h
    push_neg at h
    have hdvd : p ^ k ∣ j := dvd_trans (pow_dvd_pow p h) (Nat.ordProj_dvd j p)
    have : p ^ k ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  -- hence the valuation of the binomial coefficient is positive
  have hval_pos : 0 < ((p ^ k).choose j).factorization p := by
    rw [hfact]; omega
  -- positive valuation ⟹ p divides the coefficient
  have hstep : p ^ ((p ^ k).choose j).factorization p ∣ (p ^ k).choose j :=
    Nat.ordProj_dvd _ p
  have hpdvd : p ∣ p ^ ((p ^ k).choose j).factorization p :=
    dvd_pow_self p (by omega)
  exact dvd_trans hpdvd hstep

/-- **Common prime factor of all generators.**
For a prime power `n = p^k` (`k ≥ 1`), the prime `p` divides every generator
`C(n, j)` with `1 ≤ j ≤ n-1`. This is the per-generator statement behind the
gcd obstruction. -/
theorem prime_dvd_all_generators {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ p ^ k - 1) : p ∣ (p ^ k).choose j := by
  have hp1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  exact prime_pow_dvd_choose hp hk hj (by omega)

/-- **The generators of a prime power share a common factor `> 1`.**
For `n = p^k`, the gcd of `{C(n,1), …, C(n,n-1)}` is divisible by `p`, hence
is not `1`. A numerical semigroup whose generators have gcd `≠ 1` has infinite
complement, so no Frobenius number exists — precisely why Erdős #435 excludes
prime powers. -/
theorem generators_gcd_ne_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (Finset.Icc 1 (p ^ k - 1)).gcd (fun j => (p ^ k).choose j) ≠ 1 := by
  intro hgcd
  have hpdvd : p ∣ (Finset.Icc 1 (p ^ k - 1)).gcd (fun j => (p ^ k).choose j) := by
    apply Finset.dvd_gcd
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact prime_dvd_all_generators hp hk j hj.1 hj.2
  rw [hgcd] at hpdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hpdvd)

end Erdos435.PrimePowerObstruction
