import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Tactic

/-!
# Euler totient OQ-01 → OQ-02: the Carmichael function on prime powers

The parent chain (`euler-totient`) studies Euler's totient `φ`. Its OQ-01-OQ-02 asks to

> *prove `λ(2ᵏ) = 2ᵏ⁻² for k ≥ 3` and related Carmichael function identities in Lean,*

where `λ` is the Carmichael function (reduced totient), the exponent of the unit group
`(ℤ/nℤ)ˣ`. Mathlib defines `λ` (`ArithmeticFunction.Carmichael`) and proves its prime-power
values; this file packages them as the requested identities, with `0` axioms.

The point of `λ` is that it is the *smallest* universal exponent: `aᵏ ≡ 1 (mod n)` for all
units `a` iff `λ(n) ∣ k`, which can be far smaller than `φ(n)`. For `n = 2ᵏ` (`k ≥ 3`) the
unit group is `ℤ/2 × ℤ/2ᵏ⁻²` (not cyclic), so `λ(2ᵏ) = 2ᵏ⁻² = φ(2ᵏ)/2`, strictly less than
`φ`. For odd prime powers the unit group is cyclic, so `λ(pᵏ) = φ(pᵏ)`.

## Main results

* `carmichael_two_pow` : `λ(2ᵏ) = 2ᵏ⁻²` for `k ≥ 3` (the OQ's target).
* `two_mul_carmichael_two_pow` : `2·λ(2ᵏ) = φ(2ᵏ)` for `k ≥ 3` (`λ` is half the totient).
* `carmichael_odd_prime_pow` : `λ(pᵏ) = φ(pᵏ)` for odd primes `p`.
* `carmichael_dvd_totient` / `pow_carmichael` : `λ(n) ∣ φ(n)` and `aᵏ = 1` at `k = λ(n)`.
* `carmichael_eight`, `carmichael_sixteen` : `λ(8) = 2`, `λ(16) = 4`.
-/

namespace EulerTotientOQ01OQ02

open ArithmeticFunction Nat

/-- **`λ(2ᵏ) = 2ᵏ⁻²` for `k ≥ 3`** (the OQ's target). The unit group `(ℤ/2ᵏℤ)ˣ` is
    `ℤ/2 × ℤ/2ᵏ⁻²`, whose exponent is `2ᵏ⁻²` — strictly less than `φ(2ᵏ) = 2ᵏ⁻¹`.
    (Mathlib: `carmichael_two_pow_of_ne_two`.) -/
theorem carmichael_two_pow {k : ℕ} (hk : 3 ≤ k) :
    Carmichael (2 ^ k) = 2 ^ (k - 2) :=
  carmichael_two_pow_of_ne_two (by omega)

/-- **`λ(2ᵏ) = φ(2ᵏ)/2` for `k ≥ 3`**, stated as `2·λ(2ᵏ) = φ(2ᵏ)`: the Carmichael function
    is exactly half the totient for the high powers of two, reflecting the non-cyclic
    `ℤ/2 × ℤ/2ᵏ⁻²` structure. (Mathlib: `two_mul_carmichael_two_pow_of_three_le_eq_totient`.) -/
theorem two_mul_carmichael_two_pow {k : ℕ} (hk : 3 ≤ k) :
    2 * Carmichael (2 ^ k) = (2 ^ k).totient :=
  two_mul_carmichael_two_pow_of_three_le_eq_totient hk

/-- **`λ(pᵏ) = φ(pᵏ)` for an odd prime `p`.** The unit group of an odd prime power is cyclic,
    so its exponent equals its order — the Carmichael and totient functions coincide.
    (Mathlib: `carmichael_pow_of_prime_ne_two`.) -/
theorem carmichael_odd_prime_pow {p : ℕ} (k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    Carmichael (p ^ k) = (p ^ k).totient :=
  carmichael_pow_of_prime_ne_two k hp hodd

/-- **`λ(n) ∣ φ(n)`**: the Carmichael function always divides the totient (Euler's theorem
    factors through the smaller exponent `λ`). -/
theorem carmichael_dvd_totient (n : ℕ) : Carmichael n ∣ n.totient :=
  ArithmeticFunction.carmichael_dvd_totient n

/-- **Universal exponent.** Every unit `a` modulo `n` satisfies `a^{λ(n)} = 1`. -/
theorem pow_carmichael {n : ℕ} (a : (ZMod n)ˣ) : a ^ Carmichael n = 1 :=
  ArithmeticFunction.pow_carmichael a

/-- `λ(8) = 2`. -/
theorem carmichael_eight : Carmichael 8 = 2 := by
  have h := carmichael_two_pow (k := 3) (by norm_num)
  norm_num at h
  exact h

/-- `λ(16) = 4`. -/
theorem carmichael_sixteen : Carmichael 16 = 4 := by
  have h := carmichael_two_pow (k := 4) (by norm_num)
  norm_num at h
  exact h

end EulerTotientOQ01OQ02
