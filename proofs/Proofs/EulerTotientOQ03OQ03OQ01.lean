import Mathlib

/-
# Closed Form for the GCD–Totient Defect Factor

## Open Question OQ-03-OQ-03-OQ-01

The parent entry `EulerTotientOQ03OQ03` sharpens super-multiplicativity of Euler's totient
to the exact identity

  `φ(a) · φ(b) · gcd(a,b) / φ(gcd(a,b)) = φ(ab)`,

identifying the **defect factor** `gcd(a,b) / φ(gcd(a,b)) ≥ 1` as the precise measure of the
gap between `φ(a)·φ(b)` and `φ(ab)`.  Its open question asks:

> Does the exact defect factor `gcd(a,b) / φ(gcd(a,b))` admit a clean closed form in terms
> of the shared prime factors of `a` and `b` — e.g. `∏_{p | gcd} p/(p-1)` for squarefree
> `gcd` — and can this be formalized?

## The answer

Yes, and in the *strongest* form: the closed form holds for **every** positive `n`, not just
squarefree ones.  Working in `ℚ`,

  `n / φ(n) = ∏_{p ∈ n.primeFactors} p / (p - 1)`.

This is Euler's product formula `φ(n)/n = ∏ (1 - 1/p)` read as a statement about the
reciprocal defect ratio.  Specialising `n := gcd(a,b)` gives the defect factor of the
parent's identity in closed product form (`defect_factor_gcd`).

For **squarefree** `d` — the case the open question singles out — there is the additional
crisp fact that `φ(d)` is *itself* the product of `p - 1`:

  `φ(d) = ∏_{p ∈ d.primeFactors} (p - 1)`   (`totient_squarefree`),

because a squarefree number is exactly the product of its distinct prime factors
(`Nat.prod_primeFactors_of_squarefree`).  Both the numerator `d = ∏ p` and the totient
`φ(d) = ∏ (p-1)` are then products over the same prime set, and the ratio is `∏ p/(p-1)`.

## Proof architecture

The engine is Mathlib's `Nat.totient_mul_prod_primeFactors`:

  `φ(n) · ∏_{p ∈ n.primeFactors} p = n · ∏_{p ∈ n.primeFactors} (p - 1)`.

Casting this `ℕ`-identity into `ℚ` and dividing (both `φ(n)` and `∏ (p-1)` are nonzero for
`n > 0`, since every prime factor is `≥ 2`) yields `n / φ(n) = (∏ p) / (∏ (p-1))`, and
`Finset.prod_div_distrib` rewrites the right side as `∏ p/(p-1)`.  The squarefree totient
formula cancels `∏ p` (positive) from the same identity after substituting `∏ p = d`.

## Axioms: 0 | Sorries: 0
-/

open Nat Finset

namespace EulerTotientOQ03OQ03OQ01

/-! ### The engine (Mathlib's product form of Euler's formula) -/

/-- Mathlib's product form of Euler's totient formula, restated as the foundation:
`φ(n) · ∏_{p | n} p = n · ∏_{p | n} (p - 1)`. -/
theorem totient_mul_prod (n : ℕ) :
    φ n * ∏ p ∈ n.primeFactors, p = n * ∏ p ∈ n.primeFactors, (p - 1) :=
  Nat.totient_mul_prod_primeFactors n

/-! ### Auxiliary positivity facts over the prime factors -/

/-- Every prime factor, cast to `ℚ`, has `p - 1 ≠ 0` (as `p ≥ 2`). -/
theorem cast_sub_one_ne_zero {n p : ℕ} (hp : p ∈ n.primeFactors) :
    (p : ℚ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.ne')

/-- The product `∏_{p | n} ((p : ℚ) - 1)` is nonzero. -/
theorem prod_sub_one_ne_zero (n : ℕ) :
    ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => cast_sub_one_ne_zero hp

/-- Casting `∏_{p | n} (p - 1)` from `ℕ` to `ℚ` distributes the truncated subtraction into
the honest subtraction `(p : ℚ) - 1`, because each prime factor is `≥ 1`. -/
theorem cast_prod_sub_one (n : ℕ) :
    ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ) = ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-! ### The closed form for the defect ratio (general `n`) -/

/-- **The defect ratio in closed product form**, for every positive `n`:

  `n / φ(n) = ∏_{p ∈ n.primeFactors} p / (p - 1)`.

This is Euler's product formula, read as the reciprocal defect ratio.  It requires no
squarefree hypothesis. -/
theorem defect_ratio (n : ℕ) (hn : 0 < n) :
    (n : ℚ) / φ n = ∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
  have hφ : (φ n : ℚ) ≠ 0 := by
    have : 0 < φ n := Nat.totient_pos.mpr hn
    positivity
  have hden : ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) ≠ 0 := prod_sub_one_ne_zero n
  -- cast the ℕ engine identity into ℚ
  have keyQ : (φ n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ)
      = (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
    have h2 : ((φ n * ∏ p ∈ n.primeFactors, p : ℕ) : ℚ)
        = ((n * ∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ) := by exact_mod_cast totient_mul_prod n
    rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, cast_prod_sub_one n] at h2
  rw [Finset.prod_div_distrib, div_eq_div_iff hφ hden]
  linear_combination -keyQ

/-! ### The defect factor of the parent identity -/

/-- **The parent's defect factor in closed form.**  For `a, b` not both zero, the exact
super-multiplicativity defect factor `gcd(a,b) / φ(gcd(a,b))` of the parent identity is the
product over the shared prime factors:

  `gcd(a,b) / φ(gcd(a,b)) = ∏_{p ∈ (gcd a b).primeFactors} p / (p - 1)`. -/
theorem defect_factor_gcd (a b : ℕ) (h : 0 < Nat.gcd a b) :
    (Nat.gcd a b : ℚ) / φ (Nat.gcd a b)
      = ∏ p ∈ (Nat.gcd a b).primeFactors, (p : ℚ) / ((p : ℚ) - 1) :=
  defect_ratio (Nat.gcd a b) h

/-! ### The squarefree case singled out by the open question -/

/-- **Totient of a squarefree number.**  For squarefree `d`, the totient is exactly the
product of `p - 1` over the prime factors: `φ(d) = ∏_{p | d} (p - 1)`.  (Mathlib provides
this only implicitly through the general product formula; here it is the direct statement.)
The proof cancels `∏ p = d` (positive) from the engine identity. -/
theorem totient_squarefree {d : ℕ} (hd : Squarefree d) :
    φ d = ∏ p ∈ d.primeFactors, (p - 1) := by
  have key := totient_mul_prod d
  rw [Nat.prod_primeFactors_of_squarefree hd] at key
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  rw [mul_comm (φ d) d] at key
  exact Nat.eq_of_mul_eq_mul_left hd0 key

/-- **The squarefree defect ratio**, with both numerator and denominator displayed as
products over the prime factors: for squarefree `d`,

  `d / φ(d) = (∏_{p | d} p) / (∏_{p | d} (p - 1))`. -/
theorem defect_ratio_squarefree {d : ℕ} (hd : Squarefree d) :
    (d : ℚ) / φ d
      = (∏ p ∈ d.primeFactors, (p : ℚ)) / (∏ p ∈ d.primeFactors, ((p : ℚ) - 1)) := by
  rw [defect_ratio d (Nat.pos_of_ne_zero hd.ne_zero), Finset.prod_div_distrib]

/-! ### Worked instances -/

section Examples

/-- `6 = 2·3` is squarefree: `6/φ(6) = 6/2 = 3 = (2/1)·(3/2)`. -/
example : (6 : ℚ) / φ 6 = ∏ p ∈ (6 : ℕ).primeFactors, (p : ℚ) / ((p : ℚ) - 1) :=
  defect_ratio 6 (by norm_num)

/-- `φ(15) = (3-1)(5-1) = 8` for the squarefree `15 = 3·5`. -/
example : φ 15 = ∏ p ∈ (15 : ℕ).primeFactors, (p - 1) := by
  have h15 : Squarefree (15 : ℕ) := by
    rw [(by norm_num : (15 : ℕ) = 3 * 5), Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_three.prime.squarefree,
      (by norm_num : Nat.Prime 5).prime.squarefree⟩
  exact totient_squarefree h15

/-- The defect factor at `gcd(12, 18) = 6`: `6/φ(6) = 3`, matching `∏_{p | 6} p/(p-1)`. -/
example : (Nat.gcd 12 18 : ℚ) / φ (Nat.gcd 12 18)
    = ∏ p ∈ (Nat.gcd 12 18).primeFactors, (p : ℚ) / ((p : ℚ) - 1) :=
  defect_factor_gcd 12 18 (by norm_num)

end Examples

end EulerTotientOQ03OQ03OQ01
