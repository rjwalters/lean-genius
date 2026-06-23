import Mathlib

/-
# The Multiplicative Order of `1 + p·a` modulo an Odd Prime Power

Fix an odd prime `p` and an integer `a` not divisible by `p`. In the ring `ZMod (p^(n+1))`
the element `1 + p·a` is a unit, and its multiplicative order is exactly `p^n`:

`orderOf (1 + p·a) = p^n`.

This is the arithmetic engine behind the structure of `(ZMod (p^k))ˣ`: the "principal
units" `1 + p·ℤ` form a cyclic `p`-group of order `p^n`, which combines with the cyclic
group of order `p-1` coming from reduction mod `p` to make the whole unit group cyclic for
odd prime powers. Every element of the shape `1 + p·a` with `p ∤ a` already attains the
maximal `p`-power order `p^n`.

Mathlib proves the order computation as `ZMod.orderOf_one_add_mul_prime` (and the prime-power
generalisation `ZMod.orderOf_one_add_mul_prime_pow`). What it does **not** package is the
collection of immediate structural consequences:

* the order is *independent of the residue* `a` (every admissible `a` gives the same order);
* the order is a power of `p`, so `1 + p·a` is a `p`-element of the unit group;
* the order equals `1` exactly modulo `p` itself (the `n = 0` case);
* concrete numeric instances such as `orderOf (4 : ZMod 9) = 3`, `orderOf (4 : ZMod 27) = 9`
  and `orderOf (6 : ZMod 25) = 5`.

This file collects these, deriving each from the single Mathlib result, with no axioms and no
`native_decide` (the concrete orders are obtained from the theorem, not by kernel evaluation).

The core order computation is re-exported from Mathlib; the "independent of `a`" statement
and the structural corollaries are assembled here.
-/

namespace OrderOneAddMulPrimeOQ01

/-- **Order of `1 + p·a` modulo `p^(n+1)`** (re-export of `ZMod.orderOf_one_add_mul_prime`).
For an odd prime `p` and an integer `a` with `p ∤ a`, the multiplicative order of `1 + p·a`
in `ZMod (p^(n+1))` is `p^n`. -/
theorem orderOf_one_add_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + p * a : ZMod (p ^ (n + 1))) = p ^ n :=
  ZMod.orderOf_one_add_mul_prime hp hp2 a ha n

/-- **The order does not depend on the residue `a`.** Any two integers coprime to the odd
prime `p` produce elements `1 + p·a` of the same multiplicative order `p^n`. -/
theorem orderOf_one_add_mul_prime_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) (n : ℕ) :
    orderOf (1 + p * a : ZMod (p ^ (n + 1))) = orderOf (1 + p * b : ZMod (p ^ (n + 1))) := by
  rw [orderOf_one_add_mul_prime hp hp2 a ha n, orderOf_one_add_mul_prime hp hp2 b hb n]

/-- **The order is a power of `p`**, so `1 + p·a` is a `p`-element of the unit group. -/
theorem exists_orderOf_eq_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    ∃ k, orderOf (1 + p * a : ZMod (p ^ (n + 1))) = p ^ k :=
  ⟨n, orderOf_one_add_mul_prime hp hp2 a ha n⟩

/-- **Textbook specialisation `a = 1`:** the order of `1 + p` modulo `p^(n+1)` is `p^n`
(re-export of `ZMod.orderOf_one_add_prime`). -/
theorem orderOf_one_add_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    orderOf (1 + p : ZMod (p ^ (n + 1))) = p ^ n :=
  ZMod.orderOf_one_add_prime hp hp2 n

/-- The order is `1` exactly when `n = 0`, i.e. modulo `p` itself (where `1 + p·a = 1`). -/
theorem orderOf_eq_one_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + p * a : ZMod (p ^ (n + 1))) = 1 ↔ n = 0 := by
  rw [orderOf_one_add_mul_prime hp hp2 a ha n]
  constructor
  · intro h
    by_contra hn
    have hle : p ≤ p ^ n := le_self_pow hp.one_lt.le hn
    have := hp.two_le
    omega
  · rintro rfl; rfl

/-! ### Concrete numeric instances (axiom-free, derived from the theorem) -/

/-- `1 + 3·1 = 4` has order `3 = 3^1` modulo `9 = 3^2`. -/
theorem orderOf_four_zmod_nine : orderOf (4 : ZMod 9) = 3 := by
  have h := orderOf_one_add_mul_prime (p := 3) (by norm_num) (by norm_num) (a := 1)
    (by norm_num) (n := 1)
  have e : (1 + (3 : ℕ) * (1 : ℤ) : ZMod (3 ^ (1 + 1))) = 4 := by push_cast; ring
  rw [e] at h
  exact h

/-- `1 + 3·1 = 4` has order `9 = 3^2` modulo `27 = 3^3`. -/
theorem orderOf_four_zmod_twentyseven : orderOf (4 : ZMod 27) = 9 := by
  have h := orderOf_one_add_mul_prime (p := 3) (by norm_num) (by norm_num) (a := 1)
    (by norm_num) (n := 2)
  have e : (1 + (3 : ℕ) * (1 : ℤ) : ZMod (3 ^ (2 + 1))) = 4 := by push_cast; ring
  rw [e] at h
  exact h

/-- `1 + 5·1 = 6` has order `5 = 5^1` modulo `25 = 5^2`. -/
theorem orderOf_six_zmod_twentyfive : orderOf (6 : ZMod 25) = 5 := by
  have h := orderOf_one_add_mul_prime (p := 5) (by norm_num) (by norm_num) (a := 1)
    (by norm_num) (n := 1)
  have e : (1 + (5 : ℕ) * (1 : ℤ) : ZMod (5 ^ (1 + 1))) = 6 := by push_cast; ring
  rw [e] at h
  exact h

end OrderOneAddMulPrimeOQ01
