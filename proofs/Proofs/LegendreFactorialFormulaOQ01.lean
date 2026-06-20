/-
# Legendre's Formula for the p-adic Valuation of a Factorial

Legendre's theorem gives a closed form for the exact power of a prime `p`
dividing `n!`.  Classically it is stated in two equivalent ways:

* **Floor-sum form**:  `vₚ(n!) = ∑_{i ≥ 1} ⌊n / pⁱ⌋`.
* **Digit-sum form**:  `(p − 1) · vₚ(n!) = n − Sₚ(n)`, where `Sₚ(n)` is the sum
  of the base-`p` digits of `n`.

Mathlib supplies both forms (`padicValNat_factorial`,
`sub_one_mul_padicValNat_factorial`) and the bound `vₚ(n!) ≤ n`.  This entry
packages them as a self-contained statement of Legendre's theorem and adds the
**solved form**

  `vₚ(n!) = (n − Sₚ(n)) / (p − 1)`,

which expresses the valuation directly (Mathlib only records the `(p − 1)·`
multiple).  We close with a worked numerical instance, `v₂(10!) = 8`.

All results are fully verified with no `sorry` and no extra axioms.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Nat Finset

namespace LegendreFactorialFormulaOQ01

variable {p : ℕ}

/-- **Legendre's theorem (floor-sum form).**
For a prime `p` and any bound `b` strictly above `log p n`, the `p`-adic
valuation of `n!` is the finite sum of the quotients `⌊n / pⁱ⌋`. -/
theorem padicValNat_factorial_eq_sum [hp : Fact p.Prime] {n b : ℕ}
    (hnb : Nat.log p n < b) :
    padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i :=
  padicValNat_factorial hnb

/-- **Legendre's theorem (digit-sum form).**
`(p − 1)` times the `p`-adic valuation of `n!` equals `n` minus the sum of the
base-`p` digits of `n`. -/
theorem sub_one_mul_padicValNat_factorial_eq [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (n !) = n - (p.digits n).sum :=
  sub_one_mul_padicValNat_factorial n

/-- **Solved form of Legendre's theorem.**
The `p`-adic valuation of `n!` is exactly `(n − Sₚ(n)) / (p − 1)`, where
`Sₚ(n)` is the base-`p` digit sum.  This isolates `vₚ(n!)` itself, whereas
Mathlib records only the `(p − 1)`-multiple. -/
theorem padicValNat_factorial_eq_div [hp : Fact p.Prime] (n : ℕ) :
    padicValNat p (n !) = (n - (p.digits n).sum) / (p - 1) := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  -- From `(p-1) * v = n - S`, divide both sides by `p - 1`.
  rw [← h, Nat.mul_div_cancel_left _ hp1]

/-- **Legendre's bound.**  The `p`-adic valuation of `n!` never exceeds `n`. -/
theorem padicValNat_factorial_le [hp : Fact p.Prime] (n : ℕ) :
    padicValNat p (n !) ≤ n :=
  _root_.padicValNat_factorial_le p n

/-- Worked instance: the exact power of `2` dividing `10!` is `2⁸`.
Via the floor-sum form, `v₂(10!) = ⌊10/2⌋ + ⌊10/4⌋ + ⌊10/8⌋ = 5 + 2 + 1 = 8`. -/
example : padicValNat 2 (10 !) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_factorial_eq_sum (p := 2) (n := 10) (b := 4)
    (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
  decide

end LegendreFactorialFormulaOQ01
