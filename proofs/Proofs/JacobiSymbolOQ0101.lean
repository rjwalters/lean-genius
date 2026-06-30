/-
  Quadratic Reciprocity for the Jacobi symbol, with explicit power-form
  supplementary laws.

  The **Jacobi symbol** `J(a | b)` (for odd `b`) obeys the *Law of Quadratic
  Reciprocity* and two *supplementary laws*, exactly as the Legendre symbol
  does — even though `b` need not be prime:

    * **Reciprocity**: for odd `a, b`,
        `J(a | b) = (-1)^((a-1)/2 · (b-1)/2) · J(b | a)`;
      with the clean residue-class corollaries
        `a ≡ 1 (mod 4)  ⟹  J(a|b) = J(b|a)`,
        `a ≡ b ≡ 3 (mod 4)  ⟹  J(a|b) = -J(b|a)`.
    * **First supplementary law**: `J(-1 | b) = (-1)^((b-1)/2)`.
    * **Second supplementary law**: `J(2 | b) = (-1)^((b²-1)/8)`.

  Mathlib provides the reciprocity law directly (`jacobiSym.quadratic_reciprocity`)
  and the supplementary laws in *character* form — `J(-1|b) = χ₄ b` and
  `J(2|b) = χ₈ b`, where `χ₄, χ₈` are the quadratic characters mod 4 and mod 8.
  The mathematical content added here is the bridge to the **classical explicit
  power forms**: we evaluate `χ₄ b` and `χ₈ b` as concrete powers of `-1`,
  the form in which the supplementary laws are stated in every textbook. The
  `χ₈ → (-1)^((b²-1)/8)` bridge is the substantive step: it is an elementary
  but genuine residue computation on `b mod 8` (the parity of `(b²-1)/8` is
  `b mod 8`–periodic), carried out below from first principles.

  Together with a worked evaluation by *flipping*, this packages the full
  reciprocity toolkit that makes the Jacobi symbol an efficient,
  factorization-free residue calculator.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

namespace JacobiSymbolOQ0101

/-! ### The Law of Quadratic Reciprocity -/

/-- **Quadratic Reciprocity for the Jacobi symbol**: for odd `a, b`,
`J(a | b) = (-1)^((a/2)·(b/2)) · J(b | a)`.  (For odd `n`, `n/2 = (n-1)/2`.) -/
theorem jacobi_quadratic_reciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    jacobiSym a b = (-1) ^ (a / 2 * (b / 2)) * jacobiSym b a :=
  jacobiSym.quadratic_reciprocity ha hb

/-- If `a ≡ 1 (mod 4)` and `b` is odd, the symbols agree: `J(a|b) = J(b|a)`. -/
theorem jacobi_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    jacobiSym a b = jacobiSym b a :=
  jacobiSym.quadratic_reciprocity_one_mod_four ha hb

/-- If `a ≡ b ≡ 3 (mod 4)`, the symbols are opposite: `J(a|b) = -J(b|a)`. -/
theorem jacobi_reciprocity_three_mod_four {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
    jacobiSym a b = -jacobiSym b a :=
  jacobiSym.quadratic_reciprocity_three_mod_four ha hb

/-! ### First supplementary law: `J(-1 | b) = (-1)^((b-1)/2)` -/

/-- **First supplementary law**, explicit power form: for odd `b`,
`J(-1 | b) = (-1)^((b-1)/2)`.  Bridges Mathlib's character form `χ₄ b`. -/
theorem jacobi_at_neg_one_pow {b : ℕ} (hb : Odd b) :
    jacobiSym (-1) b = (-1) ^ ((b - 1) / 2) := by
  have hodd : b % 2 = 1 := Nat.odd_iff.mp hb
  rw [jacobiSym.at_neg_one hb, ZMod.χ₄_eq_neg_one_pow hodd]
  congr 1
  omega

/-! ### Second supplementary law: `J(2 | b) = (-1)^((b²-1)/8)`

This is the substantive bridge.  Mathlib gives `J(2|b) = χ₈ b`, where `χ₈ b`
is `+1` for `b ≡ ±1 (mod 8)` and `-1` for `b ≡ ±3 (mod 8)`.  We must show this
equals `(-1)^((b²-1)/8)`, i.e. that the parity of the exponent `(b²-1)/8` is
`+` exactly for `b ≡ ±1 (mod 8)`.  Writing `b = 8q + r` with `r = b % 8 ∈
{1,3,5,7}`, we have `b² - 1 = 8(8q² + 2qr) + (r²-1)` with `8 ∣ r²-1`, so the
parity of `(b²-1)/8` is the parity of `(r²-1)/8`, which is even iff `r ∈ {1,7}`.
The four residue cases are discharged below by `omega` (treating `q*q` as an
opaque atom) plus `pow_mul`/`pow_succ`. -/

/-- **Second supplementary law**, explicit power form: for odd `b`,
`J(2 | b) = (-1)^((b²-1)/8)`. -/
theorem jacobi_at_two_pow {b : ℕ} (hb : Odd b) :
    jacobiSym 2 b = (-1) ^ ((b ^ 2 - 1) / 8) := by
  have hodd : b % 2 = 1 := Nat.odd_iff.mp hb
  rw [jacobiSym.at_two hb, ZMod.χ₈_nat_eq_if_mod_eight]
  rw [if_neg (by omega : ¬ b % 2 = 0)]
  set q := b / 8 with hq
  rcases (by omega : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7) with h | h | h | h
  · -- b ≡ 1 (mod 8): exponent even
    rw [if_pos (Or.inl h)]
    have hb1 : b = 8 * q + 1 := by omega
    have hsq : b ^ 2 = 64 * (q * q) + 16 * q + 1 := by rw [hb1]; ring
    have hexp : (b ^ 2 - 1) / 8 = 2 * (4 * (q * q) + q) := by omega
    rw [hexp, pow_mul]; norm_num
  · -- b ≡ 3 (mod 8): exponent odd
    rw [if_neg (by omega)]
    have hb3 : b = 8 * q + 3 := by omega
    have hsq : b ^ 2 = 64 * (q * q) + 48 * q + 9 := by rw [hb3]; ring
    have hexp : (b ^ 2 - 1) / 8 = 2 * (4 * (q * q) + 3 * q) + 1 := by omega
    rw [hexp, pow_succ, pow_mul]; norm_num
  · -- b ≡ 5 (mod 8): exponent odd
    rw [if_neg (by omega)]
    have hb5 : b = 8 * q + 5 := by omega
    have hsq : b ^ 2 = 64 * (q * q) + 80 * q + 25 := by rw [hb5]; ring
    have hexp : (b ^ 2 - 1) / 8 = 2 * (4 * (q * q) + 5 * q + 1) + 1 := by omega
    rw [hexp, pow_succ, pow_mul]; norm_num
  · -- b ≡ 7 (mod 8): exponent even
    rw [if_pos (Or.inr h)]
    have hb7 : b = 8 * q + 7 := by omega
    have hsq : b ^ 2 = 64 * (q * q) + 112 * q + 49 := by rw [hb7]; ring
    have hexp : (b ^ 2 - 1) / 8 = 2 * (4 * (q * q) + 7 * q + 3) := by omega
    rw [hexp, pow_mul]; norm_num

/-! ### A worked evaluation by reciprocity (no factorization)

The payoff of Jacobi reciprocity: `J(a|b)` can be evaluated by repeatedly
*flipping* the arguments and reducing the (now larger) numerator modulo the
(smaller) denominator — never factoring `b`.  We illustrate one flip step.
`norm_num`'s Jacobi-symbol extension automates the whole chain; the explicit
flip below exhibits the single reciprocity step it performs internally. -/

/-- Worked evaluation: `J(5 | 21) = 1`, obtained by flipping (`5 ≡ 1 mod 4`,
so `J(5|21) = J(21|5)`) and then reducing — *without* factoring `21 = 3·7`. -/
theorem jacobi_five_twentyone_by_reciprocity : jacobiSym 5 21 = 1 := by
  have flip : jacobiSym 5 21 = jacobiSym 21 5 :=
    jacobiSym.quadratic_reciprocity_one_mod_four (by norm_num) (by norm_num)
  rw [flip]
  -- `J(21|5)`: numerator reduces `21 ≡ 1 (mod 5)`, giving `J(1|5) = 1`.
  norm_num

/-- Sanity cross-check: the same value computed directly (definitionally,
via the prime factorization of `21`). Both routes agree. -/
theorem jacobi_five_twentyone_direct : jacobiSym 5 21 = 1 := by norm_num

end JacobiSymbolOQ0101
