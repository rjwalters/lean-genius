import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-
# Lifting the Exponent for the *sum* `xⁿ + yⁿ` at the even prime `p = 2`

The odd-prime Lifting the Exponent Lemma (LTE) for sums states, for an odd prime
`p` with `p ∣ x + y`, `p ∤ x` and **odd** `n`,

  vₚ(xⁿ + yⁿ) = vₚ(x + y) + vₚ(n).

Mathlib proves this `emultiplicity` form for odd primes only
(`Int.emultiplicity_pow_add_pow`, which carries the hypothesis `Odd p`); the
sibling entry `LiftingTheExponentOQ01` re-exports the `padicValNat` shape.  The
companion `LiftingTheExponentOQ02` handles the *difference* `xⁿ - yⁿ` at `p = 2`,
where the even prime behaves differently.  Neither Mathlib nor the gallery records
the **sum** `xⁿ + yⁿ` at `p = 2`.  This file fills that gap and packages the
all-primes dispatch.

The `p = 2` analysis splits on the parity of the exponent:

* **`n` odd.**  Writing `xⁿ + yⁿ = xⁿ - (-y)ⁿ` (valid since `n` is odd) reduces
  the sum to a difference with `2 ∤ n`, and Mathlib's *prime-generic*
  `emultiplicity_pow_sub_pow_of_prime` (no oddness on `p`) gives
  `v₂(xⁿ + yⁿ) = v₂(x + y)`.  This is exactly the odd-prime formula with the
  vanishing `v₂(n) = 0` term, so for odd `n` the LTE-for-sums identity holds for
  **every** prime, including `2` — recorded as `emultiplicity_pow_add_pow_odd`.

* **`n` even** (with `x, y` odd).  Odd squares are `1 (mod 4)`, so for even `n`
  both `xⁿ ≡ 1` and `yⁿ ≡ 1 (mod 4)`, whence `xⁿ + yⁿ ≡ 2 (mod 4)`: the
  valuation is pinned to exactly `1`, independent of everything else
  (`two_emultiplicity_pow_add_pow_even`).  This is the additive twin of the
  difference lemma's even-exponent special value.

Results:
* `odd_pow_even_emod_four` — `Odd x → Even n → xⁿ % 4 = 1`.
* `two_emultiplicity_pow_add_pow_odd` — `v₂(xⁿ + yⁿ) = v₂(x + y)` for odd `n`.
* `two_emultiplicity_pow_add_pow_even` — `v₂(xⁿ + yⁿ) = 1` for even `n`, `x,y` odd.
* `two_padicValInt_pow_add_pow_odd` / `_even` — schoolbook integer-`v₂` forms.
* `emultiplicity_pow_add_pow_odd` — the unified all-primes dispatch for odd `n`.

The mathematical core (`emultiplicity_pow_sub_pow_of_prime`, the odd-prime LTE,
the `mod 4` fact for odd squares) is Mathlib's; the contribution is the reduction
of the sum at `p = 2` to those facts, the even-exponent value, and the uniform
all-primes statement.

Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/

namespace LiftingTheExponentOQ02OQ01

variable {x y : ℤ} {n : ℕ}

/-- For odd `x` and even `n`, `xⁿ ≡ 1 (mod 4)`.  Odd squares are `1 (mod 4)`
(`Int.sq_mod_four_eq_one_of_odd`), and an even power is a power of the square, so
the residue is carried by `Int.ModEq.pow`. -/
theorem odd_pow_even_emod_four (hx : Odd x) (hn : Even n) :
    x ^ n % 4 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hsq : x ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hx
  have hmod : (x ^ 2) ≡ 1 [ZMOD 4] := by
    show x ^ 2 % 4 = 1 % 4; omega
  have hpow : (x ^ 2) ^ m ≡ 1 ^ m [ZMOD 4] := hmod.pow m
  have hrw : x ^ (m + m) = (x ^ 2) ^ m := by rw [← two_mul, pow_mul]
  rw [hrw]
  have : (x ^ 2) ^ m % 4 = 1 ^ m % 4 := hpow
  simpa using this

/-- **LTE for the sum at `p = 2`, odd exponent.** For `2 ∣ x + y`, `2 ∤ x` and
**odd** `n`, `v₂(xⁿ + yⁿ) = v₂(x + y)`.  Reduces the sum to the difference
`xⁿ - (-y)ⁿ` (legal for odd `n`) and applies the prime-generic
`emultiplicity_pow_sub_pow_of_prime`, which — unlike the odd-prime LTE — places no
parity restriction on `p`. -/
theorem two_emultiplicity_pow_add_pow_odd
    (hxy : (2 : ℤ) ∣ x + y) (hx : ¬(2 : ℤ) ∣ x) (hn : Odd n) :
    emultiplicity (2 : ℤ) (x ^ n + y ^ n) = emultiplicity (2 : ℤ) (x + y) := by
  have hp : Prime (2 : ℤ) := Int.prime_two
  have hrw : x ^ n + y ^ n = x ^ n - (-y) ^ n := by rw [Odd.neg_pow hn]; ring
  have hxy' : (2 : ℤ) ∣ x - (-y) := by simpa [sub_neg_eq_add] using hxy
  have hnn : ¬(2 : ℤ) ∣ (n : ℤ) := by
    have hnat : ¬(2 : ℕ) ∣ n := by have h := Nat.odd_iff.mp hn; omega
    exact_mod_cast hnat
  rw [hrw, emultiplicity_pow_sub_pow_of_prime hp hxy' hx hnn, sub_neg_eq_add]

/-- **LTE for the sum at `p = 2`, even exponent.** For odd `x, y` and **even** `n`,
`v₂(xⁿ + yⁿ) = 1`.  Both `xⁿ` and `yⁿ` are `1 (mod 4)`, so the sum is `2 (mod 4)`:
divisible by `2` but not by `4`. -/
theorem two_emultiplicity_pow_add_pow_even
    (hx : Odd x) (hy : Odd y) (hn : Even n) :
    emultiplicity (2 : ℤ) (x ^ n + y ^ n) = 1 := by
  have hxm : x ^ n % 4 = 1 := odd_pow_even_emod_four hx hn
  have hym : y ^ n % 4 = 1 := odd_pow_even_emod_four hy hn
  set s := x ^ n + y ^ n with hsdef
  have hsum : s % 4 = 2 := by rw [hsdef]; omega
  have hdvd : (2 : ℤ) ∣ s := by omega
  have hndvd : ¬(4 : ℤ) ∣ s := by omega
  have hcoe : emultiplicity (2 : ℤ) s = ((1 : ℕ) : ℕ∞) := by
    rw [emultiplicity_eq_coe]
    refine ⟨by simpa using hdvd, ?_⟩
    have h4 : (2 : ℤ) ^ (1 + 1) = 4 := by norm_num
    rw [h4]; exact hndvd
  simpa using hcoe

/-- **Schoolbook integer form, odd exponent.** `v₂(xⁿ + yⁿ) = v₂(x + y)` with
`padicValInt`, carrying the nonzero hypotheses needed to descend from the extended
valuation to the finite `multiplicity`. -/
theorem two_padicValInt_pow_add_pow_odd
    (hxy : (2 : ℤ) ∣ x + y) (hx : ¬(2 : ℤ) ∣ x) (hn : Odd n)
    (hadd : x + y ≠ 0) (hne : x ^ n + y ^ n ≠ 0) :
    padicValInt 2 (x ^ n + y ^ n) = padicValInt 2 (x + y) := by
  have hem := two_emultiplicity_pow_add_pow_odd hxy hx hn
  have hf1 : FiniteMultiplicity (2 : ℤ) (x ^ n + y ^ n) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hne⟩
  have hf2 : FiniteMultiplicity (2 : ℤ) (x + y) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hadd⟩
  rw [hf1.emultiplicity_eq_multiplicity, hf2.emultiplicity_eq_multiplicity] at hem
  have hmm : multiplicity (2 : ℤ) (x ^ n + y ^ n) = multiplicity (2 : ℤ) (x + y) := by
    exact_mod_cast hem
  rw [padicValInt.of_ne_one_ne_zero (by decide) hne,
      padicValInt.of_ne_one_ne_zero (by decide) hadd]
  exact hmm

/-- **Schoolbook integer form, even exponent.** `v₂(xⁿ + yⁿ) = 1` for odd `x, y`
and even `n`.  No nonzero hypothesis is needed: `xⁿ + yⁿ ≡ 2 (mod 4)` is never
zero. -/
theorem two_padicValInt_pow_add_pow_even
    (hx : Odd x) (hy : Odd y) (hn : Even n) :
    padicValInt 2 (x ^ n + y ^ n) = 1 := by
  have hxm : x ^ n % 4 = 1 := odd_pow_even_emod_four hx hn
  have hym : y ^ n % 4 = 1 := odd_pow_even_emod_four hy hn
  have hne : x ^ n + y ^ n ≠ 0 := by omega
  have hem := two_emultiplicity_pow_add_pow_even hx hy hn
  have hf : FiniteMultiplicity (2 : ℤ) (x ^ n + y ^ n) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hne⟩
  rw [hf.emultiplicity_eq_multiplicity] at hem
  rw [padicValInt.of_ne_one_ne_zero (by decide) hne]
  exact_mod_cast hem

/-- **Unified all-primes dispatch (odd exponent).** For *every* prime `p` with
`p ∣ x + y`, `p ∤ x`, and **odd** `n`,
`vₚ(xⁿ + yⁿ) = vₚ(x + y) + vₚ(n)`.  For odd `p` this is Mathlib's
`Int.emultiplicity_pow_add_pow`; for `p = 2` the extra term `v₂(n) = 0` (odd `n`)
collapses it to `two_emultiplicity_pow_add_pow_odd`.  So the single odd-exponent
formula governs all primes at once. -/
theorem emultiplicity_pow_add_pow_odd {p : ℕ} (hp : p.Prime)
    (hxy : (p : ℤ) ∣ x + y) (hx : ¬(p : ℤ) ∣ x) (hn : Odd n) :
    emultiplicity (p : ℤ) (x ^ n + y ^ n)
      = emultiplicity (p : ℤ) (x + y) + emultiplicity p n := by
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2
    have hzero : emultiplicity (2 : ℕ) n = 0 := by
      rw [emultiplicity_eq_zero]
      have h := Nat.odd_iff.mp hn; omega
    rw [hzero, add_zero]
    have hxy' : (2 : ℤ) ∣ x + y := by exact_mod_cast hxy
    have hx' : ¬(2 : ℤ) ∣ x := by exact_mod_cast hx
    have := two_emultiplicity_pow_add_pow_odd hxy' hx' hn
    exact_mod_cast this
  · have hpodd : Odd p := hp.odd_of_ne_two hp2
    exact Int.emultiplicity_pow_add_pow hp hpodd hxy hx hn

/-! ### Concrete confirmations

Numerical witnesses, all by kernel `decide` (no `native_decide`, hence no
`Lean.ofReduceBool`). -/

/-- Odd exponent, `n = 3`: `v₂(3³ + 5³) = v₂(152) = 3 = v₂(8) = v₂(3 + 5)`.
The valuation `3` is witnessed by `8 ∣ 152 ∧ ¬16 ∣ 152`. -/
theorem check_odd_three : padicValInt 2 (3 ^ 3 + 5 ^ 3) = padicValInt 2 (3 + 5) :=
  two_padicValInt_pow_add_pow_odd (by decide) (by decide) (by decide) (by decide) (by decide)

theorem check_odd_three_value : (2 : ℤ) ^ 3 ∣ (3 ^ 3 + 5 ^ 3) ∧ ¬(2 : ℤ) ^ 4 ∣ (3 ^ 3 + 5 ^ 3) := by
  decide

/-- Even exponent, `n = 2`: `v₂(3² + 5²) = v₂(34) = 1`. -/
theorem check_even_two : padicValInt 2 (3 ^ 2 + 5 ^ 2) = 1 :=
  two_padicValInt_pow_add_pow_even (by decide) (by decide) (by decide)

theorem check_even_two_value : (2 : ℤ) ^ 1 ∣ (3 ^ 2 + 5 ^ 2) ∧ ¬(2 : ℤ) ^ 2 ∣ (3 ^ 2 + 5 ^ 2) := by
  decide

end LiftingTheExponentOQ02OQ01
