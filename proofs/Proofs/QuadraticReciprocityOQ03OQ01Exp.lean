import Mathlib
import Proofs.QuadraticReciprocityOQ03OQ01

/-
# The Textbook Exponential Form of the Second Supplementary Law (OQ-03-OQ-01, S3)

Open Question follow-up (from `quadratic-reciprocity-oq-03-oq-01`):

  S1 (`QRAlgorithmTwo.legendreSym_two_eq`) packaged the second supplementary law
  as the χ₈ *character* form `(2/p) = χ₈ (p : ZMod 8)` — the form Mathlib provides
  and the one the GCD-style algorithm actually evaluates.
  S2 added the *residue-criterion* form `(2/p) = 1 ↔ p % 8 ∈ {1,7}`.

  The single remaining documented gap was the **classical textbook exponential
  form**
        `(2/p) = (-1)^((p² - 1)/8)`,
  which Mathlib does **not** state as a named lemma. This file closes it.

## The bridge

Combining S1 with Mathlib's value table `ZMod.χ₈_nat_eq_if_mod_eight`
(`χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1`),
the claim reduces, for an odd prime `p`, to

        `(if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1) = (-1 : ℤ) ^ ((p² - 1) / 8)`.

We case-split on `p % 8 ∈ {1, 3, 5, 7}` (`p` is odd). In each case we exhibit the
**exact, subtraction-free** decomposition `p² = 8 * (8m² + 2mr + d) + 1`
(`d = 0,1,3,6` for `r = 1,3,5,7`), whence `(p² - 1)/8 = 8m² + 2mr + d` by `omega`,
and the sign follows from the parity of that integer (`Even`/`Odd.neg_one_pow`).
The parity is `0,1,1,0` on residues `1,3,5,7`, exactly matching χ₈ = `1,-1,-1,1`.

All arithmetic is independently certified (sympy symbolic + brute force over all
odd primes `p < 20000`) by
`research/problems/quadratic-reciprocity-oq-03-oq-01/verify_exp_form.py`.

Bearer lemmas verified against the Mathlib pin `v4.26.0`:
`legendreSym.at_two` (via S1), `ZMod.χ₈_nat_eq_if_mod_eight`
(`NumberTheory/LegendreSymbol/ZModChar.lean:151`), `Even.neg_one_pow` /
`Odd.neg_one_pow` (`Algebra/Ring/Parity.lean:47,176`), `Nat.Prime.odd_of_ne_two`.
-/

open ZMod

namespace QRAlgorithmTwo

/-- **Second supplementary law, textbook exponential form.**

For an odd prime `p`,

  `(2/p) = (-1)^((p² - 1)/8)`.

This is the classical `(-1)^((p²-1)/8)` statement, equivalent to the χ₈ character
form `legendreSym_two_eq` (S1) but not available in Mathlib as a named lemma. The
proof bridges the two via the χ₈ value table and a `p % 8` parity computation. -/
theorem legendreSym_two_eq_pow (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    obtain ⟨k, hk⟩ := hodd; omega
  rcases hp8 with h | h | h | h
  · -- p ≡ 1 (mod 8): exponent 8m² + 2m is even, χ₈ = +1
    obtain ⟨m, hm⟩ : ∃ m, p = 8 * m + 1 := ⟨p / 8, by omega⟩
    have h2 : p ^ 2 = 8 * (8 * m ^ 2 + 2 * m) + 1 := by rw [hm]; ring
    have he : (p ^ 2 - 1) / 8 = 8 * m ^ 2 + 2 * m := by omega
    have hev : Even (8 * m ^ 2 + 2 * m) := ⟨4 * m ^ 2 + m, by ring⟩
    rw [legendreSym_two_eq p hp, χ₈_nat_eq_if_mod_eight p, if_neg (by omega : ¬ p % 2 = 0),
        if_pos (Or.inl h), he, hev.neg_one_pow]
  · -- p ≡ 3 (mod 8): exponent 8m² + 6m + 1 is odd, χ₈ = -1
    obtain ⟨m, hm⟩ : ∃ m, p = 8 * m + 3 := ⟨p / 8, by omega⟩
    have h2 : p ^ 2 = 8 * (8 * m ^ 2 + 6 * m + 1) + 1 := by rw [hm]; ring
    have he : (p ^ 2 - 1) / 8 = 8 * m ^ 2 + 6 * m + 1 := by omega
    have hodd' : Odd (8 * m ^ 2 + 6 * m + 1) := ⟨4 * m ^ 2 + 3 * m, by ring⟩
    rw [legendreSym_two_eq p hp, χ₈_nat_eq_if_mod_eight p, if_neg (by omega : ¬ p % 2 = 0),
        if_neg (by omega : ¬ (p % 8 = 1 ∨ p % 8 = 7)), he, hodd'.neg_one_pow]
  · -- p ≡ 5 (mod 8): exponent 8m² + 10m + 3 is odd, χ₈ = -1
    obtain ⟨m, hm⟩ : ∃ m, p = 8 * m + 5 := ⟨p / 8, by omega⟩
    have h2 : p ^ 2 = 8 * (8 * m ^ 2 + 10 * m + 3) + 1 := by rw [hm]; ring
    have he : (p ^ 2 - 1) / 8 = 8 * m ^ 2 + 10 * m + 3 := by omega
    have hodd' : Odd (8 * m ^ 2 + 10 * m + 3) := ⟨4 * m ^ 2 + 5 * m + 1, by ring⟩
    rw [legendreSym_two_eq p hp, χ₈_nat_eq_if_mod_eight p, if_neg (by omega : ¬ p % 2 = 0),
        if_neg (by omega : ¬ (p % 8 = 1 ∨ p % 8 = 7)), he, hodd'.neg_one_pow]
  · -- p ≡ 7 (mod 8): exponent 8m² + 14m + 6 is even, χ₈ = +1
    obtain ⟨m, hm⟩ : ∃ m, p = 8 * m + 7 := ⟨p / 8, by omega⟩
    have h2 : p ^ 2 = 8 * (8 * m ^ 2 + 14 * m + 6) + 1 := by rw [hm]; ring
    have he : (p ^ 2 - 1) / 8 = 8 * m ^ 2 + 14 * m + 6 := by omega
    have hev : Even (8 * m ^ 2 + 14 * m + 6) := ⟨4 * m ^ 2 + 7 * m + 3, by ring⟩
    rw [legendreSym_two_eq p hp, χ₈_nat_eq_if_mod_eight p, if_neg (by omega : ¬ p % 2 = 0),
        if_pos (Or.inr h), he, hev.neg_one_pow]

-- ============================================================
-- Verified example computations of the exponential form
-- ============================================================

/-- `(2/3) = (-1)^((9-1)/8) = (-1)^1 = -1`. -/
example : legendreSym 3 2 = (-1 : ℤ) ^ ((3 ^ 2 - 1) / 8) := by decide

/-- `(2/7) = (-1)^((49-1)/8) = (-1)^6 = 1`. -/
example : legendreSym 7 2 = (-1 : ℤ) ^ ((7 ^ 2 - 1) / 8) := by decide

/-- `(2/17) = (-1)^((289-1)/8) = (-1)^36 = 1`  (17 ≡ 1 mod 8). -/
example : legendreSym 17 2 = (-1 : ℤ) ^ ((17 ^ 2 - 1) / 8) := by decide

/-- `(2/13) = (-1)^((169-1)/8) = (-1)^21 = -1`  (13 ≡ 5 mod 8). -/
example : legendreSym 13 2 = (-1 : ℤ) ^ ((13 ^ 2 - 1) / 8) := by decide

#check @legendreSym_two_eq_pow

end QRAlgorithmTwo
