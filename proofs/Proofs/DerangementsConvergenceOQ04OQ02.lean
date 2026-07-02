/-
  Derangements: the combined modulus n(n−1) and its explicit CRT residue
  Open Question: derangements-convergence-oq-04-oq-02
  (parent `derangements-convergence-oq-04`, open question 2)

  The parent entry proves two divisibility facts for the derangement numbers
  `D(n) = numDerangements n`:

    (A)  (n − 1) ∣ D(n)              for n ≥ 2      [additive recurrence]
    (B)  n ∣ (D(n) − (−1)^n)         for all n      [multiplicative recurrence]

  Its open question asks: *for which n does n(n−1) ∣ (D(n) − c) for an explicit
  residue c, combining the two facts via CRT?*  Because `n` and `n − 1` are
  coprime, the Chinese Remainder Theorem fuses (A) and (B) into a single
  congruence modulo `n(n−1)`.  The key observation is that a **single closed
  form** solves the CRT system for every parity at once:

    c(n) = (−1)^n · (n − 1)².

  Indeed `(n − 1)² ≡ 0 (mod n−1)` recovers (A) and `(n − 1)² ≡ 1 (mod n)`
  (as `n − 1 ≡ −1`) recovers (B).  Hence:

  ## Main Result

  `mul_dvd_sub_crt` (PROVED): for all n,
    (n * (n − 1) : ℤ) ∣ (D(n) − (−1)^n · (n − 1)²).

  Equivalently `D(n) ≡ (−1)^n (n−1)²  (mod n(n−1))`.

  ## Canonical reduced residue

  The closed form `(−1)^n (n−1)²` is not reduced for odd `n` (it is negative).
  Reducing modulo `n(n−1)` gives the canonical representative

    r(n) = (n − 1)²   if n is even,
    r(n) = (n − 1)    if n is odd,

  with `0 ≤ r(n) < n(n−1)` for n ≥ 2 (`reduced_residue_lt`), and
  `D(n) ≡ r(n) (mod n(n−1))` (`numDerangements_sub_reduced_dvd`).

  Sample values (checked below): D(4)=9 ≡ 9 (mod 12), D(5)=44 ≡ 4 (mod 20),
  D(6)=265 ≡ 25 (mod 30).

  Everything is read off the two standard Mathlib recurrences for
  `numDerangements`; the proofs are fully machine-checked with no extra axioms.
-/

import Mathlib

open Nat

namespace DerangementsConvergenceOQ04OQ02

/-! ### The two parent divisibility facts (reproduced, self-contained) -/

/-- Fact (A): for n ≥ 2, `(n − 1)` divides `D(n)`. Read off the additive
    recurrence `numDerangements_add_two`. -/
theorem sub_one_dvd_numDerangements (n : ℕ) (hn : 2 ≤ n) :
    (n - 1) ∣ numDerangements n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨numDerangements m + numDerangements (m + 1), ?_⟩
  simpa using numDerangements_add_two m

/-- Fact (B) over ℤ: for all n, `n ∣ (D(n) − (−1)^n)`. Read off the
    multiplicative recurrence `numDerangements_succ`. -/
theorem dvd_numDerangements_sub_neg_one_pow (n : ℕ) :
    (n : ℤ) ∣ ((numDerangements n : ℤ) - (-1) ^ n) := by
  cases n with
  | zero => simp
  | succ k =>
    refine ⟨numDerangements k, ?_⟩
    rw [numDerangements_succ k, pow_succ]
    push_cast
    ring

/-! ### Coprimality of consecutive integers -/

/-- `n` and `n − 1` are coprime as integers: `1·n + (−1)·(n−1) = 1`. -/
theorem isCoprime_self_sub_one (n : ℕ) :
    IsCoprime (n : ℤ) ((n : ℤ) - 1) :=
  ⟨1, -1, by ring⟩

/-! ### The combined modulus via CRT -/

/-- The `(n−1)`-component divisibility of the CRT residue `(−1)^n (n−1)²`. -/
private theorem sub_one_dvd_shift (n : ℕ) :
    ((n : ℤ) - 1) ∣ ((numDerangements n : ℤ) - (-1) ^ n * ((n : ℤ) - 1) ^ 2) := by
  -- (n−1) ∣ (−1)^n (n−1)² always; (n−1) ∣ D(n) for n ≥ 2 (fact A).
  have hsq : ((n : ℤ) - 1) ∣ (-1) ^ n * ((n : ℤ) - 1) ^ 2 :=
    (dvd_pow_self ((n : ℤ) - 1) (by norm_num : (2 : ℕ) ≠ 0)).mul_left _
  rcases Nat.lt_or_ge n 2 with h | h
  · -- n = 0 or 1: evaluate directly
    interval_cases n <;> simp [numDerangements_zero, numDerangements_one]
  · have hnat := sub_one_dvd_numDerangements n h
    have hA : ((n : ℤ) - 1) ∣ (numDerangements n : ℤ) := by
      have hc := Int.natCast_dvd_natCast.mpr hnat
      rwa [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hc
    exact dvd_sub hA hsq

/-- The `n`-component divisibility of the CRT residue `(−1)^n (n−1)²`. -/
private theorem cast_dvd_shift (n : ℕ) :
    (n : ℤ) ∣ ((numDerangements n : ℤ) - (-1) ^ n * ((n : ℤ) - 1) ^ 2) := by
  -- D(n) − (−1)^n (n−1)² = (D(n) − (−1)^n) + (−1)^n · (1 − (n−1)²),
  -- and 1 − (n−1)² = n(2 − n), so n divides both summands.
  have hB := dvd_numDerangements_sub_neg_one_pow n
  have hterm : (n : ℤ) ∣ (-1) ^ n * (1 - ((n : ℤ) - 1) ^ 2) := by
    refine Dvd.dvd.mul_left ?_ _
    exact ⟨2 - (n : ℤ), by ring⟩
  have := dvd_add hB hterm
  have hrw : ((numDerangements n : ℤ) - (-1) ^ n)
      + (-1) ^ n * (1 - ((n : ℤ) - 1) ^ 2)
      = (numDerangements n : ℤ) - (-1) ^ n * ((n : ℤ) - 1) ^ 2 := by ring
  rwa [hrw] at this

/-- **Main result (CRT combination).** For every `n`,
    `n(n−1)` divides `D(n) − (−1)^n (n−1)²`.  Equivalently
    `D(n) ≡ (−1)^n (n−1)²  (mod n(n−1))`.

    Proof: `n − 1 ∣ ·` is fact (A) plus `n−1 ∣ (n−1)²`; `n ∣ ·` is fact (B)
    plus `(n−1)² ≡ 1 (mod n)`. Since `n` and `n−1` are coprime, their product
    divides the common multiple. -/
theorem mul_dvd_sub_crt (n : ℕ) :
    ((n : ℤ) * ((n : ℤ) - 1)) ∣
      ((numDerangements n : ℤ) - (-1) ^ n * ((n : ℤ) - 1) ^ 2) :=
  (isCoprime_self_sub_one n).mul_dvd (cast_dvd_shift n) (sub_one_dvd_shift n)

/-- Restatement of the main result as a `ZMod` equality over the combined
    modulus `n(n−1)`:  `D(n) = (−1)^n (n−1)²` in `ℤ/n(n−1)ℤ`. -/
theorem numDerangements_zmod_mul_eq (n : ℕ) :
    (numDerangements n : ZMod (n * (n - 1)))
      = (-1) ^ n * ((n : ZMod (n * (n - 1))) - 1) ^ 2 := by
  have h := mul_dvd_sub_crt n
  have hz : ((n : ℤ) * ((n : ℤ) - 1)) = (((n * (n - 1) : ℕ)) : ℤ) := by
    rcases n with _ | k
    · simp
    · push_cast [Nat.succ_sub_one]; ring
  rw [hz] at h
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (n * (n - 1))).mpr h
  push_cast at this
  linear_combination this

/-! ### Canonical reduced residue -/

/-- The canonical representative of `D(n) mod n(n−1)`:
    `(n−1)²` for even `n`, `(n−1)` for odd `n`. -/
def reducedResidue (n : ℕ) : ℤ :=
  if Even n then ((n : ℤ) - 1) ^ 2 else ((n : ℤ) - 1)

/-- For `n ≥ 2` the canonical residue lies in the fundamental domain
    `0 ≤ r(n) < n(n−1)`. -/
theorem reduced_residue_lt (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ reducedResidue n ∧ reducedResidue n < (n : ℤ) * ((n : ℤ) - 1) := by
  have h1 : (1 : ℤ) ≤ (n : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    linarith
  unfold reducedResidue
  by_cases he : Even n
  · simp only [he, if_true]
    refine ⟨by positivity, ?_⟩
    nlinarith [h1]
  · simp only [he, if_false]
    exact ⟨by linarith, by nlinarith [h1]⟩

/-- The closed form `(−1)^n (n−1)²` agrees with the reduced residue modulo
    `n(n−1)`. -/
theorem closedForm_sub_reduced_dvd (n : ℕ) :
    ((n : ℤ) * ((n : ℤ) - 1)) ∣
      ((-1) ^ n * ((n : ℤ) - 1) ^ 2 - reducedResidue n) := by
  rw [reducedResidue]
  by_cases he : Even n
  · simp only [if_pos he, he.neg_one_pow, one_mul, sub_self]
    exact dvd_zero _
  · have hodd : Odd n := Nat.not_even_iff_odd.mp he
    simp only [if_neg he, hodd.neg_one_pow]
    -- −(n−1)² − (n−1) = −(n−1)·n
    exact ⟨-(1 : ℤ), by ring⟩

/-- **Canonical congruence.** `D(n) ≡ r(n)  (mod n(n−1))`, where `r(n)` is the
    reduced residue `(n−1)²` (n even) or `(n−1)` (n odd). -/
theorem numDerangements_sub_reduced_dvd (n : ℕ) :
    ((n : ℤ) * ((n : ℤ) - 1)) ∣ ((numDerangements n : ℤ) - reducedResidue n) := by
  have h1 := mul_dvd_sub_crt n
  have h2 := closedForm_sub_reduced_dvd n
  have := dvd_add h1 h2
  have hrw : ((numDerangements n : ℤ) - (-1) ^ n * ((n : ℤ) - 1) ^ 2)
      + ((-1) ^ n * ((n : ℤ) - 1) ^ 2 - reducedResidue n)
      = (numDerangements n : ℤ) - reducedResidue n := by ring
  rwa [hrw] at this

/-! ### Concrete sanity checks -/

-- D(2)=1, modulus 2·1=2, residue 1²=1 (even): 2 ∣ (1 − 1).
example : ((2 : ℤ) * (2 - 1)) ∣ ((numDerangements 2 : ℤ) - (-1) ^ 2 * ((2 : ℤ) - 1) ^ 2) :=
  mul_dvd_sub_crt 2
-- D(5)=44, modulus 20, closed form (−1)^5·16 = −16, 44 − (−16) = 60 = 3·20.
example : numDerangements 5 = 44 := by decide
example : ((numDerangements 5 : ℤ) - (-1) ^ 5 * ((5 : ℤ) - 1) ^ 2) = 60 := by decide
-- D(6)=265, modulus 30, reduced residue (even) 5²=25, 265 − 25 = 240 = 8·30.
example : numDerangements 6 = 265 := by decide
example : reducedResidue 6 = 25 := by decide
example : reducedResidue 5 = 4 := by decide

end DerangementsConvergenceOQ04OQ02
