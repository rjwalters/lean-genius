import Mathlib
import Proofs.LucasTheoremOQ01OQ01

/-!
# Kummer's carry count and the zero-carry stratum of Fine's theorem

For a prime `p` and `k ≤ n`, **Kummer's theorem** (1852) identifies the exact power of `p`
dividing the binomial coefficient `C(n, k)` with the number of carries that occur when adding
`k` and `n - k` in base `p`.  Mathlib packages this as `Nat.factorization_choose`:

> `(C(n,k)).factorization p = #{ i ∈ [1, b) : pⁱ ≤ k % pⁱ + (n-k) % pⁱ }`,

the right-hand side counting exactly the carry positions.  This file builds the bridge between
that *valuation* statement and the *divisibility* statement of **Lucas' theorem**, and uses it
to recover **Fine's theorem** (`LucasTheoremOQ01OQ01`) as the **zero-carry stratum**.

## What this file adds

The parent `FineTheorem` (Fine's theorem) counts the entries of row `n` of Pascal's triangle
that survive mod `p` — i.e. `fineRow p n = { k ≤ n : ¬ p ∣ C(n,k) }` — and proves the count is
the digit product `∏ᵢ (nᵢ + 1)`.  But it never characterises *which* columns `k` survive.  That
characterisation is the content of **Lucas' divisibility criterion**, which is *not* a named
Mathlib lemma (Mathlib only has the single-digit step `Nat.dvd_choose` and the Lucas
*congruence* `Choose.choose_modEq_prod_range_choose_nat`).  We prove it here:

> **Lucas' criterion (`not_dvd_choose_iff_forall_digit_le`).**
> `¬ p ∣ C(n,k) ↔ ∀ i, (k base-p digit i) ≤ (n base-p digit i)`.

i.e. `p ∤ C(n,k)` exactly when `k` is **digit-dominated** by `n` in base `p` ("no borrow when
subtracting `k` from `n`"), with the dual divisibility statement `p ∣ C(n,k) ↔ ∃ i, nᵢ < kᵢ`.

Combining this with the Kummer valuation produces the **zero-carry stratum** linking all three
classical theorems:

> **Zero-carry stratum (`carries_eq_zero_iff_forall_digit_le`).**
> For `k ≤ n`,   `kummerCarries p n k = 0  ↔  ∀ i, kᵢ ≤ nᵢ  ↔  ¬ p ∣ C(n,k)`.

Reading the three sides: *no carries* (Kummer) `⟺` *digit dominance* (Lucas) `⟺` *survives mod
`p`* (Fine).  Finally `fineRow_eq_digitDominated` rewrites Fine's surviving set as exactly the
digit-dominated columns, so Fine's count `∏ᵢ (nᵢ + 1)` is literally the size of the zero-carry
stratum.

## Proof of Lucas' criterion

The engine is the base-`p` factorisation of Pascal's triangle.  Choose `a` with `n, k < pᵃ`.
The Lucas congruence gives `C(n,k) ≡ ∏_{i<a} C(nᵢ, kᵢ) (mod p)`, so `p ∣ C(n,k)` iff `p` divides
the product, iff `p ∣ C(nᵢ, kᵢ)` for some single digit.  For digits `nᵢ < p`, the helper
`not_dvd_choose_lt_iff` shows `p ∤ C(nᵢ, kᵢ) ↔ kᵢ ≤ nᵢ`: if `kᵢ ≤ nᵢ` then `C(nᵢ,kᵢ) ∣ nᵢ!`
and `p ∤ nᵢ!` (because `nᵢ < p`); if `kᵢ > nᵢ` then `C(nᵢ,kᵢ) = 0`.  Digit positions `i ≥ a`
contribute nothing because both digits vanish there.

## Status

All results fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.

## References
- Kummer, E. (1852). "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen."
- Lucas, É. (1878). "Théorie des fonctions numériques simplement périodiques."
- Fine, N. J. (1947). "Binomial coefficients modulo a prime." *Amer. Math. Monthly* 54.
- Granville, A. (1997). "Arithmetic properties of binomial coefficients."
-/

open Nat Finset

namespace LucasKummerCarries

/-! ## A single base-`p` digit: divisibility of `C(a, b)` for `a < p`

Within the first `p` rows of Pascal's triangle there are no multiples of `p`: every nonzero
entry `C(a, b)` with `a < p` is coprime to `p`.  Hence for such a row, `p ∣ C(a, b)` happens
*only* through the trivial vanishing `b > a`. -/

/-- For a prime `p` and a row index `a < p`, a binomial with `b ≤ a` is coprime to `p`.
`C(a,b)` divides `a!`, and `a < p` forces `p ∤ a!`. -/
theorem not_dvd_choose_of_lt {p a b : ℕ} (hp : p.Prime) (ha : a < p) (hb : b ≤ a) :
    ¬ p ∣ a.choose b := by
  intro hdvd
  have hdiv : a.choose b ∣ a ! :=
    ⟨b ! * (a - b)!, by rw [← mul_assoc]; exact (choose_mul_factorial_mul_factorial hb).symm⟩
  have hpa : p ∣ a ! := hdvd.trans hdiv
  rw [hp.dvd_factorial] at hpa
  exact absurd hpa (not_le.mpr ha)

/-- **Single-digit Lucas step.** For a prime `p` and `a < p`, the binomial `C(a, b)` is coprime
to `p` exactly when the column fits the row: `b ≤ a`.  (If `b > a` then `C(a, b) = 0`.) -/
theorem not_dvd_choose_lt_iff {p a b : ℕ} (hp : p.Prime) (ha : a < p) :
    ¬ p ∣ a.choose b ↔ b ≤ a := by
  constructor
  · intro h
    by_contra hba
    push_neg at hba
    exact h (by rw [choose_eq_zero_of_lt hba]; exact dvd_zero p)
  · exact not_dvd_choose_of_lt hp ha

/-! ## Lucas' divisibility criterion via the Lucas congruence

`p ∣ C(n,k)` is governed digit-by-digit: it occurs iff some base-`p` digit of `k` strictly
exceeds the corresponding digit of `n`.  Equivalently, `p ∤ C(n,k)` iff `k` is digit-dominated
by `n`. -/

/-- **Lucas' theorem, divisibility form.** For a prime `p`, the prime `p` divides `C(n,k)`
exactly when some base-`p` digit of `k` exceeds the corresponding digit of `n`. -/
theorem dvd_choose_iff_exists_digit_lt {p n k : ℕ} (hp : p.Prime) :
    p ∣ n.choose k ↔ ∃ i, n / p ^ i % p < k / p ^ i % p := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- A common bound `a` past which all base-`p` digits of `n` and `k` vanish.
  obtain ⟨a, hna, hka⟩ : ∃ a, n < p ^ a ∧ k < p ^ a :=
    ⟨n + k,
      lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.pow_le_pow_right hp.pos (Nat.le_add_right n k)),
      lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.pow_le_pow_right hp.pos (Nat.le_add_left k n))⟩
  -- Lucas congruence: `C(n,k) ≡ ∏ᵢ C(nᵢ, kᵢ) (mod p)`, so `p` divides one iff the other.
  have hcong := Choose.choose_modEq_prod_range_choose_nat (p := p) hna hka
  have hdvd_iff : p ∣ n.choose k ↔
      p ∣ ∏ i ∈ Finset.range a, (n / p ^ i % p).choose (k / p ^ i % p) := by
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨hcong.symm.trans, hcong.trans⟩
  rw [hdvd_iff, (hp.prime).dvd_finset_prod_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    refine ⟨i, ?_⟩
    have hlt : n / p ^ i % p < p := Nat.mod_lt _ hp.pos
    by_contra hle
    push_neg at hle
    exact not_dvd_choose_of_lt hp hlt hle hi
  · rintro ⟨i, hi⟩
    refine ⟨i, Finset.mem_range.mpr ?_, ?_⟩
    · -- Digits beyond `a` vanish, so the strict inequality forces `i < a`.
      by_contra hia
      push_neg at hia
      have hn0 : n / p ^ i % p = 0 := by
        rw [Nat.div_eq_of_lt (lt_of_lt_of_le hna (Nat.pow_le_pow_right hp.pos hia)), Nat.zero_mod]
      have hk0 : k / p ^ i % p = 0 := by
        rw [Nat.div_eq_of_lt (lt_of_lt_of_le hka (Nat.pow_le_pow_right hp.pos hia)), Nat.zero_mod]
      rw [hn0, hk0] at hi
      exact absurd hi (lt_irrefl 0)
    · rw [choose_eq_zero_of_lt hi]; exact dvd_zero p

/-- **Lucas' criterion (digit-dominance form).** For a prime `p`, the prime `p` does *not*
divide `C(n,k)` exactly when every base-`p` digit of `k` is at most the corresponding digit
of `n`.  This is the precise description of which entries of row `n` survive mod `p`. -/
theorem not_dvd_choose_iff_forall_digit_le {p n k : ℕ} (hp : p.Prime) :
    ¬ p ∣ n.choose k ↔ ∀ i, k / p ^ i % p ≤ n / p ^ i % p := by
  rw [dvd_choose_iff_exists_digit_lt hp, not_exists]
  exact forall_congr' fun i => not_lt

/-! ## Kummer's carry count and the zero-carry stratum

Kummer's theorem (`Nat.factorization_choose`) reads the `p`-adic valuation of `C(n,k)` off the
base-`p` addition of `k` and `n - k`.  We package the carry count and connect it to the
divisibility criterion above. -/

/-- The number of carries when adding `k` and `n - k` in base `p`: the positions `i ≥ 1` at
which the partial sums overflow `pⁱ`.  By Kummer's theorem this equals `ν_p(C(n,k))`. -/
def kummerCarries (p n k : ℕ) : ℕ :=
  #{i ∈ Finset.Ico 1 (n + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}

/-- **Kummer's theorem.** The exact power of `p` dividing `C(n,k)` is the number of carries
when adding `k` and `n - k` in base `p`. -/
theorem factorization_choose_eq_carries {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    (n.choose k).factorization p = kummerCarries p n k :=
  Nat.factorization_choose hp hkn (Nat.lt_succ_of_le (Nat.log_le_self p n))

/-- **Zero-carry stratum (valuation form).** For `k ≤ n`, the entry `C(n,k)` survives mod `p`
exactly when adding `k` and `n - k` in base `p` produces *no carries*. -/
theorem not_dvd_choose_iff_carries_eq_zero {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    ¬ p ∣ n.choose k ↔ kummerCarries p n k = 0 := by
  have hpos : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  rw [hp.dvd_iff_one_le_factorization hpos, factorization_choose_eq_carries hp hkn]
  omega

/-- **The bridge: no carries `⟺` digit dominance.** Combining Kummer's theorem with Lucas'
criterion, the base-`p` addition `k + (n - k)` is carry-free exactly when `k` is digit-dominated
by `n`.  Equivalently: a subtraction `n - k` in base `p` needs no borrow iff every digit of `k`
fits under the corresponding digit of `n`. -/
theorem carries_eq_zero_iff_forall_digit_le {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    kummerCarries p n k = 0 ↔ ∀ i, k / p ^ i % p ≤ n / p ^ i % p := by
  rw [← not_dvd_choose_iff_carries_eq_zero hp hkn, not_dvd_choose_iff_forall_digit_le hp]

/-! ## Recovering Fine's theorem as the zero-carry stratum

Fine's surviving set `fineRow p n` (from `LucasTheoremOQ01OQ01`) is, column by column, exactly
the set of `k ≤ n` that are digit-dominated by `n` — the zero-carry stratum.  Thus Fine's count
`∏ᵢ (nᵢ + 1)` is precisely the number of carry-free columns. -/

open scoped Classical in
/-- **Fine's surviving entries are the digit-dominated columns.** The columns `k` of row `n`
that are not divisible by `p` are exactly those whose base-`p` digits are dominated by `n`. -/
theorem fineRow_eq_digitDominated {p : ℕ} (n : ℕ) (hp : p.Prime) :
    FineTheorem.fineRow p n
      = {k ∈ Finset.range (n + 1) | ∀ i, k / p ^ i % p ≤ n / p ^ i % p} := by
  ext k
  simp only [FineTheorem.fineRow, Finset.mem_filter, Finset.mem_range]
  exact and_congr_right fun _ => not_dvd_choose_iff_forall_digit_le hp

/-! ## Worked examples (kernel-checked, no `native_decide`) -/

/-- Row `4` over `p = 2`: `4 = 100₂`.  Column `1 = 001₂` has digit `1 > 0` at position `0`,
so `2 ∣ C(4,1) = 4`. -/
example : (2 : ℕ) ∣ Nat.choose 4 1 := by decide

/-- Column `0` is always digit-dominated, so it always survives: `2 ∤ C(4,0) = 1`. -/
example : ¬ (2 : ℕ) ∣ Nat.choose 4 0 := by decide

/-- `C(6,3) = 20 = 2² · 5`: adding `3 = 11₂` to `3 = 11₂` produces two carries,
so `ν₂(C(6,3)) = 2`. -/
example : (Nat.choose 6 3).factorization 2 = 2 := by
  rw [factorization_choose_eq_carries (by norm_num) (by norm_num)]; decide

/-- Fine's surviving columns of row `5` over `p = 2` (`5 = 101₂`) are the digit-dominated
columns `{0, 1, 4, 5}`, of which there are `(1+1)(0+1)(1+1) = 4` — Fine's digit product. -/
example : (FineTheorem.fineRow 2 5).card = 4 := by decide

#check @not_dvd_choose_iff_forall_digit_le
#check @dvd_choose_iff_exists_digit_lt
#check @factorization_choose_eq_carries
#check @carries_eq_zero_iff_forall_digit_le
#check @fineRow_eq_digitDominated

end LucasKummerCarries
