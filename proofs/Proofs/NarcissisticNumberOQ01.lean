/-
# Narcissistic numbers are finite  (`narcissistic-number-oq-01`)

STATUS: build-pending. Written 2026-06-16 during a Docker + Aristotle blackout
(daemon down, MCP returns 404), so this file has NOT yet been machine-checked.
It is an UNREGISTERED orphan (deliberately not imported by `Proofs.lean`), so it
cannot affect the gallery build until a future session verifies it.

A natural number `m` with `n` decimal digits is *narcissistic* when it equals the
sum of its decimal digits each raised to the `n`-th power, e.g.
`153 = 1^3 + 5^3 + 3^3`, `8208 = 8^4 + 2^4 + 0^4 + 8^4`, `9474 = 9^4+4^4+7^4+4^4`.

## Theorem (`narcissistic_finite`)
The set `{ m | Narcissistic m }` is finite.

## Proof idea
For an `n`-digit number the digit-power-sum is at most `n * 9^n`, while the number
itself is at least `10^(n-1)`. The inequality `10^(n-1) > n * 9^n` holds for all
`n ≥ 61` (Python-certified crossover, see
`research/certificates/narcissistic_number_oq01_finiteness.py`). Hence no
`n`-digit number with `n ≥ 61` can be narcissistic, so every narcissistic number
is `< 10^61`, and a set of naturals bounded above is finite.

The two genuinely arithmetic facts are isolated as `crossover` (an
`n ≥ 61` induction) and `pow_pred_length_le` (Mathlib digit lower bound). Both are
HARD-but-known, suitable for Aristotle once the prover is reachable again.
-/
import Mathlib

namespace NarcissisticNumberOQ01

open scoped BigOperators

/-- Number of decimal digits of `m` (`0` for `m = 0`). -/
def numDigits (m : ℕ) : ℕ := (Nat.digits 10 m).length

/-- `m` is narcissistic: it equals the sum of its decimal digits each raised to
the power equal to its number of digits. -/
def Narcissistic (m : ℕ) : Prop :=
  m = ((Nat.digits 10 m).map (fun d => d ^ numDigits m)).sum

/-- Every decimal digit is `≤ 9`. -/
lemma digit_le_nine {m d : ℕ} (hd : d ∈ Nat.digits 10 m) : d ≤ 9 := by
  have h : d < 10 := Nat.digits_lt_base (by norm_num) hd
  omega

/-- The digit-power-sum of `m` is at most `numDigits m * 9 ^ numDigits m`:
each of the `n` digits is `≤ 9`, so each `n`-th power is `≤ 9^n`. -/
lemma digitPowSum_le (m : ℕ) :
    ((Nat.digits 10 m).map (fun d => d ^ numDigits m)).sum
      ≤ numDigits m * 9 ^ numDigits m := by
  set n := numDigits m with hn
  have hbound : ∀ x ∈ (Nat.digits 10 m).map (fun d => d ^ n), x ≤ 9 ^ n := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact Nat.pow_le_pow_left (digit_le_nine hd) n
  calc ((Nat.digits 10 m).map (fun d => d ^ n)).sum
      ≤ ((Nat.digits 10 m).map (fun d => d ^ n)).length • (9 ^ n) :=
        List.sum_le_card_nsmul _ _ hbound
    _ = n * 9 ^ n := by
        rw [List.length_map, smul_eq_mul]; rfl

/-- Crossover bound: for `n ≥ 61`, `n * 9^n < 10^(n-1)`.

Proof plan (HARD, Aristotle-suitable): `Nat.le_induction` from `61`.
* Base `n = 61`: the concrete inequality `61 * 9^61 < 10^60`, closeable by
  `norm_num` (it evaluates both sides).
* Step: assume `n * 9^n < 10^(n-1)` with `n ≥ 61`. Then
  `(n+1) * 9^(n+1) = 9*(n+1) * 9^n ≤ 10*n * 9^n` (using `9*(n+1) ≤ 10*n`, valid
  for `n ≥ 9`) `< 10 * 10^(n-1) = 10^n`. -/
lemma crossover : ∀ n, 61 ≤ n → n * 9 ^ n < 10 ^ (n - 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have e1 : (n + 1) - 1 = n := by omega
    have e9 : (9 : ℕ) ^ (n + 1) = 9 ^ n * 9 := pow_succ 9 n
    have e10 : (10 : ℕ) ^ n = 10 ^ (n - 1) * 10 := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
    have hle : 9 * (n + 1) ≤ 10 * n := by omega
    rw [e1]
    calc (n + 1) * 9 ^ (n + 1)
        = 9 * (n + 1) * 9 ^ n := by rw [e9]; ring
      _ ≤ 10 * n * 9 ^ n := Nat.mul_le_mul hle (Nat.le_refl _)
      _ = 10 * (n * 9 ^ n) := by ring
      _ < 10 * 10 ^ (n - 1) := mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 10 ^ n := by rw [e10]; ring

/-- Digit lower bound: a nonzero `m` is at least `10^(numDigits m - 1)`.

Proof plan: from `Nat.base_pow_length_digits_le` (`10 ^ (digits).length ≤ 10 * m`
for `m ≠ 0`) cancel one factor of `10`. -/
lemma pow_pred_length_le {m : ℕ} (hm : m ≠ 0) : 10 ^ (numDigits m - 1) ≤ m := by
  have hbase : 10 ^ numDigits m ≤ 10 * m :=
    Nat.base_pow_length_digits_le 10 m (by norm_num) hm
  have hL : 0 < numDigits m :=
    List.length_pos_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hm)
  have e : numDigits m = (numDigits m - 1) + 1 := by omega
  rw [e, pow_succ] at hbase
  rw [Nat.mul_comm (10 ^ (numDigits m - 1)) 10] at hbase
  exact Nat.le_of_mul_le_mul_left hbase (by norm_num)

/-- No narcissistic number has `61` or more digits. -/
lemma numDigits_lt_61 {m : ℕ} (h : Narcissistic m) : numDigits m < 61 := by
  by_contra hge
  push_neg at hge          -- 61 ≤ numDigits m
  have hm0 : m ≠ 0 := by
    rintro rfl
    -- numDigits 0 = 0, contradicting 61 ≤ 0
    simp [numDigits] at hge
  set n := numDigits m with hn
  -- m equals its digit-power-sum, which is ≤ n * 9^n
  have hsum : m ≤ n * 9 ^ n := by
    calc m = ((Nat.digits 10 m).map (fun d => d ^ n)).sum := h
      _ ≤ n * 9 ^ n := digitPowSum_le m
  -- but m ≥ 10^(n-1) > n * 9^n, contradiction
  have hlow : 10 ^ (n - 1) ≤ m := pow_pred_length_le hm0
  have hcross : n * 9 ^ n < 10 ^ (n - 1) := crossover n hge
  omega

/-- **Narcissistic numbers are finite.** -/
theorem narcissistic_finite : {m : ℕ | Narcissistic m}.Finite := by
  apply Set.Finite.subset (Set.finite_Iio (10 ^ 61))
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  simp only [Set.mem_Iio]
  -- m < 10^(numDigits m) ≤ 10^61
  have h1 : m < 10 ^ numDigits m := by
    have := Nat.lt_base_pow_length_digits (b := 10) (m := m) (by norm_num)
    simpa [numDigits] using this
  have h2 : numDigits m < 61 := numDigits_lt_61 hm
  calc m < 10 ^ numDigits m := h1
    _ ≤ 10 ^ 61 := Nat.pow_le_pow_right (by norm_num) (le_of_lt h2)

end NarcissisticNumberOQ01
