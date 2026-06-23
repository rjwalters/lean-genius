/-
# Kummer's Theorem: the Explicit Base-`p` Carry Recurrence

The parent entry (`legendre-factorial-formula-oq-01-oq-01`) restates Kummer's
theorem with a named `carryCount p a b bound`, the *count* of carries when `a` and
`b` are added in base `p`, computed via the modular condition
`pⁱ ≤ (a mod pⁱ) + (b mod pⁱ)`.  That count is correct but **non-local**: it never
exhibits a carry as something propagated, column by column, from the previous
digit.  Likewise Mathlib's `padicValNat_choose'` supplies only the same global
inequality.

This follow-up supplies the missing *local*, algorithmic layer.  It defines the
single carry **bit** `cᵢ = ⌊(m mod pⁱ + n mod pⁱ)/pⁱ⌋ ∈ {0, 1}` and proves the
schoolbook recurrence

  `c₀ = 0`,   `c_{i+1} = ⌊(dᵢ(m) + dᵢ(n) + cᵢ) / p⌋`,

where `dᵢ(x) = ⌊x / pⁱ⌋ mod p` is the `i`-th base-`p` digit of `x` — the carry is
literally `⌊(column sum + incoming carry)/p⌋`.  Neither Mathlib nor the parent
entry proves this recurrence.  From it the file recovers Kummer's valuation as a
sum of carry bits and, crucially, sharpens the parent's `carryCount = 0`
divisibility corollary to the genuinely **digitwise** no-carry criterion.

Recall the global carry condition both Mathlib and the parent use: a carry occurs
into position `i` iff

  `pⁱ ≤ (m mod pⁱ) + (n mod pⁱ)`.

What Mathlib does **not** provide is the *local*, algorithmic carry — the single
"carry bit" propagated digit-by-digit in schoolbook addition, governed by the
recurrence

  `c₀ = 0`,   `c_{i+1} = ⌊(dᵢ(m) + dᵢ(n) + cᵢ) / p⌋ ∈ {0, 1}`,

where `dᵢ(x) = ⌊x / pⁱ⌋ mod p` is the `i`-th base-`p` digit of `x`.  This file
builds that recurrence from scratch, proves it agrees with Mathlib's modular
condition, and so restates Kummer's theorem (`padicValNat_choose_eq_sum_carry`) as
a sum of the recurrence's carry bits.  As a corollary we obtain the classical
**no-carry criterion** for `p`-divisibility (`not_dvd_choose_iff_no_carry`):

  `p ∤ C(m+n, m)  ↔  dᵢ(m) + dᵢ(n) < p  for every i`,

i.e. the binomial is a `p`-adic unit exactly when adding `m` and `n` in base `p`
produces no carry at any position (Kummer / Lucas).

This refines the parent `oq-01-oq-01` Kummer carry-count entry.  Everything is
fully verified: no `sorry` and no extra axioms; the only deep input is Mathlib's
`padicValNat_choose'`.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Nat Finset

namespace LegendreFactorialFormulaOQ01OQ01OQ01

/-- The `i`-th base-`p` digit of `x`: `⌊x / pⁱ⌋ mod p`. -/
def digit (p x i : ℕ) : ℕ := x / p ^ i % p

/-- The carry **into** position `i` when adding `m` and `n` in base `p`, defined as
`⌊(m mod pⁱ + n mod pⁱ) / pⁱ⌋`.  This is the global notion of a carry used by
Mathlib's Kummer theorem; the file's main work is to show it satisfies the local
schoolbook recurrence. -/
def carry (p m n i : ℕ) : ℕ := (m % p ^ i + n % p ^ i) / p ^ i

/-- There is never a carry into the units position. -/
theorem carry_zero (p m n : ℕ) : carry p m n 0 = 0 := by
  simp [carry, Nat.mod_one]

/-- A carry is a single bit: it is always `0` or `1`.  Indeed `m mod pⁱ` and
`n mod pⁱ` are each below `pⁱ`, so their sum is below `2·pⁱ`. -/
theorem carry_le_one (p m n : ℕ) (hp : 1 ≤ p) (i : ℕ) : carry p m n i ≤ 1 := by
  have hpi : 0 < p ^ i := pow_pos (by omega) i
  have hm : m % p ^ i < p ^ i := Nat.mod_lt _ hpi
  have hn : n % p ^ i < p ^ i := Nat.mod_lt _ hpi
  have hlt : carry p m n i < 2 :=
    Nat.div_lt_of_lt_mul (by omega : m % p ^ i + n % p ^ i < p ^ i * 2)
  omega

/-- Peeling one base-`p` digit off a remainder:
`x mod p^{i+1} = x mod pⁱ + pⁱ · dᵢ(x)`. -/
theorem mod_pow_succ_eq (p x i : ℕ) :
    x % p ^ (i + 1) = x % p ^ i + p ^ i * digit p x i := by
  unfold digit
  rw [pow_succ, Nat.mod_mul]

/-- **The schoolbook carry recurrence.**  The carry into position `i+1` is `1` iff
the digit sum `dᵢ(m) + dᵢ(n)` plus the incoming carry `cᵢ` reaches `p`:

  `c_{i+1} = ⌊(dᵢ(m) + dᵢ(n) + cᵢ) / p⌋`.

This is the digit-by-digit description of carrying that Mathlib's modular form does
not expose, and it is the engine for everything below. -/
theorem carry_succ (p m n : ℕ) (hp : 1 ≤ p) (i : ℕ) :
    carry p m n (i + 1)
      = (digit p m i + digit p n i + carry p m n i) / p := by
  have hpi : 0 < p ^ i := pow_pos (by omega) i
  have hnum :
      m % p ^ i + p ^ i * digit p m i + (n % p ^ i + p ^ i * digit p n i)
        = p ^ i * (digit p m i + digit p n i) + (m % p ^ i + n % p ^ i) := by
    ring
  have key :
      (p ^ i * (digit p m i + digit p n i) + (m % p ^ i + n % p ^ i)) / (p ^ i * p)
        = (digit p m i + digit p n i + (m % p ^ i + n % p ^ i) / p ^ i) / p := by
    rw [← Nat.div_div_eq_div_mul, Nat.mul_add_div hpi]
  unfold carry
  rw [mod_pow_succ_eq, mod_pow_succ_eq, pow_succ, hnum, key]

/-- Beyond the most significant digit there are no carries: if `m + n < pⁱ` then the
carry into position `i` vanishes. -/
theorem carry_eq_zero_of_lt (p m n : ℕ) {i : ℕ} (h : m + n < p ^ i) :
    carry p m n i = 0 := by
  have hm : m < p ^ i := lt_of_le_of_lt (Nat.le_add_right m n) h
  have hn : n < p ^ i := lt_of_le_of_lt (Nat.le_add_left n m) h
  unfold carry
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn]
  exact Nat.div_eq_of_lt h

/-- The carry bit equals the indicator of Mathlib's modular carry condition
`pⁱ ≤ m mod pⁱ + n mod pⁱ`.  This bridges our recurrence-based carry to the form in
`padicValNat_choose'`. -/
theorem carry_eq_indicator (p m n : ℕ) (hp : 1 ≤ p) (i : ℕ) :
    carry p m n i = if p ^ i ≤ m % p ^ i + n % p ^ i then 1 else 0 := by
  have hpi : 0 < p ^ i := pow_pos (by omega) i
  by_cases h : p ^ i ≤ m % p ^ i + n % p ^ i
  · rw [if_pos h]
    have h2 := carry_le_one p m n hp i
    have h1 : 1 ≤ carry p m n i := by
      show 1 ≤ (m % p ^ i + n % p ^ i) / p ^ i
      exact (Nat.one_le_div_iff hpi).mpr h
    omega
  · rw [if_neg h]
    show (m % p ^ i + n % p ^ i) / p ^ i = 0
    exact Nat.div_eq_of_lt (by omega)

/-- **Kummer's theorem, carry-recurrence form.**  The `p`-adic valuation of
`C(m+n, m)` is the total number of carries arising in the base-`p` addition of `m`
and `n`, where each carry bit is the one produced by `carry_succ`.  The sum ranges
over `Ico 1 b` for any bound `b > log p (m+n)`; positions past that contribute no
carry. -/
theorem padicValNat_choose_eq_sum_carry (p m n : ℕ) {b : ℕ} [hp : Fact p.Prime]
    (hb : log p (m + n) < b) :
    padicValNat p (choose (m + n) m) = ∑ i ∈ Finset.Ico 1 b, carry p m n i := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hb' : log p (n + m) < b := by rw [Nat.add_comm n m]; exact hb
  have hkey := padicValNat_choose' (p := p) (n := n) (k := m) (b := b) hb'
  rw [Nat.add_comm m n, hkey, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => (carry_eq_indicator p m n hp1 i).symm

/-- **No carries iff every column stays below `p`.**  Driving the recurrence
`carry_succ` shows that all carries vanish exactly when the digit columns
`dᵢ(m) + dᵢ(n)` never reach `p`. -/
theorem forall_carry_zero_iff (p m n : ℕ) (hp : 1 ≤ p) :
    (∀ i, carry p m n i = 0) ↔ (∀ i, digit p m i + digit p n i < p) := by
  constructor
  · intro h i
    have hrec := carry_succ p m n hp i
    rw [h (i + 1), h i, Nat.add_zero] at hrec
    rcases (Nat.div_eq_zero_iff).mp hrec.symm with hp0 | hlt
    · omega
    · exact hlt
  · intro h i
    induction i with
    | zero => exact carry_zero p m n
    | succ k ih =>
      rw [carry_succ p m n hp k, ih, Nat.add_zero]
      exact Nat.div_eq_of_lt (h k)

/-- **Kummer / Lucas no-carry criterion.**  `C(m+n, m)` is a `p`-adic unit (i.e.
`p` does not divide it) precisely when the base-`p` addition of `m` and `n` produces
no carry — equivalently, every digit column satisfies `dᵢ(m) + dᵢ(n) < p`. -/
theorem not_dvd_choose_iff_no_carry (p m n : ℕ) [hp : Fact p.Prime] :
    ¬ (p ∣ choose (m + n) m) ↔ ∀ i, digit p m i + digit p n i < p := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hb : log p (m + n) < log p (m + n) + 1 := Nat.lt_succ_self _
  have hsum := padicValNat_choose_eq_sum_carry p m n hb
  have hCne : choose (m + n) m ≠ 0 := Nat.choose_ne_zero (Nat.le_add_right m n)
  have hdvd : (p ∣ choose (m + n) m) ↔ 1 ≤ padicValNat p (choose (m + n) m) := by
    have h := padicValNat_dvd_iff_le (p := p) (n := 1) (a := choose (m + n) m) hCne
    simpa using h
  -- Carries past the leading digit vanish, so the finite condition lifts to all `i`.
  have hext :
      (∀ i ∈ Finset.Ico 1 (log p (m + n) + 1), carry p m n i = 0)
        ↔ (∀ i, carry p m n i = 0) := by
    constructor
    · intro h i
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; exact carry_zero p m n
      · by_cases hib : i < log p (m + n) + 1
        · exact h i (Finset.mem_Ico.mpr ⟨hi, hib⟩)
        · have hlt : m + n < p ^ (log p (m + n) + 1) :=
            Nat.lt_pow_succ_log_self hp.out.one_lt (m + n)
          have hpow : p ^ (log p (m + n) + 1) ≤ p ^ i :=
            Nat.pow_le_pow_right (by omega) (by omega)
          exact carry_eq_zero_of_lt p m n (lt_of_lt_of_le hlt hpow)
    · intro h i _; exact h i
  rw [hdvd, not_le, Nat.lt_one_iff, hsum,
      Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _), hext,
      forall_carry_zero_iff p m n hp1]

/-! ### Concrete instances of the definitions

These reduce by kernel computation (`decide`), keeping the file axiom-free. -/

/-- Adding `7` and `5` in base ten carries out of the units position. -/
example : carry 10 7 5 1 = 1 := by decide

/-- No carry yet *into* the units position. -/
example : carry 10 7 5 0 = 0 := by decide

/-- The tens digit of `753` is `5`. -/
example : digit 10 753 1 = 5 := by decide

end LegendreFactorialFormulaOQ01OQ01OQ01
