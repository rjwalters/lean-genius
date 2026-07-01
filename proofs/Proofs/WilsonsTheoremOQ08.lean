import Mathlib

/-!
# Wilson's Theorem OQ-08: Primality Criterion over ℕ and the Composite Factorial Congruence

The parent gallery entry states Wilson's theorem as the `ZMod n`-biconditional
`Nat.Prime n ↔ ((n-1)! : ZMod n) = -1`.  This follow-up sharpens the picture in
two elementary directions that live entirely in `ℕ`:

1. **Primality criterion over ℕ.**  For `n ≥ 2`,
   `Nat.Prime n ↔ n ∣ (n-1)! + 1`.
   This is Wilson's criterion in its classical arithmetic (divisibility) form,
   with no reference to `ZMod` or additive inverses.

2. **Composite factorial congruence.**  For a *composite* `n > 4`,
   `n ∣ (n-1)!`, i.e. `(n-1)! ≡ 0 (mod n)`.
   The single exception among composites is `n = 4`, where `3! = 6 ≡ 2 (mod 4)`.

Combining the two gives the sharp dichotomy for `n > 4`:
`Nat.Prime n ↔ ¬ n ∣ (n-1)!`.

The composite congruence is *not* in Mathlib; we build it from the elementary
combinatorial fact that two **distinct** nonzero naturals `≤ N` have product
dividing `N!` (they appear as separate factors of `N!`).  The perfect-square
subcase `n = p²` is handled by using the distinct factors `p` and `2p`, which
both lie below `n` precisely when `p ≥ 3` (equivalently `n > 4`).

All results are fully machine-checked with no additional axioms.
-/

namespace WilsonsTheoremOQ08

open Nat Finset

/-! ## Combinatorial core: distinct factors multiply into the factorial -/

/-- If `a` and `b` are distinct positive naturals, each at most `N`, then their
product divides `N !`.  They occur as two *separate* factors of the product
`N ! = ∏_{i=1}^{N} i`, so their product divides the whole product. -/
theorem mul_dvd_factorial_of_distinct {a b N : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (haN : a ≤ N) (hbN : b ≤ N) (hab : a ≠ b) : a * b ∣ N ! := by
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.Ico 1 (N + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    rcases hx with rfl | rfl <;> omega
  have hdvd := Finset.prod_dvd_prod_of_subset ({a, b} : Finset ℕ)
    (Finset.Ico 1 (N + 1)) (fun i => i) hsub
  rw [Finset.prod_Ico_id_eq_factorial] at hdvd
  rwa [Finset.prod_pair hab] at hdvd

/-! ## Composite factorial congruence -/

/-- **Composite factorial congruence.**  For composite `n > 4`, `n ∣ (n-1)!`.

Write `n = m * k` with `2 ≤ m ≤ k < n` (via the least prime factor).  If `m ≠ k`
they are distinct factors below `n`, so `n = m*k ∣ (n-1)!`.  If `m = k` then
`n = m²` with `m ≥ 3` (as `n > 4`), and the distinct factors `m`, `2m` both lie
below `n`, giving `n ∣ m*(2m) ∣ (n-1)!`. -/
theorem composite_dvd_factorial_pred {n : ℕ} (hn : 4 < n) (hcomp : ¬ Nat.Prime n) :
    n ∣ (n - 1)! := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨m, hmdvd, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 hn2 hcomp
  obtain ⟨k, hk⟩ := hmdvd          -- `n = m * k`
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> omega
    · exact h
  rcases eq_or_ne m k with hmk | hmk
  · -- perfect-square case `n = m * m`
    rw [← hmk] at hk                -- `hk : n = m * m`
    have hm3 : 3 ≤ m := by
      rcases Nat.lt_or_ge m 3 with h | h
      · interval_cases m
        omega
      · exact h
    have hmlt : m < n := by rw [hk]; nlinarith [hm3]
    have h2mlt : 2 * m < n := by rw [hk]; nlinarith [hm3]
    have hmle : m ≤ n - 1 := by omega
    have h2m : 2 * m ≤ n - 1 := by omega
    have key : m * (2 * m) ∣ (n - 1)! :=
      mul_dvd_factorial_of_distinct (by omega) (by omega) hmle h2m (by omega)
    have hndvd : n ∣ m * (2 * m) := ⟨2, by rw [hk]; ring⟩
    exact dvd_trans hndvd key
  · -- distinct proper factors `m ≠ k`
    have hkn : k < n := by rw [hk]; nlinarith [hm2, hk2]
    have hmle : m ≤ n - 1 := by omega
    have hkle : k ≤ n - 1 := by omega
    have key : m * k ∣ (n - 1)! :=
      mul_dvd_factorial_of_distinct (by omega) (by omega) hmle hkle hmk
    rwa [← hk] at key

/-- The composite congruence stated in `ZMod n`: for composite `n > 4`,
`(n-1)! ≡ 0 (mod n)`. -/
theorem composite_factorial_zmod {n : ℕ} (hn : 4 < n) (hcomp : ¬ Nat.Prime n) :
    ((n - 1)! : ZMod n) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).mpr (composite_dvd_factorial_pred hn hcomp)

/-- The exceptional composite `n = 4`: `3! = 6 ≡ 2 (mod 4)`, so `4 ∤ 3!`. -/
theorem four_factorial_pred_mod : (4 - 1)! % 4 = 2 := by decide

theorem four_not_dvd_factorial_pred : ¬ (4 ∣ (4 - 1)!) := by decide

/-! ## Wilson's primality criterion over ℕ -/

/-- **Wilson's criterion over ℕ.**  For `n ≥ 2`, `n` is prime iff `n ∣ (n-1)! + 1`.
This is the purely arithmetic form of Wilson's theorem, obtained from the
`ZMod`-biconditional by rewriting `(n-1)! ≡ -1` as `(n-1)! + 1 ≡ 0`. -/
theorem prime_iff_dvd_factorial_succ {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ n ∣ ((n - 1)! + 1) := by
  rw [Nat.prime_iff_fac_equiv_neg_one (by omega : n ≠ 1)]
  constructor
  · intro h
    have hz : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := by push_cast; rw [h]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  · intro h
    have hz : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    have h2 : ((n - 1)! : ZMod n) + 1 = 0 := by push_cast at hz; exact hz
    exact eq_neg_of_add_eq_zero_left h2

/-! ## The sharp dichotomy for `n > 4` -/

/-- **Sharp dichotomy.**  For `n > 4`, `n` is prime iff `n` does *not* divide
`(n-1)!`.  Primes fail to divide (Wilson: `(n-1)! ≡ -1`), composites divide
(the composite congruence).  The bound `n > 4` excludes only the exceptional
composite `n = 4`. -/
theorem prime_iff_not_dvd_factorial_pred {n : ℕ} (hn : 4 < n) :
    Nat.Prime n ↔ ¬ n ∣ (n - 1)! := by
  constructor
  · intro hp hcontra
    have h1 : n ∣ (n - 1)! + 1 := (prime_iff_dvd_factorial_succ (by omega)).mp hp
    have hone : n ∣ 1 := by simpa using Nat.dvd_sub h1 hcontra
    exact absurd (Nat.le_of_dvd one_pos hone) (by omega)
  · intro h
    by_contra hcomp
    exact h (composite_dvd_factorial_pred hn hcomp)

/-! ## Sanity checks -/

-- `n = 7` (prime): `6! = 720 = 7·103 - 1`, so `7 ∣ 6! + 1`.
example : (7 : ℕ) ∣ ((7 - 1)! + 1) := by decide

-- `n = 9` (composite): `8! = 40320 = 9 · 4480`, so `9 ∣ 8!`.
example : (9 : ℕ) ∣ (9 - 1)! := by decide

-- `n = 4`: the lone composite exception, `4 ∤ 3!`.
example : ¬ (4 : ℕ) ∣ (4 - 1)! := by decide

end WilsonsTheoremOQ08
