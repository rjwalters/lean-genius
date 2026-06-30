import Mathlib

/-
# The composite converse of Wilson's theorem

Wilson's theorem (in Mathlib as `Nat.prime_iff_fac_equiv_neg_one`) characterises the
primes by the congruence `(n-1)! ≡ -1 (mod n)`.  Its classical *composite* counterpart
sharpens the converse: for a composite modulus the factorial collapses all the way to `0`,
with a single exception at `n = 4`.

  **For every composite `n ≠ 4` one has `n ∣ (n-1)!`** (equivalently `(n-1)! ≡ 0 mod n`).

The exception is genuine: `(4-1)! = 3! = 6` and `4 ∤ 6`.

Mathlib already proves the *weak* form used inside Wilson's theorem — a single *proper*
divisor `m` of `n` divides `(n-1)!` — which is only enough to rule out `(n-1)! ≡ -1`.
The strong statement that `n` itself divides `(n-1)!` is not in Mathlib; its proof needs
the perfect-square case `n = p²`, which is exactly where the `n = 4` exception comes from.

## Proof outline

A composite `n ≥ 2` factors as `n = m · q` with `2 ≤ m < n` (`exists_dvd_of_not_prime2`)
and `2 ≤ q < n`.

* If `m ≠ q`, the two factors are *distinct* and both `≤ n-1`, so `m·q = n` divides
  `(n-1)!` because a product of two distinct factors `≤ N` divides `N!`
  (`mul_dvd_factorial_of_lt`).
* If `m = q`, then `n = m²`.  Since `n ≠ 4` we have `m ≥ 3`, and then `m` and `2m` are
  distinct with `2m ≤ m² - 1 = n - 1`.  Hence `m·(2m) = 2n` divides `(n-1)!`, so `n` does
  too.

We also record the converse pieces (a prime never divides `(n-1)!`, by Wilson) to obtain
the full characterisation `n ∣ (n-1)! ↔ ¬ n.Prime ∧ n ≠ 4` for `n ≥ 2`.
-/

namespace WilsonsTheoremOQ03OQ02

open Nat

/-- **Two distinct factors lemma.**  If `1 ≤ a < b ≤ N` then `a * b ∣ N !`.

Both `a` and `b` occur as separate factors in `N ! = 1·2·⋯·N`: concretely `a ∣ (b-1)!`
and `b ∣ b`, so `a·b ∣ (b-1)!·b = b!`, and `b! ∣ N!` since `b ≤ N`. -/
theorem mul_dvd_factorial_of_lt {a b N : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbN : b ≤ N) :
    a * b ∣ N ! := by
  have hadvd : a ∣ (b - 1)! := Nat.dvd_factorial (by omega) (by omega)
  -- `b ! = b * (b-1)!`
  have hbb : b ! = b * (b - 1)! := by
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    simp [Nat.factorial_succ]
  have key : a * b ∣ b ! := by
    rw [hbb, Nat.mul_comm a b]
    exact mul_dvd_mul_left b hadvd
  exact key.trans (Nat.factorial_dvd_factorial hbN)

/-- **Composite converse of Wilson's theorem (strong direction).**

For every composite `n ≠ 4`, the modulus divides the factorial: `n ∣ (n-1)!`, i.e.
`(n-1)! ≡ 0 (mod n)`. -/
theorem composite_dvd_factorial_pred {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime)
    (hn4 : n ≠ 4) : n ∣ (n - 1)! := by
  obtain ⟨m, hmdvd, hm2, hmn⟩ := exists_dvd_of_not_prime2 hn hnp
  set q := n / m with hq
  have hmq : n = m * q := (Nat.mul_div_cancel' hmdvd).symm
  -- `q ≥ 2`: a proper divisor's cofactor is itself proper.
  have hqpos : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · exfalso; interval_cases q
      · simp at hmq; omega
      · rw [Nat.mul_one] at hmq; omega
    · exact h
  -- `q < n`.
  have hqn : q < n := Nat.div_lt_self (by omega) (by omega)
  rcases lt_trichotomy m q with hlt | heq | hgt
  · -- distinct factors, `m < q`
    have h := mul_dvd_factorial_of_lt (a := m) (b := q) (N := n - 1)
      (by omega) hlt (by omega)
    rwa [← hmq] at h
  · -- perfect square `n = m²`
    -- `m ≥ 3`, otherwise `m = 2` forces `n = 4`.
    have hm3 : 3 ≤ m := by
      by_contra h; push_neg at h
      have hm_eq : m = 2 := by omega
      rw [hm_eq] at hmq heq
      omega
    have hnsq : n = m * m := by rw [hmq, ← heq]
    have hbig : 2 * m + 1 ≤ m * m := by nlinarith [hm3]
    have h2m : m * (2 * m) ∣ (n - 1)! :=
      mul_dvd_factorial_of_lt (a := m) (b := 2 * m) (N := n - 1)
        (by omega) (by omega) (by rw [hnsq]; omega)
    have heq2n : m * (2 * m) = 2 * n := by rw [hnsq]; ring
    rw [heq2n] at h2m
    exact (dvd_mul_left n 2).trans h2m
  · -- distinct factors, `q < m`
    have h := mul_dvd_factorial_of_lt (a := q) (b := m) (N := n - 1)
      (by omega) hgt (by omega)
    rwa [Nat.mul_comm q m, ← hmq] at h

/-- **A prime never divides `(n-1)!`.**  Immediate from Wilson's theorem
`(n-1)! ≡ -1 (mod n)`: if also `n ∣ (n-1)!` then `-1 ≡ 0`, impossible in the field
`ZMod n`. -/
theorem prime_not_dvd_factorial_pred {n : ℕ} (hp : n.Prime) : ¬ n ∣ (n - 1)! := by
  haveI := Fact.mk hp
  intro hdvd
  have hwil : ((n - 1)! : ZMod n) = -1 :=
    (Nat.prime_iff_fac_equiv_neg_one hp.ne_one).mp hp
  have hz : ((n - 1)! : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [hwil] at hz
  exact one_ne_zero (neg_eq_zero.mp hz)

/-- **Full characterisation.**  For `n ≥ 2`, the modulus divides `(n-1)!` precisely when
`n` is composite and `n ≠ 4`:

  `n ∣ (n-1)! ↔ ¬ n.Prime ∧ n ≠ 4`.

Combined with Wilson's theorem this completely sorts the value of `(n-1)! mod n`:
`-1` for primes, `2` for `n = 4`, and `0` for every other composite. -/
theorem dvd_factorial_pred_iff {n : ℕ} (hn : 2 ≤ n) :
    n ∣ (n - 1)! ↔ ¬ n.Prime ∧ n ≠ 4 := by
  constructor
  · intro hdvd
    refine ⟨fun hp => prime_not_dvd_factorial_pred hp hdvd, ?_⟩
    rintro rfl
    exact absurd hdvd (by decide)
  · rintro ⟨hnp, hn4⟩
    exact composite_dvd_factorial_pred hn hnp hn4

end WilsonsTheoremOQ03OQ02
