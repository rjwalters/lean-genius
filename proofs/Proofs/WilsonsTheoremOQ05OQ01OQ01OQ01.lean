import Mathlib

/-
# The Kempner–Smarandache value `S(p^k)` for prime powers via Legendre's formula

**Open Question (`wilsons-theorem-oq-05-oq-01-oq-01-oq-01`)**: the parent entry
`wilsons-theorem-oq-05-oq-01-oq-01` proved the *Kempner threshold*
`(∃ m < n, n ∣ m!) ↔ (¬ n.Prime ∧ n ≠ 4)`, i.e. it located *when* the
Kempner–Smarandache function `S(n) = min {m : n ∣ m!}` drops strictly below `n`,
but it did not compute `S(n)` itself for any composite `n`.  Its first registered
open question asks to **determine the exact value `S(p^k)` for prime powers**,
"and the role of the largest prime power dividing `n`", via Legendre's formula.

This entry does exactly that.  The Kempner–Smarandache function is

  `S m = sInf {n | m ∣ n !}`,

the least `n` whose factorial is divisible by `m`.  For a prime `p` and `k ≥ 1`
we prove, purely from Legendre's formula (the `p`-adic valuation of `n!`):

* `pow_dvd_factorial_iff`     : `p^k ∣ n! ↔ k ≤ (n!).factorization p`  (Legendre).
* `S_prime_pow_le`            : `S(p^k) ≤ p·k`.
* `prime_le_S_prime_pow`      : `p ≤ S(p^k)`.
* `prime_dvd_S_prime_pow`     : `p ∣ S(p^k)` — `S(p^k)` is *always a multiple of
  `p`* (the new increment of the valuation can only happen at a multiple of `p`).
* `S_prime_pow_eq_mul_iff`    : **`S(p^k) = p·k ↔ k ≤ p`** — the exact value on
  the largest "linear" range, and the sharp boundary where the closed form `p·k`
  first fails.
* `S_prime`                   : `S(p) = p` (the classical base case).

The engine is the Mathlib identity `Nat.factorization_factorial_mul`,
`(p·n)!.factorization p = (n!).factorization p + n`, which is Legendre's formula
read at multiples of `p`.  Combined with `factorization_factorial_eq_zero_of_lt`
(no power of `p` divides `t!` for `t < p`) it pins `S(p^k) = p·k` exactly when
`k ≤ p`, and shows `S(p^k) < p·k` for every `k > p` (the valuation of `(k-1)!`
already contributes, so `(p·(k-1))!` is divisible by `p^k`).
-/

open Nat

namespace WilsonsTheoremOQ05OQ01OQ01OQ01

/-! ## The Kempner–Smarandache function -/

/-- The **Kempner–Smarandache function**: the least `n` with `m ∣ n!`.
For `m ≥ 1` this is well defined, since `m ∣ m!`. -/
noncomputable def S (m : ℕ) : ℕ := sInf {n | m ∣ n !}

/-- For `m ≥ 1`, `S m` is an actual witness: `m ∣ (S m)!`. -/
theorem dvd_factorial_S {m : ℕ} (hm : 0 < m) : m ∣ (S m)! := by
  have hne : Set.Nonempty {n | m ∣ n !} := ⟨m, Nat.dvd_factorial hm le_rfl⟩
  exact Nat.sInf_mem hne

/-- `S m` is the *least* witness: every `n` with `m ∣ n!` satisfies `S m ≤ n`. -/
theorem S_le {m n : ℕ} (h : m ∣ n !) : S m ≤ n := Nat.sInf_le h

/-! ## Legendre's formula and the prime-power value -/

variable {p k : ℕ}

/-- A factorial splits off its top factor multiplicatively, so the `p`-valuation
of `(t+1)!` is that of `(t+1)` plus that of `t!`. -/
theorem factorization_factorial_succ_split (t : ℕ) :
    ((t + 1)!).factorization p
      = (t + 1).factorization p + (t !).factorization p := by
  rw [Nat.factorial_succ,
      Nat.factorization_mul (Nat.succ_ne_zero t) (Nat.factorial_ne_zero t),
      Finsupp.add_apply]

/-- **Legendre's divisibility criterion.**  `p^k ∣ n!` exactly when `k` does not
exceed the `p`-adic valuation `(n!).factorization p = ∑_{i≥1} ⌊n/p^i⌋`. -/
theorem pow_dvd_factorial_iff (hp : p.Prime) {n : ℕ} :
    p ^ k ∣ n ! ↔ k ≤ (n !).factorization p :=
  Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.factorial_ne_zero n)

/-- `p^k ∣ (p·k)!`: by Legendre at multiples, `(p·k)!.factorization p
= (k!).factorization p + k ≥ k`. -/
theorem prime_pow_dvd_factorial_mul (hp : p.Prime) : p ^ k ∣ (p * k)! := by
  rw [pow_dvd_factorial_iff hp, Nat.factorization_factorial_mul hp]
  exact Nat.le_add_left k _

/-- **Upper bound:** `S(p^k) ≤ p·k`. -/
theorem S_prime_pow_le (hp : p.Prime) : S (p ^ k) ≤ p * k :=
  S_le (prime_pow_dvd_factorial_mul hp)

/-- **Lower bound:** `p ≤ S(p^k)` for `k ≥ 1`, since `p ∣ p^k ∣ (S(p^k))!`
forces `p ≤ S(p^k)`. -/
theorem prime_le_S_prime_pow (hp : p.Prime) (hk : 0 < k) : p ≤ S (p ^ k) := by
  have hdvd : p ^ k ∣ (S (p ^ k))! := dvd_factorial_S (pow_pos hp.pos k)
  have hp_dvd : p ∣ (S (p ^ k))! := dvd_trans (dvd_pow_self p hk.ne') hdvd
  exact (Nat.Prime.dvd_factorial hp).mp hp_dvd

/-- **Structural fact:** `S(p^k)` is always a multiple of `p`.  The minimal `n`
with `p^k ∣ n!` must *strictly increase* the `p`-valuation of the factorial, and
that valuation only ever increases at a multiple of `p`. -/
theorem prime_dvd_S_prime_pow (hp : p.Prime) (hk : 0 < k) : p ∣ S (p ^ k) := by
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  have hp2 : 2 ≤ p := hp.two_le
  have hp_le : p ≤ S (p ^ k) := prime_le_S_prime_pow hp hk
  obtain ⟨t, ht⟩ : ∃ t, S (p ^ k) = t + 1 := ⟨S (p ^ k) - 1, by omega⟩
  have hmem : k ≤ ((t + 1)!).factorization p := by
    have h := (pow_dvd_factorial_iff hp).mp (dvd_factorial_S hpos)
    rwa [ht] at h
  have hnot : ((t)!).factorization p < k := by
    by_contra h
    push_neg at h
    have hd : p ^ k ∣ t ! := (pow_dvd_factorial_iff hp).mpr h
    have := S_le hd
    omega
  have hsplit := factorization_factorial_succ_split (p := p) t
  rw [ht]
  apply Nat.dvd_of_factorization_pos
  omega

/-- **The exact value on the linear range.**  For a prime `p` and `k ≥ 1`,
the Kempner–Smarandache value of `p^k` equals `p·k` *iff* `k ≤ p`.

For `k ≤ p` the valuation of `(k-1)!` is `0`, so `(p·(k-1))!` is *not* divisible
by `p^k` and the first multiple that works is `p·k`.  For `k > p` the valuation
of `(k-1)!` is already positive, so `(p·(k-1))!` is divisible by `p^k` and
`S(p^k) ≤ p·(k-1) < p·k`. -/
theorem S_prime_pow_eq_mul_iff (hp : p.Prime) (hk : 0 < k) :
    S (p ^ k) = p * k ↔ k ≤ p := by
  constructor
  · -- `S(p^k) = p·k → k ≤ p`, via the contrapositive.
    intro hEq
    by_contra hkp
    push_neg at hkp                       -- `p < k`
    have hpk1 : p ≤ k - 1 := by omega
    have hdvd_fact : p ∣ (k - 1)! := (Nat.Prime.dvd_factorial hp).mpr hpk1
    have hposf : 0 < ((k - 1)!).factorization p :=
      hp.factorization_pos_of_dvd (Nat.factorial_ne_zero _) hdvd_fact
    have hmul : ((p * (k - 1))!).factorization p
        = ((k - 1)!).factorization p + (k - 1) :=
      Nat.factorization_factorial_mul hp
    have hge : k ≤ ((p * (k - 1))!).factorization p := by omega
    have hdvd : p ^ k ∣ (p * (k - 1))! := (pow_dvd_factorial_iff hp).mpr hge
    have hle : S (p ^ k) ≤ p * (k - 1) := S_le hdvd
    have hcontra : p * k ≤ p * (k - 1) := hEq ▸ hle
    have hlt2 : p * (k - 1) < p * k := mul_lt_mul_of_pos_left (by omega) hp.pos
    omega
  · -- `k ≤ p → S(p^k) = p·k`.
    intro hkp
    have hle : S (p ^ k) ≤ p * k := S_prime_pow_le hp
    obtain ⟨t, ht⟩ := prime_dvd_S_prime_pow hp hk      -- `S(p^k) = p·t`
    have htk : t ≤ k := by
      have hmul : p * t ≤ p * k := ht ▸ hle
      exact le_of_mul_le_mul_left hmul hp.pos
    have hmem : p ^ k ∣ (p * t)! := by
      rw [← ht]; exact dvd_factorial_S (pow_pos hp.pos k)
    have hmemf : k ≤ ((p * t)!).factorization p := (pow_dvd_factorial_iff hp).mp hmem
    rw [Nat.factorization_factorial_mul hp] at hmemf   -- `k ≤ (t!).factorization p + t`
    rcases Nat.lt_or_ge t k with hlt | hge
    · exfalso
      have htp : t < p := by omega                     -- `t < k ≤ p`
      have hz : ((t)!).factorization p = 0 :=
        Nat.factorization_factorial_eq_zero_of_lt htp
      rw [hz] at hmemf
      omega
    · have hteq : t = k := le_antisymm htk hge
      rw [ht, hteq]

/-- **Base case (classical):** `S(p) = p` for any prime `p`. -/
theorem S_prime (hp : p.Prime) : S p = p := by
  have h := (S_prime_pow_eq_mul_iff hp one_pos).mpr hp.one_lt.le
  simpa using h

end WilsonsTheoremOQ05OQ01OQ01OQ01
