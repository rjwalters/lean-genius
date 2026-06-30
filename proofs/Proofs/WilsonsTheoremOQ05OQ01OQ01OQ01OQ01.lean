import Mathlib

/-
# The Kempner–Smarandache value of a squarefree semiprime: `S(p·q) = max p q`

**Open Question (`wilsons-theorem-oq-05-oq-01-oq-01-oq-01-oq-01`)**: the parent
entry `wilsons-theorem-oq-05-oq-01-oq-01-oq-01` computed the Kempner–Smarandache
function on prime powers, proving `S(p^k) = p·k ↔ k ≤ p` and isolating the role
of the largest prime power dividing `n`.  For a general `n` the Kempner function
is the *maximum* of its values on the prime-power factors,

  `S(n) = max_{p^k ‖ n} S(p^k)`,

so the very first nontrivial multi-prime case is the squarefree semiprime
`n = p·q` with `p ≠ q` prime, where each prime appears to the first power and
`S(p) = p`, `S(q) = q`.  This entry proves the expected closed form

  `S(p·q) = max p q`     (for distinct primes `p`, `q`).

## The mathematics

The Kempner–Smarandache function is `S m = sInf {n | m ∣ n !}`, the least `n`
whose factorial is divisible by `m`.  For distinct primes `p`, `q`:

* **Upper bound `S(p·q) ≤ max p q`.**  Both `p` and `q` are `≤ max p q`, so each
  divides `(max p q)!` (a prime divides `n!` iff it is `≤ n`).  Being *distinct*
  primes they are coprime, hence their product divides `(max p q)!`.  Thus
  `max p q` is a witness and `S(p·q)` cannot exceed it.

* **Lower bound `max p q ≤ S(p·q)`.**  By definition `p·q ∣ (S(p·q))!`, so in
  particular `p ∣ (S(p·q))!` and `q ∣ (S(p·q))!`.  Since a prime divides a
  factorial only once the index reaches it, both `p ≤ S(p·q)` and `q ≤ S(p·q)`,
  i.e. `max p q ≤ S(p·q)`.

Antisymmetry gives the exact value.  As a corollary `S(p·q) = max p q < p·q`,
the **Kempner drop** for composite arguments that the grandparent threshold
theorem `(∃ m < n, n ∣ m!) ↔ (¬ n.Prime ∧ n ≠ 4)` predicts qualitatively — here
made fully explicit, with the precise value of the drop.

The engine is purely the prime-divides-factorial criterion
`Nat.Prime.dvd_factorial : p ∣ n! ↔ p ≤ n` and coprimality of distinct primes
`Nat.coprime_primes`; no Legendre valuation machinery is needed because each
prime occurs to the first power.
-/

open Nat

namespace WilsonsTheoremOQ05OQ01OQ01OQ01OQ01

/-! ## The Kempner–Smarandache function

We re-establish the minimal interface from the parent entry so this file is
self-contained: the function `S` together with its membership and minimality
witnesses. -/

/-- The **Kempner–Smarandache function**: the least `n` with `m ∣ n!`.
For `m ≥ 1` this is well defined, since `m ∣ m!`. -/
noncomputable def S (m : ℕ) : ℕ := sInf {n | m ∣ n !}

/-- For `m ≥ 1`, `S m` is an actual witness: `m ∣ (S m)!`. -/
theorem dvd_factorial_S {m : ℕ} (hm : 0 < m) : m ∣ (S m)! := by
  have hne : Set.Nonempty {n | m ∣ n !} := ⟨m, Nat.dvd_factorial hm le_rfl⟩
  exact Nat.sInf_mem hne

/-- `S m` is the *least* witness: every `n` with `m ∣ n!` satisfies `S m ≤ n`. -/
theorem S_le {m n : ℕ} (h : m ∣ n !) : S m ≤ n := Nat.sInf_le h

/-! ## The squarefree semiprime value -/

variable {p q : ℕ}

/-- **Upper bound.**  For distinct primes `p`, `q` the product `p·q` divides
`(max p q)!`: each prime is `≤ max p q` hence divides the factorial, and being
distinct primes they are coprime, so their product divides it too.  Therefore
`max p q` is a Kempner witness for `p·q`. -/
theorem semiprime_dvd_factorial_max (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    p * q ∣ (max p q)! := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpd : p ∣ (max p q)! := (hp.dvd_factorial).mpr (le_max_left p q)
  have hqd : q ∣ (max p q)! := (hq.dvd_factorial).mpr (le_max_right p q)
  exact hcop.mul_dvd_of_dvd_of_dvd hpd hqd

/-- **The Kempner–Smarandache value of a squarefree semiprime.**
For distinct primes `p`, `q`, `S(p·q) = max p q`. -/
theorem S_semiprime (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    S (p * q) = max p q := by
  -- Upper bound: `max p q` is a witness.
  have hupper : S (p * q) ≤ max p q := S_le (semiprime_dvd_factorial_max hp hq hpq)
  -- Lower bound: `p·q ∣ (S(p·q))!` forces both primes to lie below `S(p·q)`.
  have hpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hdvd : p * q ∣ (S (p * q))! := dvd_factorial_S hpos
  have hpS : p ≤ S (p * q) := (hp.dvd_factorial).mp ((dvd_mul_right p q).trans hdvd)
  have hqS : q ≤ S (p * q) := (hq.dvd_factorial).mp ((dvd_mul_left q p).trans hdvd)
  have hlower : max p q ≤ S (p * q) := max_le hpS hqS
  exact le_antisymm hupper hlower

/-- **The Kempner drop, explicitly.**  For distinct primes `p`, `q` the value
`S(p·q) = max p q` is *strictly below* `p·q`; the grandparent threshold theorem
guarantees such a drop for every composite, and here it is computed exactly. -/
theorem S_semiprime_lt_self (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    S (p * q) < p * q := by
  rw [S_semiprime hp hq hpq]
  exact max_lt (lt_mul_of_one_lt_right hp.pos hq.one_lt)
    (lt_mul_of_one_lt_left hq.pos hp.one_lt)

/-- **Symmetry.**  `S` only sees the product, so the value is symmetric in the
two primes. -/
theorem S_semiprime_comm (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    S (p * q) = S (q * p) := by
  rw [S_semiprime hp hq hpq, S_semiprime hq hp hpq.symm, max_comm]

/-! ## Sanity checks -/

/-- `S(6) = 3 = max 2 3`. -/
example : S (2 * 3) = 3 := by
  rw [S_semiprime Nat.prime_two Nat.prime_three (by norm_num)]; decide

/-- `S(15) = 5 = max 3 5`. -/
example : S (3 * 5) = 5 := by
  rw [S_semiprime Nat.prime_three (by norm_num) (by norm_num)]; decide

/-- `S(35) = 7 = max 5 7`. -/
example : S (5 * 7) = 7 := by
  rw [S_semiprime (by norm_num) (by norm_num) (by norm_num)]; decide

end WilsonsTheoremOQ05OQ01OQ01OQ01OQ01
