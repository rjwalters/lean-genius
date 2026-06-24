import Mathlib

/-
# The Kempner–Smarandache value of a squarefree semiprime: `S(pq) = max(p, q)`

**Open Question (`wilsons-theorem-oq-05-oq-01-oq-01-oq-01-oq-01`)**: the parent
entry `wilsons-theorem-oq-05-oq-01-oq-01-oq-01` computed the Kempner–Smarandache
function

  `S m = sInf {n | m ∣ n !}`

on **prime powers** (`S(p^k) = p·k ⟺ k ≤ p`) via Legendre's formula.  Its first
registered open question asks to assemble the general value
`S(n) = max_{p^k ∥ n} S(p^k)`, i.e. that `S` is determined by the prime-power
components in the factorization of `n`.

This entry proves the first nontrivial instance of that maximum-over-prime-powers
principle: the **squarefree-semiprime** case.  For two *distinct* primes `p ≠ q`,

  `S(p·q) = max(p, q) = max(S(p), S(q))`.

The smallest case where two different primes compete, it isolates the coprimality
(CRT-style independence) argument without the Legendre bookkeeping needed for
higher prime powers.

## Proof outline

By symmetry it suffices to treat `p < q` and show `S(p·q) = q`.

* **Upper bound** `S(p·q) ≤ q`.  Both prime factors already appear in `q!`:
  `p ∣ q!` because `p ≤ q` (`Nat.Prime.dvd_factorial`), and `q ∣ q!` trivially.
  Since `p` and `q` are distinct primes they are coprime, so
  `p·q ∣ q!` (`Nat.Coprime.mul_dvd_of_dvd_of_dvd`); `q` is therefore a witness for
  `S(p·q)`, giving `S(p·q) ≤ q` via `S_le`.

* **Lower bound** `q ≤ S(p·q)`.  The value `S(p·q)` is a genuine witness, so
  `p·q ∣ (S(p·q))!` (`dvd_factorial_S`); hence `q ∣ (S(p·q))!`, and since `q` is
  prime, `Nat.Prime.dvd_factorial` forces `q ≤ S(p·q)`.

Antisymmetry then pins `S(p·q) = q`.  The main theorem dispatches the two orders
of `p, q` by trichotomy, using `mul_comm` and `max_comm` for the `q < p` branch.

We restate the `S` definition together with the two parent-leaf API lemmas
`dvd_factorial_S` (the value is a witness) and `S_le` (it is the least witness),
so the file is self-contained and `0`-axiom.
-/

open Nat

namespace WilsonsTheoremOQ05OQ01OQ01OQ01OQ01

/-! ## The Kempner–Smarandache function (restated from the parent leaf) -/

/-- The **Kempner–Smarandache function**: the least `n` with `m ∣ n!`.
For `m ≥ 1` this is well defined, since `m ∣ m!`. -/
noncomputable def S (m : ℕ) : ℕ := sInf {n | m ∣ n !}

/-- For `m ≥ 1`, `S m` is an actual witness: `m ∣ (S m)!`. -/
theorem dvd_factorial_S {m : ℕ} (hm : 0 < m) : m ∣ (S m)! := by
  have hne : Set.Nonempty {n | m ∣ n !} := ⟨m, Nat.dvd_factorial hm le_rfl⟩
  exact Nat.sInf_mem hne

/-- `S m` is the *least* witness: every `n` with `m ∣ n!` satisfies `S m ≤ n`. -/
theorem S_le {m n : ℕ} (h : m ∣ n !) : S m ≤ n := Nat.sInf_le h

/-! ## The squarefree-semiprime value -/

/-- **Core case `p < q`.**  For distinct primes with `p < q`, the larger prime `q`
is exactly the Kempner–Smarandache value of the semiprime `p·q`. -/
theorem S_mul_primes_of_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    S (p * q) = q := by
  have hpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  -- Upper bound: `p·q ∣ q!`, so `q` is a witness for `S (p*q)`.
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hlt.ne
  have hpd : p ∣ q ! := (Nat.Prime.dvd_factorial hp).mpr hlt.le
  have hqd : q ∣ q ! := Nat.dvd_factorial hq.pos le_rfl
  have hpqd : p * q ∣ q ! := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpd hqd
  have hub : S (p * q) ≤ q := S_le hpqd
  -- Lower bound: `q ∣ p·q ∣ (S (p*q))!`, and `q` prime forces `q ≤ S (p*q)`.
  have hdvd : p * q ∣ (S (p * q))! := dvd_factorial_S hpos
  have hqdvd : q ∣ (S (p * q))! := dvd_trans (dvd_mul_left q p) hdvd
  have hlb : q ≤ S (p * q) := (Nat.Prime.dvd_factorial hq).mp hqdvd
  exact le_antisymm hub hlb

/-- **The squarefree-semiprime Kempner–Smarandache value.**  For two distinct
primes `p ≠ q`, the least `n` with `p·q ∣ n!` is the larger of the two primes:
`S(p·q) = max(p, q)`. -/
theorem S_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    S (p * q) = max p q := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · -- `p < q`: `max p q = q`.
    rw [max_eq_right hlt.le]
    exact S_mul_primes_of_lt hp hq hlt
  · -- `q < p`: `max p q = p`; reduce to the core case on `q·p`.
    rw [max_eq_left hgt.le, mul_comm]
    exact S_mul_primes_of_lt hq hp hgt

/-- Reformulation exhibiting the maximum-over-prime-powers principle in this case:
`S(p·q) = max (S p) (S q)`, using the base value `S(p) = p` from the parent leaf. -/
theorem S_mul_primes_eq_max_S {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : S (p * q) = max (S p) (S q) := by
  have hSp : S p = p := by
    refine le_antisymm (S_le (Nat.dvd_factorial hp.pos le_rfl)) ?_
    exact (Nat.Prime.dvd_factorial hp).mp (dvd_factorial_S hp.pos)
  have hSq : S q = q := by
    refine le_antisymm (S_le (Nat.dvd_factorial hq.pos le_rfl)) ?_
    exact (Nat.Prime.dvd_factorial hq).mp (dvd_factorial_S hq.pos)
  rw [hSp, hSq]
  exact S_mul_primes hp hq hpq

end WilsonsTheoremOQ05OQ01OQ01OQ01OQ01
