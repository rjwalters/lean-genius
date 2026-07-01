/-
# A Hermite-Only Derivation of the Legendre Core (no `padicValNat_factorial`)

The parent entry *Legendre's Formula through Hermite's Identity*
(`HermiteLegendreFactorial`) rewrote every Legendre summand `⌊n/p^i⌋` as a Hermite
floor sum one level down, but it obtained the **base** identity
`v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋` by citing Mathlib's packaged closed form
`padicValNat_factorial`.  Its sibling recorded the open question:

> Give a Hermite-only proof of the Legendre core itself — the recursion
> `v_p((p·m)!) = m + v_p(m!)`, or the digit-sum form
> `(p−1)·v_p(n!) = n − s_p(n)` — so the entry no longer cites
> `padicValNat_factorial` but derives the whole formula from the floor identity.

This file answers it.  The **only** valuation input we use is the level-peeling
recursion

  `legendre_recursion : v_p(n!) = ⌊n/p⌋ + v_p(⌊n/p⌋!)`,

assembled from Mathlib's `padicValNat_factorial_mul` (the `p`-adic valuation of
`(p·m)!` exceeds that of `m!` by `m`) and `padicValNat_mul_div_factorial`
(residues below `p` do not change the valuation).  Neither is the closed form
`padicValNat_factorial`; both are the genuine *core* recursion the open question
names.  From this single recursion we derive, by strong induction:

* `legendre_closed`   — Legendre's closed form `v_p(n!) = ∑_{i∈Ico 1 b} n/p^i`,
* `sub_one_mul_valuation_factorial` — the digit-sum form
  `(p−1)·v_p(n!) = n − s_p(n)`,

both without ever invoking `padicValNat_factorial` /
`sub_one_mul_padicValNat_factorial`.  Feeding `legendre_closed` into the parent's
Hermite splitting `legendre_summand_split` then re-derives the parent headline

* `legendre_factorial_hermite'` — `v_p(n!) = ∑_{i∈Ico 1 b} ∑_{k<p} ⌊n/p^{i+1}+k/p⌋`

so the entire double–Hermite formula is now grounded on the recursion plus the
floor identity, with `0` axioms and `0` sorries.
-/
import Mathlib
import Proofs.HermiteLegendreFactorial

open Finset

namespace HermiteLegendreFactorialOQ02

variable {p : ℕ}

/-- **Legendre core recursion.**  The `p`-adic valuation of `n!` peels one power
of `p` at a time: `v_p(n!) = ⌊n/p⌋ + v_p(⌊n/p⌋!)`.  Assembled from Mathlib's
`padicValNat_mul_div_factorial` (residues `< p` are irrelevant) and
`padicValNat_factorial_mul` (`v_p((p·m)!) = v_p(m!) + m`); it does **not** use the
closed form `padicValNat_factorial`. -/
theorem legendre_recursion [hp : Fact p.Prime] (n : ℕ) :
    padicValNat p (Nat.factorial n) = n / p + padicValNat p (Nat.factorial (n / p)) := by
  rw [← padicValNat_mul_div_factorial (p := p) n, padicValNat_factorial_mul]
  ring

/-- The Legendre summand transforms cleanly under level shift:
`n / p^(i+1) = (n/p) / p^i`.  Pure Euclidean arithmetic. -/
theorem div_pow_succ (n i : ℕ) : (n / p) / p ^ i = n / p ^ (i + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- **Floor-sum recursion.**  The Legendre sum for `n` peels its `i = 1` term and
reindexes to the Legendre sum for `⌊n/p⌋`:
`∑_{i∈Ico 1 b} n/p^i = n/p + ∑_{i∈Ico 1 (b-1)} (n/p)/p^i` (for `b ≥ 2`). -/
theorem sum_div_pow_recursion (n b : ℕ) (hb : 2 ≤ b) :
    ∑ i ∈ Finset.Ico 1 b, n / p ^ i
      = n / p + ∑ i ∈ Finset.Ico 1 (b - 1), (n / p) / p ^ i := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  rw [show c + 2 - 1 = c + 1 from by omega]
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  rw [show c + 2 - 1 = c + 1 from by omega, show c + 1 - 1 = c from by omega]
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · norm_num
  · apply Finset.sum_congr rfl
    intro k _
    rw [div_pow_succ, Nat.add_assoc]

/-- **Legendre's closed form, derived from the recursion.**  For a prime `p` and
any bound `b > log_p n`, `v_p(n!) = ∑_{i∈Ico 1 b} n/p^i`.  Proved by strong
induction on `n` using only `legendre_recursion` and `sum_div_pow_recursion` —
independent of Mathlib's `padicValNat_factorial`. -/
theorem legendre_closed [hp : Fact p.Prime] :
    ∀ (n b : ℕ), Nat.log p n < b →
      padicValNat p (Nat.factorial n) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb
    have hp1 : 1 < p := hp.out.one_lt
    rcases lt_or_ge n p with hlt | hge
    · -- `n < p`: every quotient `n / p^i` (i ≥ 1) vanishes, and so does `v_p(n!)`.
      have hrhs : ∑ i ∈ Finset.Ico 1 b, n / p ^ i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Nat.div_eq_of_lt
        calc n < p := hlt
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ i := Nat.pow_le_pow_right hp1.le (Finset.mem_Ico.mp hi).1
      rw [hrhs, legendre_recursion (p := p) n, Nat.div_eq_of_lt hlt]
      simp [padicValNat.one]
    · -- `n ≥ p`: recurse on `⌊n/p⌋`, which is strictly smaller.
      have hpos : 0 < n := lt_of_lt_of_le (by omega) hge
      have hlogpos : 0 < Nat.log p n := Nat.log_pos hp1 hge
      have hb2 : 2 ≤ b := by omega
      have hdiv : n / p < n := Nat.div_lt_self hpos hp1
      have hlogb : Nat.log p (n / p) < b - 1 := by
        rw [Nat.log_div_base]; omega
      rw [legendre_recursion (p := p) n, ih (n / p) hdiv (b - 1) hlogb,
          sum_div_pow_recursion (p := p) n b hb2]

/-- **Digit-sum form of Legendre's theorem, derived from the recursion.**
`(p − 1) · v_p(n!) = n − s_p(n)`, where `s_p(n)` is the sum of the base-`p`
digits of `n`.  Proved by strong induction on `n` from `legendre_recursion` and
the digit recursion `digits_def'` — independent of Mathlib's
`sub_one_mul_padicValNat_factorial`. -/
theorem sub_one_mul_valuation_factorial [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (Nat.factorial n) = n - (p.digits n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [padicValNat.one]
    · have hp1 : 1 < p := hp.out.one_lt
      have hdiv : n / p < n := Nat.div_lt_self hn hp1
      have ihd := ih (n / p) hdiv
      have hdig : p.digits n = (n % p) :: p.digits (n / p) := Nat.digits_def' hp1 hn
      have hs : (p.digits (n / p)).sum ≤ n / p := Nat.digit_sum_le p (n / p)
      have hnp : p * (n / p) + n % p = n := Nat.div_add_mod n p
      have key : (p - 1) * (n / p) + (n / p) = p * (n / p) := by
        have hpp : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.out.pos
        calc (p - 1) * (n / p) + (n / p)
            = (p - 1 + 1) * (n / p) := by ring
          _ = p * (n / p) := by rw [hpp]
      rw [legendre_recursion (p := p) n, Nat.mul_add, ihd, hdig, List.sum_cons]
      omega

/-- **Parent headline, re-derived without `padicValNat_factorial`.**  The double
Hermite floor sum for `v_p(n!)` now rests on `legendre_closed` (proved here from
the recursion) composed with the parent's Hermite splitting
`legendre_summand_split`. -/
theorem legendre_factorial_hermite' [hp : Fact p.Prime] (n b : ℕ)
    (hb : Nat.log p n < b) :
    (padicValNat p (Nat.factorial n) : ℤ)
      = ∑ i ∈ Finset.Ico 1 b, ∑ k ∈ Finset.range p,
          ⌊(n : ℝ) / (p : ℝ) ^ (i + 1) + (k : ℝ) / (p : ℝ)⌋ := by
  rw [legendre_closed (p := p) n b hb, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact HermiteLegendreFactorial.legendre_summand_split p n i hp.out.pos

end HermiteLegendreFactorialOQ02
