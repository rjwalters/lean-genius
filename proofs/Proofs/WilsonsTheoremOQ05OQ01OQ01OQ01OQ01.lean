import Mathlib

/-
# The Kempner–Smarandache function is determined by its prime powers:
# `S(n) = max over p^k ∥ n of S(p^k)`

**Open Question (`wilsons-theorem-oq-05-oq-01-oq-01-oq-01-oq-01`)**: the parent
entry `wilsons-theorem-oq-05-oq-01-oq-01-oq-01` computed the Kempner–Smarandache
value `S(p^k) = sInf {n | p^k ∣ n!}` for prime powers (e.g. `S(p^k) = p·k` iff
`k ≤ p`). Its **first** registered open question asks to *assemble the general
value*:

  > prove `S(n) = max over prime powers p^k ∥ n of S(p^k)`, i.e. that the
  > Kempner function is determined by its values on the prime powers in the
  > factorization of `n`.

This file proves exactly that. The Kempner–Smarandache function is

  `S m = sInf {n | m ∣ n !}`,

the least `n` whose factorial is divisible by `m` (identical to the parent's
definition; re-stated here so the file is self-contained — the assembly result
is independent of the *exact* prime-power values).

## Main results

* `S_mono_dvd`        : `a ∣ b → 0 < b → S a ≤ S b`  (divisibility-monotonicity).
* `S_eq_sup_prime_pow`: **`S n = ⨆_{p ∈ primeFactors n} S(p^{v_p(n)})`** for
  `n ≥ 1` — the Kempner function is the maximum of its prime-power values.
* `S_eq_S_some_prime_pow`: for `n > 1`, that maximum is *attained* by a single
  prime power: `∃ p ∣ n, S n = S(p^{v_p(n)})`.

## Engine

Two halves, by `le_antisymm`:

* `M ≤ S n`: each prime power `p^{v_p(n)} ∣ n`, so `S(p^{v_p(n)}) ≤ S n` by
  divisibility-monotonicity; take the sup.
* `S n ≤ M`: it suffices that `n ∣ M!`. By `Nat.factorization_le_iff_dvd` this is
  a pointwise valuation inequality `v_p(n) ≤ v_p(M!)` at each prime `p ∣ n`. For
  such `p`, `S(p^{v_p(n)}) ≤ M`, hence `p^{v_p(n)} ∣ (S(p^{v_p(n)}))! ∣ M!`
  (factorial-monotonicity), and Legendre (`pow_dvd_iff_le_factorization`) turns
  this divisibility into the valuation bound.
-/

open Nat

namespace WilsonsTheoremOQ05OQ01OQ01OQ01OQ01

/-! ## The Kempner–Smarandache function (matching the parent definition) -/

/-- The **Kempner–Smarandache function**: the least `n` with `m ∣ n!`. -/
noncomputable def S (m : ℕ) : ℕ := sInf {n | m ∣ n !}

/-- For `m ≥ 1`, `S m` is an actual witness: `m ∣ (S m)!`. -/
theorem dvd_factorial_S {m : ℕ} (hm : 0 < m) : m ∣ (S m)! := by
  have hne : Set.Nonempty {n | m ∣ n !} := ⟨m, Nat.dvd_factorial hm le_rfl⟩
  exact Nat.sInf_mem hne

/-- `S m` is the *least* witness: every `n` with `m ∣ n!` satisfies `S m ≤ n`. -/
theorem S_le {m n : ℕ} (h : m ∣ n !) : S m ≤ n := Nat.sInf_le h

/-! ## Divisibility-monotonicity -/

/-- **Monotonicity under divisibility.** If `a ∣ b` and `b ≥ 1`, then
`S a ≤ S b`: since `b ∣ (S b)!` and `a ∣ b`, also `a ∣ (S b)!`, so `S a ≤ S b`. -/
theorem S_mono_dvd {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : S a ≤ S b :=
  S_le (dvd_trans hab (dvd_factorial_S hb))

/-! ## Assembly: `S` is the maximum of its prime-power values -/

/-- **The Kempner function is determined by its prime powers.** For `n ≥ 1`,

  `S n = ⨆_{p ∈ primeFactors n} S(p^{v_p(n)})`,

the maximum of the Kempner values of the prime powers `p^{v_p(n)}` exactly
dividing `n`. -/
theorem S_eq_sup_prime_pow {n : ℕ} (hn : 0 < n) :
    S n = n.primeFactors.sup (fun p => S (p ^ n.factorization p)) := by
  set M := n.primeFactors.sup (fun p => S (p ^ n.factorization p)) with hM
  refine le_antisymm ?_ ?_
  · -- `S n ≤ M`, via `n ∣ M!`.
    apply S_le
    rw [← Nat.factorization_le_iff_dvd hn.ne' (Nat.factorial_ne_zero M), Finsupp.le_iff]
    intro p hp
    have hk0 : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hpp : p.Prime := by
      by_contra h
      exact hk0 (Nat.factorization_eq_zero_of_not_prime n h)
    have hmem : p ∈ n.primeFactors :=
      hpp.mem_primeFactors (Nat.dvd_of_factorization_pos hk0) hn.ne'
    -- `p^{v_p(n)} ∣ M!`
    have hSle : S (p ^ n.factorization p) ≤ M :=
      Finset.le_sup (f := fun q => S (q ^ n.factorization q)) hmem
    have hdvd : p ^ n.factorization p ∣ M ! :=
      dvd_trans (dvd_factorial_S (pow_pos hpp.pos _))
        (Nat.factorial_dvd_factorial hSle)
    -- Legendre converts divisibility to the valuation bound.
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpp (Nat.factorial_ne_zero M)).mp hdvd
  · -- `M ≤ S n`: each prime-power factor's value is `≤ S n`.
    apply Finset.sup_le
    intro p hp
    exact S_mono_dvd (Nat.ordProj_dvd n p) hn

/-- **The maximum is attained by a single prime power.** For `n > 1` there is a
prime `p ∣ n` with `S n = S(p^{v_p(n)})`: the Kempner value of `n` is realized by
one of its prime-power factors (the "dominant" prime power). -/
theorem S_eq_S_some_prime_pow {n : ℕ} (hn : 1 < n) :
    ∃ p ∈ n.primeFactors, S n = S (p ^ n.factorization p) := by
  obtain ⟨p, hp, hpe⟩ :=
    Finset.exists_mem_eq_sup n.primeFactors (Nat.nonempty_primeFactors.mpr hn)
      (fun p => S (p ^ n.factorization p))
  exact ⟨p, hp, (S_eq_sup_prime_pow (by omega)).trans hpe⟩

end WilsonsTheoremOQ05OQ01OQ01OQ01OQ01
