/-
# Euler's totient modulo 4: characterizing `φ(n) ≡ 2 (mod 4)`

The parent entry `euler-totient-oq-06` settles the *parity* of Euler's totient
(`φ(n)` is even for `n > 2`), and the sibling `euler-totient-oq-06-oq-01`
computes the full 2-adic valuation `v₂(φ(n))` from the prime factorization of
`n`.  This file answers the mod-4 refinement:

  `φ(n) ≡ 2 (mod 4)  ⟺  v₂(φ(n)) = 1`,

and characterizes *exactly* which `n` satisfy it.

## The characterization (and a correction)

Writing `n = 2^a · m` with `m` odd, Euler's product formula gives the additive
split
  `v₂(φ(n)) = (a - 1) + ∑_{p ∣ m} v₂(p - 1)`,
where each odd prime `p ∣ m` contributes `v₂(p - 1) ≥ 1`.  For the total to be
exactly `1` there are two — not one — families of solutions:

* `a ≤ 1` and a single odd prime factor `p` with `v₂(p - 1) = 1`, i.e.
  `p ≡ 3 (mod 4)`.  This gives `n = p^k` (`a = 0`) or `n = 2·p^k` (`a = 1`).
* `a = 2` and **no** odd prime factor, i.e. `n = 4`.

The last case is easy to miss: `φ(4) = 2 ≡ 2 (mod 4)`, yet `4` is neither of the
form `p^k` nor `2·p^k` for an odd prime `p ≡ 3 (mod 4)`.  So the naive
characterization "`n = p^k` or `n = 2·p^k`" is **incomplete** — `n = 4` is a
genuine extra solution.  We prove the corrected biconditional and record `n = 4`
as an explicit counterexample to the naive form.

Main results:

* `padicValNat_two_eq_one_iff`   — the arithmetic core `v₂(m) = 1 ↔ m ≡ 2 (mod 4)`.
* `v2_totient_master`            — the split `v₂(φ n) = (a - 1) + ∑_{p ∣ oddpart} v₂(p-1)`.
* `v2_totient_eq_one_iff`        — the corrected characterization of `v₂(φ n) = 1`.
* `totient_mod_four_eq_two_iff`  — its `mod 4` restatement.
* `four_is_extra_solution`       — `n = 4` witnesses the incompleteness of the
  naive characterization.

Fully machine-checked: 0 sorries, 0 axioms.
-/
import Mathlib

open Nat Finset

namespace EulerTotientOQ06OQ02

/-! ## The arithmetic core: `v₂(m) = 1 ↔ m ≡ 2 (mod 4)` -/

/-- For every natural number `m`, its 2-adic valuation is exactly `1` iff
`m ≡ 2 (mod 4)`.  (Both sides are false at `m = 0`.) -/
theorem padicValNat_two_eq_one_iff {m : ℕ} : padicValNat 2 m = 1 ↔ m % 4 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  constructor
  · intro h
    -- `2^1 ∣ m` but `2^2 ∤ m`, hence `m % 4 = 2`.
    have hdvd : (2 : ℕ) ∣ m := by
      have := (padicValNat_dvd_iff_le hm (p := 2) (n := 1)).mpr (by omega)
      simpa using this
    have hndvd : ¬ (4 : ℕ) ∣ m := by
      intro h4
      have : (2 : ℕ) ≤ padicValNat 2 m :=
        (padicValNat_dvd_iff_le hm (p := 2) (n := 2)).mp (by simpa using h4)
      omega
    omega
  · intro h
    -- `m = 4q + 2 = 2·(2q+1)`.
    have hdvd : (2 : ℕ) ^ 1 ∣ m := by simpa using (by omega : (2 : ℕ) ∣ m)
    have hndvd : ¬ (2 : ℕ) ^ 2 ∣ m := by
      have : ¬ (4 : ℕ) ∣ m := by omega
      simpa using this
    have h1 : 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm (p := 2) (n := 1)).mp hdvd
    have h2 : ¬ 2 ≤ padicValNat 2 m := by
      intro hle
      exact hndvd ((padicValNat_dvd_iff_le hm (p := 2) (n := 2)).mpr hle)
    omega

/-! ## Prime-power building blocks -/

/-- `v₂(φ(2^a)) = a - 1`.  (For `a = 0`: `φ 1 = 1`, both sides `0`.) -/
theorem v2_tot_two_pow (a : ℕ) : padicValNat 2 (φ (2 ^ a)) = a - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two ha, show (2 : ℕ) - 1 = 1 from rfl, mul_one,
      padicValNat.prime_pow]

/-- For an odd prime `p` and `k ≥ 1`, `v₂(φ(p^k)) = v₂(p - 1)`.
The factor `p^(k-1)` is odd, so it contributes nothing. -/
theorem v2_tot_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hk : 1 ≤ k) :
    padicValNat 2 (φ (p ^ k)) = padicValNat 2 (p - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : (p - 1) ≠ 0 := by have := hp.two_le; omega
  rw [Nat.totient_prime_pow hp hk,
    padicValNat.mul (pow_ne_zero _ hp.ne_zero) hp1]
  have hz : padicValNat 2 (p ^ (k - 1)) = 0 := by
    rw [padicValNat.pow _ hp.ne_zero]
    have : padicValNat 2 p = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h =>
        hodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm)
    rw [this, mul_zero]
  rw [hz, zero_add]

/-- For an odd prime `p`, `v₂(p - 1) = 1 ⟺ p ≡ 3 (mod 4)`. -/
theorem v2_pred_eq_one_iff {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    padicValNat 2 (p - 1) = 1 ↔ p % 4 = 3 := by
  rw [padicValNat_two_eq_one_iff]
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hodd
  have := hp.two_le
  omega

/-- For an odd prime `p`, `1 ≤ v₂(p - 1)`: `p - 1` is even. -/
theorem one_le_v2_pred {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    1 ≤ padicValNat 2 (p - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hodd
  have h2le := hp.two_le
  have hp1 : (p - 1) ≠ 0 := by omega
  have hdvd : (2 : ℕ) ^ 1 ∣ (p - 1) := by
    have : (2 : ℕ) ∣ (p - 1) := by omega
    simpa using this
  exact (padicValNat_dvd_iff_le hp1 (p := 2) (n := 1)).mp hdvd

/-! ## The odd-part valuation as a sum over prime factors -/

/-- For odd `m ≠ 0`, `v₂(φ m) = ∑_{p ∣ m} v₂(p - 1)`. -/
theorem v2_tot_odd {m : ℕ} (hm : m ≠ 0) (hodd : ¬ 2 ∣ m) :
    padicValNat 2 (φ m) = ∑ p ∈ m.primeFactors, padicValNat 2 (p - 1) := by
  rw [← Nat.factorization_def _ Nat.prime_two, Nat.totient_eq_prod_factorization hm,
    Finsupp.prod, Nat.support_factorization]
  have hne : ∀ p ∈ m.primeFactors, p ^ (m.factorization p - 1) * (p - 1) ≠ 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := hpp.two_le
    exact mul_ne_zero (pow_ne_zero _ hpp.ne_zero) (by omega)
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h2le := hpp.two_le
  have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by rintro rfl; exact hodd hpdvd
  have hpow : (p ^ (m.factorization p - 1)) ≠ 0 := pow_ne_zero _ hpp.ne_zero
  have hp1 : (p - 1) ≠ 0 := by omega
  rw [Nat.factorization_mul hpow hp1, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul]
  have h2p : p.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp hdvd).symm)
  rw [h2p, mul_zero, zero_add, Nat.factorization_def _ Nat.prime_two]

/-- For odd `m ≠ 0`, `v₂(φ m) = 1 ⟺ m = p^k` for a prime `p ≡ 3 (mod 4)`, `k ≥ 1`. -/
theorem v2_tot_odd_eq_one_iff {m : ℕ} (hm : m ≠ 0) (hodd : ¬ 2 ∣ m) :
    padicValNat 2 (φ m) = 1 ↔
      ∃ p k, p.Prime ∧ p % 4 = 3 ∧ 1 ≤ k ∧ m = p ^ k := by
  rw [v2_tot_odd hm hodd]
  constructor
  · intro hsum
    -- every summand is `≥ 1`, so the index set is a singleton.
    have hpos : ∀ p ∈ m.primeFactors, 1 ≤ padicValNat 2 (p - 1) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := by
        rintro rfl; exact hodd (Nat.dvd_of_mem_primeFactors hp)
      exact one_le_v2_pred hpp hp2
    have hcardle : m.primeFactors.card ≤ 1 := by
      have := Finset.card_nsmul_le_sum m.primeFactors (fun p => padicValNat 2 (p - 1)) 1 hpos
      simpa [hsum] using this
    have hne : m.primeFactors.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.sum_empty] at hsum
      exact absurd hsum (by norm_num)
    have hcard1 : m.primeFactors.card = 1 := le_antisymm hcardle (hne.card_pos)
    obtain ⟨p, hPF⟩ := Finset.card_eq_one.mp hcard1
    -- `p ≡ 3 (mod 4)` from the single summand being `1`.
    have hterm : padicValNat 2 (p - 1) = 1 := by
      rw [hPF, Finset.sum_singleton] at hsum; exact hsum
    have hpmem : p ∈ m.primeFactors := by rw [hPF]; exact Finset.mem_singleton_self p
    have hpp := Nat.prime_of_mem_primeFactors hpmem
    have hp2 : p ≠ 2 := by rintro rfl; exact hodd (Nat.dvd_of_mem_primeFactors hpmem)
    have hp4 : p % 4 = 3 := (v2_pred_eq_one_iff hpp hp2).mp hterm
    -- `m` has a unique prime factor, so it is a prime power `p^k`.
    have hpp1 : IsPrimePow m :=
      isPrimePow_iff_card_primeFactors_eq_one.mpr hcard1
    obtain ⟨q, k, hq, hk0, hqk⟩ := (isPrimePow_nat_iff m).mp hpp1
    have h1 : (q ^ k).primeFactors = {q} := Nat.primeFactors_prime_pow hk0.ne' hq
    have hqp : q = p := by
      have : ({q} : Finset ℕ) = {p} := by rw [← h1, hqk, hPF]
      exact Finset.singleton_inj.mp this
    subst hqp
    exact ⟨q, k, hq, hp4, hk0, hqk.symm⟩
  · rintro ⟨p, k, hp, hp4, hk, rfl⟩
    have hp2 : p ≠ 2 := by intro h; rw [h] at hp4; norm_num at hp4
    rw [Nat.primeFactors_prime_pow (by omega : k ≠ 0) hp, Finset.sum_singleton]
    exact (v2_pred_eq_one_iff hp hp2).mpr hp4

/-! ## Master formula: peeling off the prime `2` -/

/-- **The 2-part / odd-part split.**  For `n ≠ 0`, writing `a = v₂(n)` and
`m = ordCompl[2] n` (the odd part of `n`),
`v₂(φ n) = (a - 1) + ∑_{p ∣ m} v₂(p - 1)`. -/
theorem v2_totient_master {n : ℕ} (hn : n ≠ 0) :
    padicValNat 2 (φ n) =
      (n.factorization 2 - 1) +
        ∑ p ∈ (ordCompl[2] n).primeFactors, padicValNat 2 (p - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := n.factorization 2 with ha
  set m := ordCompl[2] n with hm
  have hprod : 2 ^ a * m = n := ordProj_mul_ordCompl_eq_self n 2
  have hmne : m ≠ 0 := (ordCompl_pos 2 hn).ne'
  have hcop : Nat.Coprime (2 ^ a) m := (coprime_ordCompl Nat.prime_two hn).pow_left a
  have hoddm : ¬ 2 ∣ m := not_dvd_ordCompl Nat.prime_two hn
  have hφmul : φ n = φ (2 ^ a) * φ m := by rw [← hprod, Nat.totient_mul hcop]
  have h2a : φ (2 ^ a) ≠ 0 := (Nat.totient_pos.mpr (by positivity)).ne'
  have hφm : φ m ≠ 0 := (Nat.totient_pos.mpr hmne.bot_lt).ne'
  rw [hφmul, padicValNat.mul h2a hφm, v2_tot_two_pow a, v2_tot_odd hmne hoddm]

/-! ## The corrected characterization -/

/-- **Main theorem (corrected characterization).**  `v₂(φ n) = 1` — equivalently
`φ n ≡ 2 (mod 4)` — holds precisely for `n = 4` and for `n = p^k` or `n = 2·p^k`
with `p` a prime `≡ 3 (mod 4)` and `k ≥ 1`.

Note the `n = 4` case: it is *not* of the form `p^k` or `2·p^k`, so it is a
genuine extra solution missed by the naive characterization. -/
theorem v2_totient_eq_one_iff {n : ℕ} :
    padicValNat 2 (φ n) = 1 ↔
      n = 4 ∨ ∃ p k, p.Prime ∧ p % 4 = 3 ∧ 1 ≤ k ∧ (n = p ^ k ∨ n = 2 * p ^ k) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    have hn : n ≠ 0 := by rintro rfl; simp at h
    rw [v2_totient_master hn] at h
    set a := n.factorization 2 with ha
    set m := ordCompl[2] n with hm
    have hprod : 2 ^ a * m = n := ordProj_mul_ordCompl_eq_self n 2
    have hmne : m ≠ 0 := (ordCompl_pos 2 hn).ne'
    have hoddm : ¬ 2 ∣ m := not_dvd_ordCompl Nat.prime_two hn
    set S := ∑ p ∈ m.primeFactors, padicValNat 2 (p - 1) with hS
    have hφmS : padicValNat 2 (φ m) = S := v2_tot_odd hmne hoddm
    -- `(a - 1) + S = 1`, both terms `≥ 0`; case on `a`.
    have hsum : (a - 1) + S = 1 := h
    rcases (by omega : a ≤ 1 ∨ a = 2 ∨ 3 ≤ a) with hle | ha2 | hge
    · -- `a ≤ 1`, so `S = 1`: `m = p^k` with `p ≡ 3 (mod 4)`.
      have hSval : S = 1 := by omega
      obtain ⟨p, k, hp, hp4, hk, hmpk⟩ :=
        (v2_tot_odd_eq_one_iff hmne hoddm).mp (hφmS.trans hSval)
      refine Or.inr ⟨p, k, hp, hp4, hk, ?_⟩
      rcases (by omega : a = 0 ∨ a = 1) with ha0 | ha1
      · left; rw [← hprod, ha0, pow_zero, one_mul, hmpk]
      · right; rw [← hprod, ha1, pow_one, hmpk]
    · -- `a = 2`, so `S = 0`: `m = 1`, hence `n = 4`.
      have hSval : S = 0 := by omega
      have hempty : m.primeFactors = ∅ := by
        by_contra hne
        obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hp2 : p ≠ 2 := by rintro rfl; exact hoddm (Nat.dvd_of_mem_primeFactors hp)
        have : 1 ≤ padicValNat 2 (p - 1) := one_le_v2_pred hpp hp2
        have hle : padicValNat 2 (p - 1) ≤ S :=
          Finset.single_le_sum (f := fun p => padicValNat 2 (p - 1))
            (fun _ _ => Nat.zero_le _) hp
        omega
      have hm1 : m = 1 := (Nat.primeFactors_eq_empty.mp hempty).resolve_left hmne
      left; rw [← hprod, ha2, hm1]; norm_num
    · -- `a ≥ 3` forces `(a - 1) + S ≥ 2`, impossible.
      omega
  · rintro (rfl | ⟨p, k, hp, hp4, hk, hcase⟩)
    · -- `n = 4 = 2^2`.
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, v2_tot_two_pow]
    · have hp2 : p ≠ 2 := by intro h; rw [h] at hp4; norm_num at hp4
      rcases hcase with rfl | rfl
      · rw [v2_tot_odd_prime_pow hp hp2 hk]
        exact (v2_pred_eq_one_iff hp hp2).mpr hp4
      · -- `n = 2·p^k`: `φ(2·p^k) = φ 2 · φ(p^k) = φ(p^k)`.
        have hcop : Nat.Coprime 2 (p ^ k) := by
          rw [Nat.coprime_pow_right_iff (by omega)]
          exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
        rw [Nat.totient_mul hcop, show φ 2 = 1 by decide, one_mul,
          v2_tot_odd_prime_pow hp hp2 hk]
        exact (v2_pred_eq_one_iff hp hp2).mpr hp4

/-- **`mod 4` restatement.**  `φ n ≡ 2 (mod 4)` under the same characterization. -/
theorem totient_mod_four_eq_two_iff {n : ℕ} :
    φ n % 4 = 2 ↔
      n = 4 ∨ ∃ p k, p.Prime ∧ p % 4 = 3 ∧ 1 ≤ k ∧ (n = p ^ k ∨ n = 2 * p ^ k) := by
  rw [← padicValNat_two_eq_one_iff, v2_totient_eq_one_iff]

/-! ## The `n = 4` correction, made explicit -/

/-- `φ(4) ≡ 2 (mod 4)`. -/
theorem totient_four_mod_four : φ 4 % 4 = 2 := by decide

/-- **`n = 4` is a genuine extra solution.**  It satisfies `φ n ≡ 2 (mod 4)` yet
is neither `p^k` nor `2·p^k` for an odd prime `p ≡ 3 (mod 4)`.  Hence the naive
characterization "`n = p^k` or `n = 2·p^k`" is incomplete. -/
theorem four_is_extra_solution :
    φ 4 % 4 = 2 ∧
      ¬ ∃ p k, p.Prime ∧ p % 4 = 3 ∧ 1 ≤ k ∧ ((4 : ℕ) = p ^ k ∨ (4 : ℕ) = 2 * p ^ k) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨p, k, hp, hp4, hk, hcase⟩
  have hp2 : p ≠ 2 := by intro h; rw [h] at hp4; norm_num at hp4
  -- `p` is odd and `≥ 3`; neither `p^k = 4` nor `2 p^k = 4` is possible.
  have hp3 : 3 ≤ p := by
    have := hp.two_le; omega
  rcases hcase with h4 | h4
  · -- `p^k = 4 = 2^2` with `p` an odd prime forces `p ∣ 2`, impossible for `p ≥ 3`.
    have hpk : p ^ k = 4 := h4.symm
    have hdvd : p ∣ 2 := by
      have h2 : p ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 4 from rfl, ← hpk]
        exact dvd_pow_self p (by omega : k ≠ 0)
      exact hp.dvd_of_dvd_pow h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · -- `2·p^k = 4`, so `p^k = 2`, again forcing `p ∣ 2`.
    have hpk : 2 * p ^ k = 4 := h4.symm
    have hpk2 : p ^ k = 2 := by omega
    have hdvd : p ∣ 2 := hpk2 ▸ dvd_pow_self p (by omega : k ≠ 0)
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

/-! ## Sanity checks against small values -/

example : padicValNat 2 (φ 3) = 1 := (v2_totient_eq_one_iff).mpr (Or.inr ⟨3, 1, by norm_num, by norm_num, le_refl _, Or.inl (by norm_num)⟩)
example : padicValNat 2 (φ 4) = 1 := (v2_totient_eq_one_iff).mpr (Or.inl rfl)
example : padicValNat 2 (φ 6) = 1 := (v2_totient_eq_one_iff).mpr (Or.inr ⟨3, 1, by norm_num, by norm_num, le_refl _, Or.inr (by norm_num)⟩)
example : φ 5 % 4 ≠ 2 := by decide
example : φ 8 % 4 ≠ 2 := by decide
example : φ 15 % 4 ≠ 2 := by decide

end EulerTotientOQ06OQ02
