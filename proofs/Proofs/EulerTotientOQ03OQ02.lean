import Mathlib

/-
# A lower bound for Euler's totient: `φ(n) ≥ √n` for `n > 6`

`euler-totient-oq-03-oq-02`

The gallery entry `euler-totient-oq-03` ("Structural Properties: Parity, Divisibility,
and the Product Formula") lists, among its open questions:

> "Is there a Lean proof that `φ(n) ≥ √n` for all `n > 6`? This would require bounding
>  the product formula from below using prime number estimates."

This file answers that question.  The cleanest formulation avoids real square roots
entirely by squaring: `φ(n) ≥ √n` is, for natural numbers, exactly

    `n ≤ φ(n)²`.

The two genuine exceptions are `n = 2` (`φ(2)² = 1 < 2`) and `n = 6`
(`φ(6)² = 4 < 6`); for every other `n` — in particular every `n > 6` — the bound holds.

## Proof strategy (no analytic prime estimates needed)

`f(n) = φ(n)²/n` is multiplicative, so the bound reduces to prime powers.  For an
**odd** prime power `pᵏ` (`p ≥ 3`) one has `pᵏ ≤ φ(pᵏ)²` with room to spare, while the
only deficient prime power is `2¹`.  Writing `n = 2ᵏ·m` with `m` odd:

* the **odd part** always satisfies `m ≤ φ(m)²`, and in fact `2m ≤ φ(m)²` once `m ∉ {1,3}`
  (proved together by induction on the multiplicative structure of `m`, via
  `Nat.recOnPosPrimePosCoprime`);
* gluing in the `2`-part: for `k ≥ 2` the factor `2^{2k-2}` already dominates `2ᵏ`, and
  for `k = 1` the hypothesis `n > 6` forces `m ≥ 5`, so the sharper odd bound `2m ≤ φ(m)²`
  closes the gap.

Everything is elementary `Nat` arithmetic on top of Mathlib's `Nat.totient` API — no
prime-counting or analytic input is required, contrary to the question's expectation.

## What is proved (fully verified: 0 axioms, 0 sorries)

* `totient_sq_ge_self`   — `6 < n → n ≤ φ(n)²` (the squared, exception-free form).
* `sqrt_le_totient`      — `6 < n → √n ≤ φ(n)` (the literal statement, over `ℝ`).
* `phi_sq_ge_self_of_odd` / `phi_sq_ge_two_mul_of_odd` — the odd-part lemmas, of
  independent interest (`m ≤ φ(m)²` for all odd `m`; `2m ≤ φ(m)²` for odd `m ∉ {1,3}`).
-/

open Nat

namespace EulerTotientOQ03OQ02

/-! ## Arithmetic kernels for the prime-power estimate

With `q = p^{k-1} ≥ 1` and `a = p-1`, a prime power is `pᵏ = q·(a+1)` and
`φ(pᵏ) = q·a`.  The required inequalities become subtraction-free statements in `q, a`. -/

private lemma le_self_mul (q a : ℕ) (hq : 1 ≤ q) : a ≤ q * a := by
  have := Nat.mul_le_mul hq (le_refl a); simpa using this

private lemma arith_self (q a : ℕ) (hq : 1 ≤ q) (ha : 2 ≤ a) :
    q * (a + 1) ≤ (q * a) ^ 2 := by
  have e1 : a + 1 ≤ a * a := by nlinarith [ha]
  have e2 : a ≤ q * a := le_self_mul q a hq
  calc q * (a + 1) ≤ q * (a * a) := Nat.mul_le_mul (le_refl q) e1
    _ = q * a * a := by ring
    _ ≤ q * a * (q * a) := Nat.mul_le_mul (le_refl (q * a)) e2
    _ = (q * a) ^ 2 := by ring

private lemma arith_two_of_a (q a : ℕ) (hq : 1 ≤ q) (ha : 3 ≤ a) :
    2 * (q * (a + 1)) ≤ (q * a) ^ 2 := by
  have e1 : 2 * (a + 1) ≤ a * a := by nlinarith [ha]
  have e2 : a ≤ q * a := le_self_mul q a hq
  calc 2 * (q * (a + 1)) = q * (2 * (a + 1)) := by ring
    _ ≤ q * (a * a) := Nat.mul_le_mul (le_refl q) e1
    _ = q * a * a := by ring
    _ ≤ q * a * (q * a) := Nat.mul_le_mul (le_refl (q * a)) e2
    _ = (q * a) ^ 2 := by ring

private lemma arith_two_of_q (q a : ℕ) (hq : 2 ≤ q) (ha : 2 ≤ a) :
    2 * (q * (a + 1)) ≤ (q * a) ^ 2 := by
  have e0 : a + 1 ≤ a * a := by nlinarith [ha]
  calc 2 * (q * (a + 1)) ≤ q * (q * (a + 1)) := Nat.mul_le_mul hq (le_refl _)
    _ = q * q * (a + 1) := by ring
    _ ≤ q * q * (a * a) := Nat.mul_le_mul (le_refl (q * q)) e0
    _ = (q * a) ^ 2 := by ring

/-! ## The odd-part induction

A single induction proves both `m ≤ φ(m)²` and the sharpened `2m ≤ φ(m)²` (away from the
two small exceptions `m = 1, 3`).  We carry the disjunction `m = 1 ∨ m = 3 ∨ 2m ≤ φ(m)²`
so that the multiplicative step has enough slack to recombine. -/

private def OddBound (m : ℕ) : Prop :=
  Odd m → m ≤ (Nat.totient m) ^ 2 ∧ (m = 1 ∨ m = 3 ∨ 2 * m ≤ (Nat.totient m) ^ 2)

private lemma oddBound_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    OddBound (p ^ k) := by
  intro hodd
  -- An odd prime power has odd base, so `p ≥ 3`.
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
    have h2 : 2 ^ k % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | hodd'
    · exact absurd h hp2
    · have := hp.two_le; omega
  -- Set `a = p - 1 ≥ 2`, `q = p^{k-1} ≥ 1`; then `p^k = q*(a+1)`, `φ(p^k) = q*a`.
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  have ha : 2 ≤ a := by omega
  obtain ⟨q, hq_def⟩ : ∃ q, q = (a + 1) ^ (k - 1) := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by
    rw [hq_def]; exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hpk : (a + 1) ^ k = q * (a + 1) := by
    rw [hq_def, ← pow_succ]; congr 1; omega
  have hphi : Nat.totient ((a + 1) ^ k) = q * a := by
    rw [Nat.totient_prime_pow hp hk, ← hq_def, Nat.add_sub_cancel]
  rw [hphi, hpk]
  refine ⟨arith_self q a hq1 ha, ?_⟩
  -- Disjunction: either `p^k = 3` (i.e. `a = 2, k = 1`) or `2·p^k ≤ φ(p^k)²`.
  by_cases hexc : a = 2 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := hexc
    right; left; rw [hq_def]; norm_num
  · refine Or.inr (Or.inr ?_)
    rcases lt_or_ge a 3 with hlt | hge
    · -- `a = 2`, so `p = 3`; then `hexc` forces `k ≥ 2`, giving `q ≥ 2`.
      have ha2 : a = 2 := by omega
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · exact absurd ⟨ha2, by omega⟩ hexc
        · exact h
      have hq2 : 2 ≤ q := by
        rw [hq_def, ha2]
        calc 2 ≤ 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact arith_two_of_q q a hq2 ha
    · exact arith_two_of_a q a hq1 hge

private lemma oddBound_one : OddBound 1 := by
  intro _; refine ⟨by simp, Or.inl rfl⟩

private lemma oddBound_coprime (a b : ℕ) (ha1 : 1 < a) (hb1 : 1 < b)
    (hcop : Nat.Coprime a b) (iha : OddBound a) (ihb : OddBound b) :
    OddBound (a * b) := by
  intro hodd
  obtain ⟨hoa, hob⟩ := Nat.odd_mul.mp hodd
  obtain ⟨hsa, hda⟩ := iha hoa
  obtain ⟨hsb, hdb⟩ := ihb hob
  have hφ : Nat.totient (a * b) = Nat.totient a * Nat.totient b := Nat.totient_mul hcop
  have hsq : (Nat.totient (a * b)) ^ 2 = (Nat.totient a) ^ 2 * (Nat.totient b) ^ 2 := by
    rw [hφ, mul_pow]
  -- The product `a*b ≥ 4 > 3`, so we must land in the `2·(a*b) ≤ φ²` disjunct.
  refine ⟨by rw [hsq]; exact Nat.mul_le_mul hsa hsb, Or.inr (Or.inr ?_)⟩
  rw [hsq, mul_comm 2 (a * b), mul_assoc]
  -- `a, b` are both `> 1`, so they fall in the `a = 3 ∨ 2a ≤ φ(a)²` shape.
  have hda' : a = 3 ∨ 2 * a ≤ (Nat.totient a) ^ 2 := hda.resolve_left (by omega)
  have hdb' : b = 3 ∨ 2 * b ≤ (Nat.totient b) ^ 2 := hdb.resolve_left (by omega)
  rcases hdb' with hb3 | hb2
  · -- `b = 3`: then `a` is coprime to `3`, hence `a ≠ 3`, so `a` has the sharp slack.
    subst hb3
    have hane3 : a ≠ 3 := by
      rintro rfl
      exact absurd hcop (by decide)
    have ha2 : 2 * a ≤ (Nat.totient a) ^ 2 := hda'.resolve_left hane3
    have hφ3 : Nat.totient 3 = 2 := by decide
    rw [hφ3]
    -- Goal: `a * (3 * 2) ≤ φ(a)² * 2²`, i.e. `6a ≤ 4·φ(a)²`; from `2a ≤ φ(a)²`.
    nlinarith [ha2]
  · -- `2b ≤ φ(b)²`: combine with `a ≤ φ(a)²`.
    calc a * (b * 2) = a * (2 * b) := by ring
      _ ≤ (Nat.totient a) ^ 2 * (Nat.totient b) ^ 2 := Nat.mul_le_mul hsa hb2

private lemma oddBound_all (m : ℕ) : OddBound m :=
  Nat.recOnPosPrimePosCoprime oddBound_prime_pow (fun h => absurd h (by decide))
    oddBound_one oddBound_coprime m

/-- **Odd totient lower bound.** For every odd `m`, `m ≤ φ(m)²` (equivalently `φ(m) ≥ √m`).
No exceptions: the small odd values check directly (`1 ≤ 1`, `3 ≤ 4`, `5 ≤ 16`, …). -/
theorem phi_sq_ge_self_of_odd {m : ℕ} (hm : Odd m) : m ≤ (Nat.totient m) ^ 2 :=
  (oddBound_all m hm).1

/-- **Sharpened odd bound.** For odd `m` other than `1` and `3`, even `2m ≤ φ(m)²` holds.
(`m = 1` gives `2 ≤ 1` and `m = 3` gives `6 ≤ 4`, the two genuine failures.) -/
theorem phi_sq_ge_two_mul_of_odd {m : ℕ} (hm : Odd m) (h1 : m ≠ 1) (h3 : m ≠ 3) :
    2 * m ≤ (Nat.totient m) ^ 2 := by
  have h := (oddBound_all m hm).2
  rcases h with h | h | h
  · exact absurd h h1
  · exact absurd h h3
  · exact h

/-! ## The full bound via the `2`-adic decomposition -/

/-- **`φ(n) ≥ √n` for `n > 6`, squared form.**  For every `n > 6`, `n ≤ φ(n)²`.
The two genuine exceptions to `n ≤ φ(n)²` are `n = 2` and `n = 6`, both excluded by
`n > 6`. -/
theorem totient_sq_ge_self {n : ℕ} (hn : 6 < n) : n ≤ (Nat.totient n) ^ 2 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  -- `m` is odd, so `2ᵏ` and `m` are coprime.
  have hcop : Nat.Coprime (2 ^ k) m := by
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    have hm1 : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  have hφ : Nat.totient (2 ^ k * m) = Nat.totient (2 ^ k) * Nat.totient m :=
    Nat.totient_mul hcop
  have hmpos : 0 < m := hm.pos
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: `n = m` is odd; apply the odd bound.
    subst hk0
    simpa using phi_sq_ge_self_of_odd hm
  · -- `k = j + 1 ≥ 1`: `φ(2ᵏ) = 2ʲ`.
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hφ2 : Nat.totient (2 ^ (j + 1)) = 2 ^ j := by
      rw [Nat.totient_prime_pow_succ Nat.prime_two]; norm_num
    rw [hφ, hφ2, mul_pow]
    -- Goal: `2^{j+1} * m ≤ (2^j)² * φ(m)² = 2^{2j} * φ(m)²`.
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- `j = 0`, i.e. `k = 1`, `n = 2m > 6` ⟹ `m ≥ 5`, so `m ∉ {1,3}`.
      subst hj0
      have hm5 : 5 ≤ m := by
        rcases hm with ⟨t, rfl⟩; omega
      have := phi_sq_ge_two_mul_of_odd hm (by omega) (by omega)
      simpa using this
    · -- `j ≥ 1`: `2^{j+1} ≤ 2^{2j}` dominates, and `m ≤ φ(m)²`.
      have hpow : 2 ^ (j + 1) ≤ (2 ^ j) ^ 2 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmm : m ≤ (Nat.totient m) ^ 2 := phi_sq_ge_self_of_odd hm
      calc 2 ^ (j + 1) * m ≤ (2 ^ j) ^ 2 * (Nat.totient m) ^ 2 :=
            Nat.mul_le_mul hpow hmm
        _ = (2 ^ j) ^ 2 * (Nat.totient m) ^ 2 := rfl

/-- **`φ(n) ≥ √n` for `n > 6`** — the literal statement over the reals.  Immediate from
the squared form `totient_sq_ge_self` by taking square roots. -/
theorem sqrt_le_totient {n : ℕ} (hn : 6 < n) :
    Real.sqrt n ≤ (Nat.totient n : ℝ) := by
  have h : (n : ℝ) ≤ (Nat.totient n : ℝ) ^ 2 := by exact_mod_cast totient_sq_ge_self hn
  calc Real.sqrt n ≤ Real.sqrt ((Nat.totient n : ℝ) ^ 2) := Real.sqrt_le_sqrt h
    _ = (Nat.totient n : ℝ) := Real.sqrt_sq (by positivity)

end EulerTotientOQ03OQ02
