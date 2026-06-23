/-
  Erdős Problem #277 — Prime-power non-vacuity (companion / Aristotle targets)

  See `Erdos277Problem.lean` for the main formalization. That file establishes
  non-vacuity of the corrected `ErdosQuestion277` for `n = 1`
  (`no_proper_covering_one`) and for every prime `n = p` (`no_proper_covering_prime`):
  these are values of `n` that admit **no** proper covering (distinct divisor
  moduli, each `> 1`), so they witness that the negation in the Erdős question is
  not vacuous.

  This file extends that line to **all prime powers** `n = p^k`, `k ≥ 1`.

  ## Why every prime power blocks a proper covering

  A proper covering of `p^k` uses congruences whose moduli are **distinct**
  divisors of `p^k`, each `> 1`. The divisors of `p^k` greater than `1` are
  exactly `p, p^2, …, p^k`, so the moduli are distinct powers `p^j`,
  `1 ≤ j ≤ k`. There are two standard ways to see no such covering exists:

  * **Density.** The reciprocal sum of the moduli is
    `∑ 1/p^{j} ≤ 1/p + … + 1/p^k = (1 - p^{-k})/(p-1) < 1`,
    while any covering system of ℤ has reciprocal sum `≥ 1`.

  * **Elementary induction on `k`** (used in the proof sketch below, needs no
    density theory). Base case `k = 1` is `no_proper_covering_prime`. For the
    step, split on whether the top modulus `p^k` actually occurs:
      - If it does not, every modulus divides `p^{k-1}`, so `S` is a proper
        covering of `p^{k-1}` — contradiction by the induction hypothesis.
      - If it does, let `c₀` be the unique congruence with modulus `p^k` and
        set `S' = S.erase c₀`. Every modulus in `S'` divides `p^{k-1}`, so the
        set of integers covered by `S'` is **periodic with period `p^{k-1}`**
        (`covers_add_of_dvd`). If some `x` is uncovered by `S'`, then `S` covers
        it only via `c₀`, i.e. `x ≡ c₀.residue (mod p^k)`; but `x + p^{k-1}` is
        also uncovered by `S'` (periodicity), hence also `≡ c₀.residue (mod p^k)`
        — forcing `p^k ∣ p^{k-1}`, impossible. So `S'` already covers ℤ. If
        `S' = ∅` then `S = {c₀}` is a single congruence with modulus `p^k ≥ 2`,
        which misses `c₀.residue + 1` (`single_congruence_not_covering`); else
        `S'` is a proper covering of `p^{k-1}` — contradiction by induction.

  The three supporting lemmas below (`single_congruence_not_covering`,
  `covers_add_of_dvd`, `proper_modulus_is_prime_pow`) are the reusable toolkit
  for the elementary argument; they are proved here. The headline theorem
  `no_proper_covering_prime_power` is fully proved below by the elementary
  induction on `k` (no density theory, no `sorry`, no `axiom`).
-/

import Mathlib
import Proofs.Erdos277Problem

namespace Erdos277

/-- A single congruence with modulus `≥ 2` never covers `ℤ`: it misses
    `c.residue + 1`. (Pulled out of `no_proper_covering_prime`; reusable.) -/
theorem single_congruence_not_covering (c : Congruence) (hm : c.modulus ≥ 2) :
    ¬ c.covers (c.residue + 1) := by
  intro h
  simp only [Congruence.covers] at h
  have hmeq : (c.residue + 1) ≡ c.residue [ZMOD (c.modulus : ℤ)] := h
  have hdvd1 : (c.modulus : ℤ) ∣ 1 := by
    have hh : (c.modulus : ℤ) ∣ c.residue - (c.residue + 1) := Int.ModEq.dvd hmeq
    have heq : c.residue - (c.residue + 1) = -1 := by ring
    rw [heq] at hh
    exact (dvd_neg).mp hh
  have hle : (c.modulus : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd1
  have h2 : (c.modulus : ℤ) ≥ 2 := by exact_mod_cast hm
  omega

/-- The set of integers a congruence covers is invariant under shifting by any
    multiple of its modulus: if `c.modulus ∣ d` and `c` covers `x`, then `c`
    covers `x + d`. This makes the covered-set of a family of congruences whose
    moduli all divide `d` periodic with period `d`. -/
theorem covers_add_of_dvd (c : Congruence) (x d : ℤ)
    (hdvd : (c.modulus : ℤ) ∣ d) (h : c.covers x) : c.covers (x + d) := by
  simp only [Congruence.covers] at h ⊢
  obtain ⟨t, rfl⟩ := hdvd
  rw [Int.add_mul_emod_self_left]
  exact h

/-- A modulus that is a divisor of `p^k` exceeding `1` is itself a positive
    power of `p`: `m = p^j` with `1 ≤ j ≤ k`. This is the structural fact that
    pins the moduli of a proper covering of `p^k` to the chain `p, p², …, pᵏ`. -/
theorem proper_modulus_is_prime_pow (p k : ℕ) (hp : p.Prime)
    (m : ℕ) (hm1 : m > 1) (hmd : m ∣ p ^ k) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ m = p ^ j := by
  obtain ⟨j, hjk, hmj⟩ := (Nat.dvd_prime_pow hp).mp hmd
  refine ⟨j, ?_, hjk, hmj⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    simp only [pow_zero] at hmj
    omega
  · exact hjpos

/-- **Prime-power non-vacuity.**
    No prime power `p^k` (`k ≥ 1`) admits a proper covering with distinct
    divisor moduli each `> 1`. This strengthens `no_proper_covering_prime`
    (the `k = 1` case) and shows the corrected `ErdosQuestion277` is non-vacuous
    on the infinite set of all prime powers.

    Proof (elementary induction on `k`): see the file header. The base case is
    `no_proper_covering_prime`; the inductive step uses
    `covers_add_of_dvd` and `proper_modulus_is_prime_pow`. -/
theorem no_proper_covering_prime_power (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    ¬ HasProperCoveringWithDivisorModuli (p ^ k) := by
  induction k, hk using Nat.le_induction with
  | base => rw [pow_one]; exact no_proper_covering_prime p hp
  | succ k hk ih =>
    rintro ⟨S, hcov, hdistinct, hgt, hdvd⟩
    have hp2 : 2 ≤ p := hp.two_le
    -- Every modulus of `S` other than the top one `p^(k+1)` divides `p^k`.
    have key : ∀ c ∈ S, c.modulus ≠ p ^ (k + 1) → c.modulus ∣ p ^ k := by
      intro c hc hne
      obtain ⟨j, hj1, hjk, hmj⟩ :=
        proper_modulus_is_prime_pow p (k + 1) hp c.modulus (hgt c hc) (hdvd c hc)
      have hjle : j ≤ k := by
        by_contra h
        push_neg at h
        have hjeq : j = k + 1 := by omega
        rw [hjeq] at hmj
        exact hne hmj
      rw [hmj]
      exact pow_dvd_pow p hjle
    by_cases htop : ∃ c ∈ S, c.modulus = p ^ (k + 1)
    · -- Top modulus occurs: erase it and show the rest still covers ℤ.
      obtain ⟨c₀, hc₀S, hc₀mod⟩ := htop
      have hdvd' : ∀ c ∈ S.erase c₀, c.modulus ∣ p ^ k := by
        intro c hc
        have hcS : c ∈ S := Finset.mem_of_mem_erase hc
        have hcne : c ≠ c₀ := Finset.ne_of_mem_erase hc
        refine key c hcS ?_
        intro heq
        exact hcne (hdistinct c hcS c₀ hc₀S (by rw [heq, hc₀mod]))
      have hcov' : IsCoveringSystem (S.erase c₀) := by
        intro x
        by_contra hno
        push_neg at hno
        -- `x + p^k` is also uncovered by the erased system (periodicity).
        have hnox' : ∀ c ∈ S.erase c₀, ¬ c.covers (x + (p : ℤ) ^ k) := by
          intro c hc hcc
          have hd : (c.modulus : ℤ) ∣ (p : ℤ) ^ k := by
            have h2 : (c.modulus : ℤ) ∣ ((p ^ k : ℕ) : ℤ) :=
              Int.natCast_dvd_natCast.mpr (hdvd' c hc)
            rwa [show ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k by push_cast; ring] at h2
          have h3 : c.covers ((x + (p : ℤ) ^ k) + (-(p : ℤ) ^ k)) :=
            covers_add_of_dvd c (x + (p : ℤ) ^ k) (-(p : ℤ) ^ k) (dvd_neg.mpr hd) hcc
          rw [show (x + (p : ℤ) ^ k) + (-(p : ℤ) ^ k) = x by ring] at h3
          exact hno c hc h3
        -- Then `c₀` must cover both `x` and `x + p^k`, forcing `p^(k+1) ∣ p^k`.
        obtain ⟨c, hcS, hcx⟩ := hcov x
        have hcc₀ : c = c₀ := by
          by_contra h
          exact hno c (Finset.mem_erase.mpr ⟨h, hcS⟩) hcx
        obtain ⟨c', hc'S, hc'x⟩ := hcov (x + (p : ℤ) ^ k)
        have hc'c₀ : c' = c₀ := by
          by_contra h
          exact hnox' c' (Finset.mem_erase.mpr ⟨h, hc'S⟩) hc'x
        rw [hcc₀] at hcx
        rw [hc'c₀] at hc'x
        simp only [Congruence.covers] at hcx hc'x
        have hmod : (x + (p : ℤ) ^ k) ≡ x [ZMOD (c₀.modulus : ℤ)] := by
          unfold Int.ModEq; rw [hc'x, hcx]
        have hdvdpk : (c₀.modulus : ℤ) ∣ (p : ℤ) ^ k := by
          have hd := Int.modEq_iff_dvd.mp hmod
          rw [show x - (x + (p : ℤ) ^ k) = -(p : ℤ) ^ k by ring] at hd
          exact (dvd_neg).mp hd
        have hdvdN : c₀.modulus ∣ p ^ k := by
          have h2 : (c₀.modulus : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
            rwa [show ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k by push_cast; ring]
          exact_mod_cast h2
        rw [hc₀mod] at hdvdN
        have hppos : 0 < p ^ k := pow_pos hp.pos k
        have hmul : p ^ k * p ≤ p ^ k * 1 := by
          rw [mul_one, ← pow_succ]; exact Nat.le_of_dvd hppos hdvdN
        have hp1 : p ≤ 1 := Nat.le_of_mul_le_mul_left hmul hppos
        omega
      -- The erased system is a proper covering of `p^k`: contradiction by IH.
      exact ih ⟨S.erase c₀, hcov',
        fun c₁ h₁ c₂ h₂ hmeq =>
          hdistinct c₁ (Finset.mem_of_mem_erase h₁) c₂ (Finset.mem_of_mem_erase h₂) hmeq,
        fun c hc => hgt c (Finset.mem_of_mem_erase hc), hdvd'⟩
    · -- Top modulus absent: every modulus divides `p^k`, so `S` covers `p^k`.
      exact ih ⟨S, hcov, hdistinct, hgt,
        fun c hc => key c hc (fun heq => htop ⟨c, hc, heq⟩)⟩

end Erdos277
