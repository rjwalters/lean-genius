/-
  Erdős Problem #1002 — OQ-04, capstone: a single fixed Liouville number with
  unbounded inner sum.

  `Erdos1002OQ04` proves the *perturbation lemma* and deduces that the inner sum
      S(α, n) = Σ_{k=1}^{n} (1/2 − {αk})
  is unbounded *near every rational*: for every reduced `p/q` and every height `M`
  there exists an irrational `α > p/q` (depending on `M`) with `S(α, n) > M`.

  That statement leaves the witness `α` depending on `M`.  This file upgrades it to
  the genuine Liouville phenomenon: a **single, explicit** irrational number whose
  inner sum is unbounded along a sequence `n → ∞`.  We take Liouville's constant

      α = liouvilleNumber 10 = Σ_{i≥0} 10^{-i!}   (`Mathlib.NumberTheory…LiouvilleNumber`).

  Its partial sums `partialSum 10 k = p_k / 10^{k!}` approximate `α` **from below**
  (the remainder `α − partialSum 10 k = remainder 10 k > 0` is a sum of positive
  terms), which is exactly the one-sided hypothesis `p/q < α` of `innerSum_perturb`.
  The remainder decays super-geometrically, `remainder 10 k < 1/(10^{k!})^k`, so the
  approximation budget `1/(Nq)²` is met with room to spare.  Reducing `p_k/10^{k!}`
  to lowest terms and feeding it to `innerSum_perturb` yields, for every `M`, an `N`
  and a spike `S(α, N·q') > N/2 − 1 > M`.

  The height `N` (controlling `N/2 − 1 > M`) and the approximation depth `k`
  (controlling `remainder 10 k · (Nq')² < 1`) are chosen independently, which keeps
  the numeric estimate elementary.

  Status: 0 sorries, 0 axioms.  Reuses `Erdos1002OQ04.innerSum_perturb` and
  Mathlib's `LiouvilleNumber` API.
-/

import Mathlib
import Proofs.Erdos1002OQ04

set_option maxHeartbeats 800000

open Real LiouvilleNumber
open Erdos1002OQ03 (innerSum)
open Erdos1002OQ04 (innerSum_perturb)

namespace Erdos1002OQ04

/-! ## Reducing a fraction to lowest terms -/

/-- Any nonnegative fraction `p/q` (`q > 0`) equals a reduced fraction `p'/q'` with
`gcd(p',q') = 1`, `q' ≥ 1`, and `q' ≤ q`.  Used to turn the (possibly non-reduced)
Liouville partial-sum numerator into a fraction `innerSum_perturb` accepts. -/
private theorem exists_reduced (p q : ℕ) (hq : 0 < q) :
    ∃ p' q' : ℕ, 0 < q' ∧ q' ≤ q ∧ Nat.gcd p' q' = 1 ∧
      ((p' : ℝ) / (q' : ℝ) = (p : ℝ) / (q : ℝ)) := by
  set g : ℕ := Nat.gcd p q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right p hq
  have hgne : (g : ℝ) ≠ 0 := by positivity
  set p' : ℕ := p / g with hp'
  set q' : ℕ := q / g with hq'
  have hgp : g * p' = p := Nat.mul_div_cancel' (Nat.gcd_dvd_left p q)
  have hgq : g * q' = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right p q)
  have hq'pos : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · rw [h, Nat.mul_zero] at hgq; omega
    · exact h
  have hq'le : q' ≤ q := by rw [hq']; exact Nat.div_le_self q g
  have hcop : Nat.gcd p' q' = 1 := Nat.coprime_div_gcd_div_gcd hgpos
  refine ⟨p', q', hq'pos, hq'le, hcop, ?_⟩
  have hpR : (p : ℝ) = (g : ℝ) * (p' : ℝ) := by exact_mod_cast hgp.symm
  have hqR : (q : ℝ) = (g : ℝ) * (q' : ℝ) := by exact_mod_cast hgq.symm
  rw [hpR, hqR, mul_div_mul_left _ _ hgne]

/-! ## The fixed Liouville witness -/

/-- **Capstone (Liouville side, single witness).**  Liouville's constant
`α = Σ_{i≥0} 10^{-i!}` is irrational and its inner sum is *unbounded*: for every
height `M` there is an `n` with `S(α, n) > M`.

This sharpens `innerSum_unbounded_near_rational` (where the witness `α` depended on
`M`) to a *single fixed* number, exhibiting the genuine Liouville phenomenon —
the polar opposite of the `O(log n)` boundedness for badly-approximable `α`. -/
theorem innerSum_liouvilleNumber_unbounded :
    ∃ α : ℝ, Irrational α ∧ ∀ M : ℝ, ∃ n : ℕ, M < innerSum α n := by
  have h10 : ((10 : ℕ) : ℝ) = (10 : ℝ) := by norm_num
  refine ⟨liouvilleNumber (10 : ℝ), ?_, ?_⟩
  · -- Irrationality: Liouville numbers are irrational.
    have hirr := (liouville_liouvilleNumber (m := 10) (by norm_num)).irrational
    rwa [h10] at hirr
  intro M
  -- Step 1 (height): choose `N ≥ 1` with `N/2 − 1 > M`.
  obtain ⟨N, hN1, hNM⟩ : ∃ N : ℕ, 1 ≤ N ∧ M < (N : ℝ) / 2 - 1 := by
    obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * M + 2)
    refine ⟨max 1 N0, le_max_left _ _, ?_⟩
    have : (N0 : ℝ) ≤ ((max 1 N0 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  -- Step 2 (approximation depth): choose `k = K + 3` with `10^{k!} > N²`.
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((N : ℝ) ^ 2) (by norm_num : (1 : ℝ) < 10)
  set k : ℕ := K + 3 with hkdef
  have hk3 : 3 ≤ k := by omega
  -- The partial sum is a fraction `p / 10^{k!}`.
  obtain ⟨p, hp⟩ := partialSum_eq_rat (m := 10) (by norm_num) k
  rw [h10] at hp
  set qN : ℕ := 10 ^ k.factorial with hqN
  have hqNpos : 0 < qN := by rw [hqN]; positivity
  have hcast : (qN : ℝ) = (10 : ℝ) ^ k.factorial := by rw [hqN]; push_cast; ring
  -- Reduce `p / qN` to lowest terms `p' / q'`.
  obtain ⟨p', q', hq'pos, hq'le, hcop, hval⟩ := exists_reduced p qN hqNpos
  have hq'1 : 1 ≤ q' := hq'pos
  set Qr : ℝ := (qN : ℝ) with hQr
  have hQrpow : Qr = (10 : ℝ) ^ k.factorial := hcast
  have hQr1 : (1 : ℝ) ≤ Qr := by rw [hQrpow]; exact one_le_pow₀ (by norm_num)
  have hQrpos : (0 : ℝ) < Qr := by linarith
  -- `partialSum 10 k = p'/q'` and the remainder.
  have hps : partialSum (10 : ℝ) k = (p' : ℝ) / (q' : ℝ) := by rw [hp]; exact hval.symm
  have hsum : partialSum (10 : ℝ) k + remainder (10 : ℝ) k = liouvilleNumber (10 : ℝ) :=
    partialSum_add_remainder (m := (10 : ℝ)) (by norm_num) k
  have hrempos : 0 < remainder (10 : ℝ) k := remainder_pos (m := (10 : ℝ)) (by norm_num) k
  -- One-sided approximation `p'/q' < α`.
  have hlo : (p' : ℝ) / (q' : ℝ) < liouvilleNumber (10 : ℝ) := by
    rw [← hps]; linarith [hsum, hrempos]
  -- The difference equals the remainder.
  have hdiff : liouvilleNumber (10 : ℝ) - (p' : ℝ) / (q' : ℝ) = remainder (10 : ℝ) k := by
    rw [← hps]; linarith [hsum]
  -- Remainder decay: `remainder 10 k < 1 / Qr^k`.
  have hrem_lt : remainder (10 : ℝ) k < 1 / Qr ^ k := by
    have hrl : remainder (10 : ℝ) k < 1 / ((10 : ℝ) ^ k.factorial) ^ k :=
      remainder_lt k (m := (10 : ℝ)) (by norm_num)
    rwa [← hQrpow] at hrl
  -- Numeric estimate: `(α − p'/q') · (N·q')² < 1`.
  have hhi : (liouvilleNumber (10 : ℝ) - (p' : ℝ) / (q' : ℝ)) * (((N * q' : ℕ) : ℝ)) ^ 2 < 1 := by
    rw [hdiff]
    set R : ℝ := remainder (10 : ℝ) k with hR
    have hRpos : 0 ≤ R := le_of_lt hrempos
    have hQk : (0 : ℝ) < Qr ^ k := by positivity
    -- `(N·q' : ℝ) ≤ N·Qr`.
    have hNq'le : ((N * q' : ℕ) : ℝ) ≤ (N : ℝ) * Qr := by
      have he : ((N * q' : ℕ) : ℝ) = (N : ℝ) * (q' : ℝ) := by push_cast; ring
      rw [he]
      have hq'R : (q' : ℝ) ≤ Qr := by rw [hQr]; exact_mod_cast hq'le
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hq'R hN0
    have hNq'pos : (0 : ℝ) ≤ ((N * q' : ℕ) : ℝ) := by positivity
    have hsq : (((N * q' : ℕ) : ℝ)) ^ 2 ≤ ((N : ℝ) * Qr) ^ 2 :=
      pow_le_pow_left₀ hNq'pos hNq'le 2
    -- `N² < Qr` from the choice of `k = K + 3`.
    have hNQ : (N : ℝ) ^ 2 < Qr := by
      have hKle : K ≤ k.factorial := le_trans (by omega) (Nat.self_le_factorial k)
      have hmono : (10 : ℝ) ^ K ≤ (10 : ℝ) ^ k.factorial := pow_le_pow_right₀ (by norm_num) hKle
      calc (N : ℝ) ^ 2 < (10 : ℝ) ^ K := hK
        _ ≤ (10 : ℝ) ^ k.factorial := hmono
        _ = Qr := hQrpow.symm
    -- `(N·Qr)² < Qr³ ≤ Qr^k`.
    have hQr2pos : (0 : ℝ) < Qr ^ 2 := by positivity
    have hcube : ((N : ℝ) * Qr) ^ 2 < Qr ^ 3 := by
      have hexp : ((N : ℝ) * Qr) ^ 2 = (N : ℝ) ^ 2 * Qr ^ 2 := by ring
      rw [hexp]
      calc (N : ℝ) ^ 2 * Qr ^ 2 < Qr * Qr ^ 2 := mul_lt_mul_of_pos_right hNQ hQr2pos
        _ = Qr ^ 3 := by ring
    have hcubek : Qr ^ 3 ≤ Qr ^ k := pow_le_pow_right₀ hQr1 hk3
    have hbig : ((N : ℝ) * Qr) ^ 2 < Qr ^ k := lt_of_lt_of_le hcube hcubek
    -- Assemble the chain.
    have hNQrsq_pos : (0 : ℝ) < ((N : ℝ) * Qr) ^ 2 := by positivity
    have step1 : R * (((N * q' : ℕ) : ℝ)) ^ 2 ≤ R * ((N : ℝ) * Qr) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hRpos
    have step2 : R * ((N : ℝ) * Qr) ^ 2 < (1 / Qr ^ k) * ((N : ℝ) * Qr) ^ 2 :=
      mul_lt_mul_of_pos_right hrem_lt hNQrsq_pos
    have step3 : (1 / Qr ^ k) * ((N : ℝ) * Qr) ^ 2 < 1 := by
      have heq : (1 / Qr ^ k) * ((N : ℝ) * Qr) ^ 2 = ((N : ℝ) * Qr) ^ 2 / Qr ^ k := by ring
      rw [heq, div_lt_one hQk]
      exact hbig
    linarith [step1, step2, step3]
  -- Step 3: apply the perturbation lemma at the reduced fraction.
  obtain ⟨hlow, _⟩ := innerSum_perturb p' q' N hq'1 hcop hN1 _ hlo hhi
  exact ⟨N * q', by linarith [hNM, hlow]⟩

end Erdos1002OQ04
