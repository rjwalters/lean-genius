/-
  Erdős Problem #897 — OQ-01 (Part I): Non-Vacuity, Selectivity, and a
  Strongly-Additive Reduction

  Companion to `Erdos897Problem.lean`. Part I of Erdős #897 asks: if `f` is
  additive with `limsup_{p,k} f(p^k)/log(p^k) = ∞`, must
  `limsup_n (f(n+1)-f(n))/log n = ∞`?  The forward implication is OPEN and is
  **not** asserted here. This file supplies the verified surrounding theory that
  any analysis of Part I needs:

  (1) **Non-vacuity.** The hypothesis `UnboundedOnPrimePowers` is satisfiable:
      `logSqWeight n = ∑_{p ∣ n} (log p)²` is additive — in fact strongly
      additive — and grows faster than `log` on prime powers. So Part I is not
      vacuously true.
  (2) **Selectivity.** The parent file's flagship additive functions `log` and
      `ω` both FAIL the hypothesis (`log` sits exactly at the boundary,
      `ω` is bounded on prime powers). The hypothesis therefore isolates functions
      growing strictly faster than `log` on prime powers.
  (3) The hypothesis forces plain unboundedness of `f` on prime powers.
  (4) **Strongly-additive reduction.** For strongly additive `f` the hypothesis
      collapses to `f(p)/log p` unbounded over primes — the counterpart of the
      parent file's completely-additive reduction. The cancellation differs: the
      value is constant in `k`, so the binding case is `k = 1`, and the `M < 0`
      branch is handled by invoking the hypothesis at `0`.

  Verified, 0 axioms, 0 sorries, no `native_decide`.
-/

import Proofs.Erdos897Problem

namespace Erdos897

open Finset

/-
## (1) Non-vacuity: an explicit witness satisfying the hypothesis

`logSqWeight n = ∑_{p ∈ primeFactors n} (log p)²`. On a prime power `p^k` (k ≥ 1)
its value is `(log p)²`, independent of `k`, while `log(p^k) = k·log p`. Choosing a
large prime makes `(log p)² / log(p^k) = log p / k` as large as we like at `k = 1`,
so the function is unbounded on prime powers relative to `log`.
-/

/-- The additive weight `logSqWeight n = ∑_{p ∣ n} (log p)²`, our witness that the
Erdős #897 hypothesis `UnboundedOnPrimePowers` is non-vacuous. -/
noncomputable def logSqWeight (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (Real.log p) ^ 2

/-- On a prime power the sum collapses to the single prime: `logSqWeight p = (log p)²`. -/
theorem logSqWeight_prime {p : ℕ} (hp : p.Prime) :
    logSqWeight p = (Real.log p) ^ 2 := by
  simp only [logSqWeight, hp.primeFactors, Finset.sum_singleton]

/-- `logSqWeight` is additive: prime supports of coprime numbers are disjoint, so the
defining sum splits over a coprime product. -/
theorem logSqWeight_additive : IsAdditive logSqWeight := by
  intro a b ha hb hab
  simp only [logSqWeight]
  rw [Nat.primeFactors_mul ha.ne' hb.ne',
      Finset.sum_union hab.disjoint_primeFactors]

/-- `logSqWeight` is in fact **strongly additive**: `logSqWeight (p^k) = logSqWeight p`
for every prime `p` and `k ≥ 1`, since `(p^k).primeFactors = p.primeFactors`. -/
theorem logSqWeight_stronglyAdditive : IsStronglyAdditive logSqWeight := by
  refine ⟨logSqWeight_additive, ?_⟩
  intro p k hp hk
  simp only [logSqWeight]
  rw [Nat.primeFactors_pow p (by omega : k ≠ 0)]

/-- `logSqWeight` satisfies the Erdős #897 hypothesis: it is unbounded on prime powers
relative to `log`. At `k = 1` we have `logSqWeight p = (log p)²` versus `log p`, and a
sufficiently large prime makes `(log p)² > M·log p` for any target `M`. -/
theorem logSqWeight_unboundedOnPrimePowers : UnboundedOnPrimePowers logSqWeight := by
  intro M
  -- Pick a prime `p` with `log p > M` by going past `exp M`.
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (⌈Real.exp M⌉₊ + 1)
  refine ⟨p, 1, hp, le_refl 1, ?_⟩
  have hlogpos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogM : M < Real.log p := by
    have hexp_lt : Real.exp M < (p : ℝ) := by
      have hceil : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
      have hNp : ((⌈Real.exp M⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpN
      push_cast at hNp
      linarith
    have := Real.log_lt_log (Real.exp_pos M) hexp_lt
    rwa [Real.log_exp] at this
  simp only [pow_one]
  rw [logSqWeight_prime hp]
  -- goal: `(log p)² > M * log p`; both factors of `(log p)(log p - M)` are positive.
  nlinarith [mul_pos hlogpos (sub_pos.mpr hlogM)]

/-- **Non-vacuity (headline).** There exists an additive function satisfying the
Erdős #897 hypothesis, so Part I is not vacuously true. Witness: `logSqWeight`. -/
theorem exists_additive_unboundedOnPrimePowers :
    ∃ f : ℕ → ℝ, IsAdditive f ∧ UnboundedOnPrimePowers f :=
  ⟨logSqWeight, logSqWeight_additive, logSqWeight_unboundedOnPrimePowers⟩

/-
## (2) Selectivity: the classical examples fail the hypothesis

`log` sits exactly at the boundary (`log(p^k)/log(p^k) = 1`) and `ω` is bounded on
prime powers (`ω(p^k) = 1`). Neither is unbounded relative to `log`, so the
hypothesis genuinely restricts to functions growing *strictly* faster than `log`.
-/

/-- **Selectivity for `log`.** The logarithm does not satisfy the hypothesis:
`logN(p^k) = log(p^k)` exactly, so it never exceeds `1 · log(p^k)`. -/
theorem not_unboundedOnPrimePowers_logN : ¬ UnboundedOnPrimePowers logN := by
  intro h
  obtain ⟨p, k, _hp, _hk, hlt⟩ := h 1
  simp only [logN, one_mul, Nat.cast_pow] at hlt
  exact lt_irrefl _ hlt

/-- **Selectivity for `ω`.** The distinct-prime-factor count is bounded (`ω(p^k) = 1`)
on prime powers, so it cannot outgrow `log`: with `M = 2/log 2` the required
inequality `ω(p^k) > M·log(p^k)` would force `1 > 2`. -/
theorem not_unboundedOnPrimePowers_omega : ¬ UnboundedOnPrimePowers omega := by
  intro h
  obtain ⟨p, k, hp, hk, hlt⟩ := h (2 / Real.log 2)
  have homega : omega (p ^ k) = 1 := by
    simp only [omega]
    rw [Nat.primeFactors_pow p (by omega : k ≠ 0), hp.primeFactors, Finset.card_singleton]
    norm_num
  rw [homega] at hlt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpk2 : (2 : ℝ) ≤ (p : ℝ) ^ k := by
    have hle : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    calc (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (p : ℝ) ^ k := by push_cast; ring
  have hloglb : Real.log 2 ≤ Real.log ((p : ℝ) ^ k) := Real.log_le_log (by norm_num) hpk2
  have hcnn : (0 : ℝ) ≤ 2 / Real.log 2 := by positivity
  have hmul : (2 / Real.log 2) * Real.log 2 ≤ (2 / Real.log 2) * Real.log ((p : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left hloglb hcnn
  have hval : (2 / Real.log 2) * Real.log 2 = 2 := by field_simp
  linarith

/-
## (3) The hypothesis forces plain unboundedness on prime powers
-/

/-- If `f` is unbounded on prime powers relative to `log`, then `f` is plainly
unbounded on prime powers: for every `B` some `f(p^k)` exceeds `B`. The uniform
lower bound `log(p^k) ≥ log 2 > 0` lets us dial the multiplier against `B`. -/
theorem unboundedOnPrimePowers_unbounded {f : ℕ → ℝ}
    (hf : UnboundedOnPrimePowers f) :
    ∀ B : ℝ, ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ f (p ^ k) > B := by
  intro B
  set M := (|B| + 1) / Real.log 2 with hMdef
  obtain ⟨p, k, hp, hk, hpk⟩ := hf M
  refine ⟨p, k, hp, hk, ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hpk2 : (2 : ℝ) ≤ (p : ℝ) ^ k := by
    have hle : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    calc (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (p : ℝ) ^ k := by push_cast; ring
  have hloglb : Real.log 2 ≤ Real.log ((p : ℝ) ^ k) := Real.log_le_log (by norm_num) hpk2
  have hchain : M * Real.log 2 ≤ M * Real.log ((p : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left hloglb hMnn
  have hval : M * Real.log 2 = |B| + 1 := by rw [hMdef]; field_simp
  have hBlt : B < |B| + 1 := by nlinarith [abs_nonneg B, le_abs_self B]
  calc B < |B| + 1 := hBlt
    _ = M * Real.log 2 := hval.symm
    _ ≤ M * Real.log ((p : ℝ) ^ k) := hchain
    _ < f (p ^ k) := hpk

/-
## (4) A strongly-additive reduction

For strongly additive `f`, `f(p^k) = f(p)` is constant in `k`, so the prime-power
hypothesis reduces to a statement about primes alone — the strongly-additive
counterpart of `completelyAdditive_unboundedOnPrimePowers_iff`.
-/

/-- **Reduction theorem (strongly additive).** For strongly additive `f`, the Erdős
#897 hypothesis is equivalent to `f(p)/log p` being unbounded over the primes.

Forward: since `f(p^k) = f(p)` the multiplier `k` appears only through
`log(p^k) = k·log p`; for `M ≥ 0` we drop the extra factor `k ≥ 1` (both `M` and
`log p` are nonnegative), and for `M < 0` we instead invoke the hypothesis at `0`
(then `f(p) > 0 ≥ M·log p`). Reverse: take `k = 1`. -/
theorem stronglyAdditive_unboundedOnPrimePowers_iff {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) :
    UnboundedOnPrimePowers f ↔
      ∀ M : ℝ, ∃ p : ℕ, p.Prime ∧ f p > M * Real.log p := by
  constructor
  · intro h M
    by_cases hM : 0 ≤ M
    · obtain ⟨p, k, hp, hk, hpk⟩ := h M
      refine ⟨p, hp, ?_⟩
      have hfp : f (p ^ k) = f p := hf.2 p k hp hk
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      rw [hfp, Real.log_pow] at hpk
      -- hpk : f p > M * (↑k * log p); drop the factor k ≥ 1.
      have hdrop : M * Real.log p ≤ M * ((k : ℝ) * Real.log p) := by
        nlinarith [mul_nonneg (mul_nonneg hM (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1)) hlogp]
      linarith
    · push_neg at hM
      obtain ⟨p, k, hp, hk, hpk⟩ := h 0
      refine ⟨p, hp, ?_⟩
      have hfp : f (p ^ k) = f p := hf.2 p k hp hk
      rw [hfp, zero_mul] at hpk
      have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hnp : M * Real.log p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hM.le hlogp.le
      linarith
  · intro h M
    obtain ⟨p, hp, hpp⟩ := h M
    refine ⟨p, 1, hp, le_refl 1, ?_⟩
    have hfp : f (p ^ 1) = f p := hf.2 p 1 hp (le_refl 1)
    rw [hfp, pow_one]
    exact hpp

end Erdos897
