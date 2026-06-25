/-
  Maclaurin's Inequality Chain from Newton's Log-Concavity
  (Newton Inductive Step OQ-01-OQ-02)

  Open question from NewtonInductiveStepOQ01 (openQuestions[1]):
    "Derive the full Maclaurin inequality chain ē₁ ≥ ē₂^{1/2} ≥ ... ≥ ēₙ^{1/n}."

  Setup. The normalized elementary symmetric means ēₖ = eₖ/C(n,k) of nonnegative
  reals are positive (for ≤ n nonzero entries), satisfy ē₀ = 1, and — this is
  Newton's inequality — are log-concave: ēₖ² ≥ ēₖ₋₁·ēₖ₊₁.  Maclaurin's theorem
  states that the sequence ēₖ^{1/k} is non-increasing.

  This file gives the complete, axiom-free **reduction** Newton ⟹ Maclaurin for
  an abstract positive log-concave sequence `a : ℕ → ℝ` with `a 0 = 1`:

  - `ratioSeq_antitone_of_logConcave`: log-concavity makes the consecutive ratios
    `a k / a (k-1)` non-increasing.
  - `prod_ratioSeq`: `a k` telescopes as `∏_{j=1}^k (a j / a (j-1))`.
  - `maclaurin_pow`: the Maclaurin chain in **polynomial form**,
        `a (k+1) ^ k ≤ a k ^ (k+1)`   (k ≥ 1),
    which is equivalent to `a (k+1)^{1/(k+1)} ≤ a k^{1/k}` but avoids real powers.
  - `maclaurin_root`: the genuine **radical form**
        `a (k+1) ^ (1/(k+1) : ℝ) ≤ a k ^ (1/k : ℝ)`   (k ≥ 1),
    via `Real.rpow`.

  Why a reduction. The parent's general Newton inequality `newton_inequality_means`
  (for k ≥ 2) still rests on an open inductive `sorry`. Rather than build on that,
  we keep Newton's inequalities as an explicit hypothesis and prove the chain
  follows — so the file is 0-axiom and 0-sorry. Instantiating `a := ēₖ` then yields
  the full Maclaurin chain the moment the parent's Newton inequality is completed.
  As a tightness witness, the geometric sequence `a k = t^k` (equal entries) meets
  all hypotheses with equality and the chain holds with equality.

  References:
  - Maclaurin (1729), A second letter ... concerning the roots of equations
  - Hardy–Littlewood–Pólya (1952), Inequalities, §2.22 (Theorem 52)
  - Niculescu (2000), A new look at Newton's inequalities
-/

import Mathlib

namespace NewtonMaclaurinChain

open Finset

/-- The consecutive-ratio sequence `r k = a k / a (k-1)` of a sequence `a`.
    For `k = 0` this is `a 0 / a 0`; the results below only use it for `k ≥ 1`. -/
noncomputable def ratioSeq (a : ℕ → ℝ) (k : ℕ) : ℝ := a k / a (k - 1)

/-- Each ratio is positive when the sequence is positive. -/
theorem ratioSeq_pos {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (m : ℕ) :
    0 < ratioSeq a m := by
  unfold ratioSeq; exact div_pos (hpos _) (hpos _)

-- ═══════════════════════════════════════════════════════════════════════
-- PART I: LOG-CONCAVITY ⇒ RATIOS NON-INCREASING
-- ═══════════════════════════════════════════════════════════════════════

/-- One step: log-concavity `a (k-1)·a (k+1) ≤ a k²` forces the ratio to drop,
    `a (k+1)/a k ≤ a k/a (k-1)`. -/
theorem ratioSeq_step_of_logConcave {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n)
    {k : ℕ} (hk : 1 ≤ k) (hlc : a (k - 1) * a (k + 1) ≤ a k ^ 2) :
    ratioSeq a (k + 1) ≤ ratioSeq a k := by
  unfold ratioSeq
  rw [show k + 1 - 1 = k by omega,
      div_le_div_iff₀ (hpos k) (hpos (k - 1))]
  nlinarith [hlc]

/-- The ratios are non-increasing from index 1 onward: `m ≤ n` (with `1 ≤ m`)
    gives `ratioSeq a n ≤ ratioSeq a m`. -/
theorem ratioSeq_antitone_of_logConcave {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n)
    (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2) :
    ∀ n m, 1 ≤ m → m ≤ n → ratioSeq a n ≤ ratioSeq a m := by
  intro n
  induction n with
  | zero => intro m hm hmn; omega
  | succ p ih =>
    intro m hm hmn
    rcases Nat.lt_or_ge m (p + 1) with hlt | hge
    · have hmp : m ≤ p := by omega
      have hp1 : 1 ≤ p := by omega
      exact (ratioSeq_step_of_logConcave hpos hp1 (hlc p hp1)).trans (ih m hm hmp)
    · have : m = p + 1 := by omega
      rw [this]

-- ═══════════════════════════════════════════════════════════════════════
-- PART II: TELESCOPING PRODUCT
-- ═══════════════════════════════════════════════════════════════════════

/-- `a k` telescopes as the product of consecutive ratios:
    `a k = ∏_{j=1}^{k} (a j / a (j-1))`, using `a 0 = 1`. -/
theorem prod_ratioSeq {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : a 0 = 1) :
    ∀ k, ∏ j ∈ Finset.Icc 1 k, ratioSeq a j = a k := by
  intro k
  induction k with
  | zero => simp [h0]
  | succ p ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ p + 1), ih]
    unfold ratioSeq
    rw [show p + 1 - 1 = p by omega,
        mul_div_cancel₀ _ (ne_of_gt (hpos p))]

-- ═══════════════════════════════════════════════════════════════════════
-- PART III: THE MACLAURIN CHAIN (POLYNOMIAL FORM)
-- ═══════════════════════════════════════════════════════════════════════

/-- Key estimate: `a k` dominates the `k`-th power of the *last* ratio,
    `ratioSeq a (k+1) ^ k ≤ a k`, because every earlier ratio is at least as big
    (ratios are non-increasing) and `a k` is their product. -/
theorem lastRatio_pow_le {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : a 0 = 1)
    (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    ratioSeq a (k + 1) ^ k ≤ a k := by
  rw [← prod_ratioSeq hpos h0 k]
  have hcard : (Finset.Icc 1 k).card = k := by rw [Nat.card_Icc]; omega
  calc ratioSeq a (k + 1) ^ k
      = ∏ _j ∈ Finset.Icc 1 k, ratioSeq a (k + 1) := by
        rw [Finset.prod_const, hcard]
    _ ≤ ∏ j ∈ Finset.Icc 1 k, ratioSeq a j := by
        apply Finset.prod_le_prod
        · intro j _; exact (ratioSeq_pos hpos (k + 1)).le
        · intro j hj
          rw [Finset.mem_Icc] at hj
          exact ratioSeq_antitone_of_logConcave hpos hlc (k + 1) j hj.1 (by omega)

/-- **Maclaurin's inequality chain, polynomial form.** For a positive log-concave
    sequence with `a 0 = 1` and `k ≥ 1`,
        `a (k+1) ^ k ≤ a k ^ (k+1)`.
    Equivalently `a (k+1)^{1/(k+1)} ≤ a k^{1/k}` (see `maclaurin_root`), i.e. the
    sequence `a k^{1/k}` is non-increasing — Maclaurin's theorem. -/
theorem maclaurin_pow {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : a 0 = 1)
    (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    a (k + 1) ^ k ≤ a k ^ (k + 1) := by
  have hkey : ratioSeq a (k + 1) ^ k ≤ a k := lastRatio_pow_le hpos h0 hlc hk
  have hrec : a (k + 1) = a k * ratioSeq a (k + 1) := by
    unfold ratioSeq
    rw [show k + 1 - 1 = k by omega,
        mul_div_cancel₀ _ (ne_of_gt (hpos k))]
  calc a (k + 1) ^ k
      = a k ^ k * ratioSeq a (k + 1) ^ k := by rw [hrec, mul_pow]
    _ ≤ a k ^ k * a k := by
        exact mul_le_mul_of_nonneg_left hkey (pow_nonneg (hpos k).le k)
    _ = a k ^ (k + 1) := (pow_succ (a k) k).symm

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: THE MACLAURIN CHAIN (RADICAL FORM)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Maclaurin's inequality chain, radical form.** For a positive log-concave
    sequence with `a 0 = 1` and `k ≥ 1`,
        `a (k+1) ^ (1/(k+1)) ≤ a k ^ (1/k)`   (real powers),
    i.e. `ē₁ ≥ ē₂^{1/2} ≥ ē₃^{1/3} ≥ ⋯` — the chain exactly as stated. -/
theorem maclaurin_root {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : a 0 = 1)
    (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    a (k + 1) ^ (1 / (k + 1 : ℝ)) ≤ a k ^ (1 / k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hx := hpos k
  have hy := hpos (k + 1)
  -- polynomial form (npow), recast with real exponents
  have hpoly : a (k + 1) ^ (k : ℝ) ≤ a k ^ ((k : ℝ) + 1) := by
    have h := maclaurin_pow hpos h0 hlc hk
    rw [Real.rpow_natCast,
        show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    exact h
  -- raise both sides to the positive power e = 1/(k(k+1))
  set e : ℝ := 1 / ((k : ℝ) * ((k : ℝ) + 1)) with he
  have hmono :
      (a (k + 1) ^ (k : ℝ)) ^ e ≤ (a k ^ ((k : ℝ) + 1)) ^ e :=
    Real.rpow_le_rpow (by positivity) hpoly (by rw [he]; positivity)
  -- collapse the iterated powers and simplify the exponents
  rw [← Real.rpow_mul hy.le, ← Real.rpow_mul hx.le] at hmono
  have eL : (k : ℝ) * e = 1 / ((k : ℝ) + 1) := by
    rw [he]; field_simp
  have eR : ((k : ℝ) + 1) * e = 1 / (k : ℝ) := by
    rw [he]; field_simp
  rw [eL, eR] at hmono
  exact hmono

end NewtonMaclaurinChain
