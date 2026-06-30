/-
  Maclaurin's Step Inequality, Derived from Newton's Log-Concavity
  ================================================================

  Problem: amgm-inequality-oq-03-oq-02-oq-02
  ("Mathlib contribution: fill existing AM-GM TODO with formal Maclaurin steps")

  Context.  The gallery file `Proofs/AmgmInequalityOQ02.lean` (Maclaurin
  Inequalities) carries TWO independent `axiom` declarations:

    * `newton_log_concavity` : (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1))·(eₖ₊₁/C(n,k+1))
    * `maclaurin_step`        : Mₖ ≥ Mₖ₊₁   (the Maclaurin chain step)

  These are NOT logically independent: the classical theory derives the
  Maclaurin step *from* Newton's log-concavity.  Mathlib (checked 2026-06)
  has neither Newton's inequalities nor Maclaurin's, so the deep result
  `newton_log_concavity` (which needs the real-rootedness / Rolle machinery)
  must stay axiomatized for now.  But `maclaurin_step` should be a THEOREM.

  This file does exactly that for strictly positive inputs: it proves the
  Maclaurin step inequality `Mₖ₊₁ ≤ Mₖ` taking `newton_log_concavity` as the
  ONLY assumption.  `#print axioms maclaurin_step_pos` lists `newton_log_concavity`
  and the standard foundational axioms — but NOT a separate Maclaurin axiom.

  Key idea (avoids logarithms and infinite products).  Write
  pₖ = eₖ/C(n,k) for the normalized symmetric mean, so Mₖ = pₖ^(1/k).
  Newton says pₖ² ≥ pₖ₋₁·pₖ₊₁.  Define the statement

        S(k) :   p_{k+1}^k  ≤  p_k^{k+1}.

  Then S is provable by a short induction using ONLY natural-number powers:
    * S(0):  p₁⁰ = 1 ≤ 1 = p₀¹      (since p₀ = e₀/C(n,0) = 1).
    * S(k-1) ⟹ S(k):  from Newton p_k² ≥ p_{k-1}·p_{k+1} and p_{k-1} > 0,
        p_{k+1}^k ≤ (p_k²/p_{k-1})^k, and S(k-1): p_k^{k-1} ≤ p_{k-1}^k
        is precisely what is needed to bound this by p_k^{k+1}.
  Concretely the step is the multiplicative chain
        (p_{k-1}·p_{k+1})^{k} ≤ (p_k²)^{k} = p_k^{2k} = p_k^{k-1}·p_k^{k+1}
                              ≤ p_{k-1}^{k}·p_k^{k+1},
  and cancelling p_{k-1}^{k} > 0 gives p_{k+1}^{k} ≤ p_k^{k+1}.

  Finally Mₖ₊₁ ≤ Mₖ follows by taking k(k+1)-th roots (`rpow_cross`).

  References:
    - Maclaurin, C. (1729). A Second Letter to Martin Folkes, Esq.
    - Newton, I. (1707). Arithmetica Universalis.
    - Hardy, Littlewood, Pólya. Inequalities (1934), §2.22.
-/

import Mathlib

open Finset Real

namespace MaclaurinStepFromNewton

/-! ## Elementary symmetric polynomials (mirrors `AmgmInequalityOQ02.lean`) -/

/-- The k-th elementary symmetric polynomial of x₁, …, xₙ. -/
noncomputable def elemSymm {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, x i

/-- e₀ = 1. -/
theorem elemSymm_zero {n : ℕ} (x : Fin n → ℝ) : elemSymm 0 x = 1 := by
  simp [elemSymm, powersetCard_zero]

/-- For strictly positive inputs and `k ≤ n`, the k-th symmetric polynomial is
    strictly positive (the index set of size-k subsets is nonempty). -/
theorem elemSymm_pos {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) : 0 < elemSymm k x := by
  unfold elemSymm
  apply Finset.sum_pos
  · intro s _
    exact Finset.prod_pos (fun i _ => hx i)
  · rw [← Finset.card_pos, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin]
    exact Nat.choose_pos hk

/-- The normalized symmetric mean pₖ = eₖ / C(n,k). -/
noncomputable def normElemSymm {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  elemSymm k x / (n.choose k : ℝ)

/-- p₀ = 1. -/
theorem normElemSymm_zero {n : ℕ} (x : Fin n → ℝ) : normElemSymm 0 x = 1 := by
  simp [normElemSymm, elemSymm_zero, Nat.choose_zero_right]

/-- pₖ > 0 for strictly positive inputs and `k ≤ n`. -/
theorem normElemSymm_pos {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) : 0 < normElemSymm k x := by
  apply div_pos (elemSymm_pos k hk x hx)
  exact_mod_cast Nat.choose_pos hk

/-! ## The retained axiom: Newton's log-concavity (same statement as the gallery) -/

/-- Newton's inequality: the normalized elementary symmetric polynomials are
    log-concave.  This is the genuinely deep input (real-rootedness / Rolle),
    absent from Mathlib, and is the SOLE assumption used below. -/
axiom newton_log_concavity {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (elemSymm k x / (Nat.choose n k : ℝ)) ^ 2 ≥
    (elemSymm (k - 1) x / (Nat.choose n (k - 1) : ℝ)) *
    (elemSymm (k + 1) x / (Nat.choose n (k + 1) : ℝ))

/-! ## The Maclaurin means -/

/-- The Maclaurin means Mₖ = (eₖ/C(n,k))^(1/k) = pₖ^(1/k). -/
noncomputable def maclaurinMean {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  (elemSymm k x / (Nat.choose n k : ℝ)) ^ ((1 : ℝ) / k)

/-! ## Core induction (natural-number powers only) -/

/-- The multiplicative Maclaurin core: `p_{k+1}^k ≤ p_k^{k+1}`, proved from
    Newton's log-concavity by induction on `k`, using ONLY `ℕ`-powers. -/
theorem maclaurin_core {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ k : ℕ, k + 1 ≤ n →
      normElemSymm (k + 1) x ^ k ≤ normElemSymm k x ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [normElemSymm_zero]
  | succ m ih =>
    intro hk
    have hm : m + 1 ≤ n := by omega
    have IH := ih hm
    -- positivity of the three relevant normalized means
    have hA : 0 < normElemSymm m x := normElemSymm_pos m (by omega) x hx
    have hB : 0 < normElemSymm (m + 1) x := normElemSymm_pos (m + 1) (by omega) x hx
    have hC : 0 < normElemSymm (m + 2) x := normElemSymm_pos (m + 2) (by omega) x hx
    -- Newton at j = m+1 :  p_m · p_{m+2} ≤ p_{m+1}²
    have hNewton : normElemSymm m x * normElemSymm (m + 2) x
        ≤ normElemSymm (m + 1) x ^ 2 := by
      have h := newton_log_concavity (m + 1) (by omega) (by omega) x
        (fun i => (hx i).le)
      simp only [Nat.add_sub_cancel] at h
      exact h
    -- raise Newton to the m+1 power
    have hAC : (normElemSymm m x * normElemSymm (m + 2) x) ^ (m + 1)
        ≤ (normElemSymm (m + 1) x ^ 2) ^ (m + 1) :=
      pow_le_pow_left₀ (mul_nonneg hA.le hC.le) hNewton (m + 1)
    rw [mul_pow, ← pow_mul] at hAC
    -- split the exponent 2*(m+1) = m + (m+2)
    have hsplit : normElemSymm (m + 1) x ^ (2 * (m + 1))
        = normElemSymm (m + 1) x ^ m * normElemSymm (m + 1) x ^ (m + 2) := by
      rw [← pow_add]; congr 1; omega
    -- use the induction hypothesis  p_{m+1}^m ≤ p_m^{m+1}
    have hIH2 : normElemSymm (m + 1) x ^ m * normElemSymm (m + 1) x ^ (m + 2)
        ≤ normElemSymm m x ^ (m + 1) * normElemSymm (m + 1) x ^ (m + 2) :=
      mul_le_mul_of_nonneg_right IH (pow_nonneg hB.le _)
    -- assemble:  p_m^{m+1} · p_{m+2}^{m+1} ≤ p_m^{m+1} · p_{m+1}^{m+2}
    have hcomb : normElemSymm m x ^ (m + 1) * normElemSymm (m + 2) x ^ (m + 1)
        ≤ normElemSymm m x ^ (m + 1) * normElemSymm (m + 1) x ^ (m + 2) := by
      calc normElemSymm m x ^ (m + 1) * normElemSymm (m + 2) x ^ (m + 1)
            ≤ normElemSymm (m + 1) x ^ (2 * (m + 1)) := hAC
        _ = normElemSymm (m + 1) x ^ m * normElemSymm (m + 1) x ^ (m + 2) := hsplit
        _ ≤ normElemSymm m x ^ (m + 1) * normElemSymm (m + 1) x ^ (m + 2) := hIH2
    -- cancel p_m^{m+1} > 0
    exact le_of_mul_le_mul_left hcomb (pow_pos hA _)

/-! ## Root extraction: from ℕ-powers back to the means -/

/-- If `b^s ≤ a^t` for positive reals and positive naturals, then taking the
    appropriate roots gives `b^(1/t) ≤ a^(1/s)`.  (The roots are crossed:
    the exponent of `b` uses `t`, the exponent of `a` uses `s`.) -/
theorem rpow_cross {a b : ℝ} {s t : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (ht : 0 < t) (h : b ^ s ≤ a ^ t) :
    b ^ ((1 : ℝ) / t) ≤ a ^ ((1 : ℝ) / s) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  -- raise both sides to the power 1/(s·t)
  have key : (b ^ s) ^ ((1 : ℝ) / (s * t)) ≤ (a ^ t) ^ ((1 : ℝ) / (s * t)) :=
    Real.rpow_le_rpow (pow_nonneg hb.le s) h (by positivity)
  have lhs : (b ^ s) ^ ((1 : ℝ) / (s * t)) = b ^ ((1 : ℝ) / t) := by
    rw [← Real.rpow_natCast b s, ← Real.rpow_mul hb.le]
    congr 1
    field_simp
  have rhs : (a ^ t) ^ ((1 : ℝ) / (s * t)) = a ^ ((1 : ℝ) / s) := by
    rw [← Real.rpow_natCast a t, ← Real.rpow_mul ha.le]
    congr 1
    field_simp
    ring
  rwa [lhs, rhs] at key

/-! ## Main result: the Maclaurin step, derived from Newton -/

/-- **Maclaurin's step inequality** for strictly positive inputs, proved from
    `newton_log_concavity` alone:  Mₖ₊₁ ≤ Mₖ. -/
theorem maclaurin_step_pos {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    maclaurinMean (k + 1) x ≤ maclaurinMean k x := by
  have hcore := maclaurin_core x hx k hkn
  have hp : 0 < normElemSymm k x := normElemSymm_pos k (by omega) x hx
  have hq : 0 < normElemSymm (k + 1) x := normElemSymm_pos (k + 1) (by omega) x hx
  have hmk : maclaurinMean k x = normElemSymm k x ^ ((1 : ℝ) / k) := rfl
  have hmk1 : maclaurinMean (k + 1) x
      = normElemSymm (k + 1) x ^ ((1 : ℝ) / (k + 1)) := rfl
  rw [hmk, hmk1]
  exact rpow_cross hp hq hk (by omega) hcore

end MaclaurinStepFromNewton
