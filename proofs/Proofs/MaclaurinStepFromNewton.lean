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

  This file does exactly that, for the FULL non-negative case: it proves the
  Maclaurin step inequality `Mₖ₊₁ ≤ Mₖ` for all inputs `xᵢ ≥ 0` (`maclaurin_step`,
  matching the exact statement of the gallery's `maclaurin_step` axiom) taking
  `newton_log_concavity` as the ONLY assumption.  `#print axioms maclaurin_step`
  lists `newton_log_concavity` and the standard foundational axioms — but NOT a
  separate Maclaurin axiom.

  The strictly-positive case `maclaurin_step_pos` is the clean core; the general
  non-negative `maclaurin_step` adds a short case split on `e_{k+1}`:
    * `e_{k+1} = 0`  ⟹  `Mₖ₊₁ = 0 ≤ Mₖ`;
    * `e_{k+1} > 0`  ⟹  the elementary symmetric polynomials `e_j` are positive for
      all `j ≤ k+1` ("zeros form a suffix", `elemSymm_pos_of_top_pos`), so the same
      core induction applies.

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

/-- For non-negative inputs, every elementary symmetric polynomial is non-negative
    (a sum of products of non-negative terms). -/
theorem elemSymm_nonneg {n : ℕ} (k : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ elemSymm k x :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun i _ => hx i))

/-- **Zeros form a suffix (single step).** For non-negative inputs, if the
    `(j+1)`-st elementary symmetric polynomial is positive, then so is the `j`-th.

    A positive `e_{j+1}` means some `(j+1)`-subset `S` has all-positive product, hence
    all its entries are positive; any `j`-subset `T ⊆ S` then has positive product and
    is one of the (non-negative) summands of `e_j`, forcing `e_j > 0`. -/
theorem elemSymm_pred_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    {j : ℕ} (hjn : j + 1 ≤ n) (h : 0 < elemSymm (j + 1) x) : 0 < elemSymm j x := by
  rw [elemSymm] at h
  obtain ⟨S, hS, hSne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  have hSpos : 0 < ∏ i ∈ S, x i :=
    lt_of_le_of_ne (Finset.prod_nonneg (fun i _ => hx i)) (Ne.symm hSne)
  have hSx : ∀ i ∈ S, 0 < x i := by
    intro i hi
    rcases (hx i).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (Finset.prod_eq_zero hi h'.symm) hSpos.ne'
  have hScard : S.card = j + 1 := (Finset.mem_powersetCard.1 hS).2
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show j ≤ S.card by omega)
  have hTmem : T ∈ (univ : Finset (Fin n)).powersetCard j :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ T, hTcard⟩
  have hTpos : 0 < ∏ i ∈ T, x i := Finset.prod_pos (fun i hi => hSx i (hTS hi))
  calc 0 < ∏ i ∈ T, x i := hTpos
    _ ≤ elemSymm j x := by
        rw [elemSymm]
        exact Finset.single_le_sum (f := fun s => ∏ i ∈ s, x i)
          (fun s _ => Finset.prod_nonneg (fun i _ => hx i)) hTmem

/-- **Zeros form a suffix (prefix form).** For non-negative inputs, if `e_K > 0` then
    `e_j > 0` for every `j ≤ K`. Iterates `elemSymm_pred_pos` down from `K`. -/
theorem elemSymm_pos_of_top_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ K, K ≤ n → 0 < elemSymm K x → ∀ j, j ≤ K → 0 < elemSymm j x := by
  intro K
  induction K with
  | zero =>
    intro _ _ j hj
    rw [Nat.le_zero.1 hj, elemSymm_zero]; exact one_pos
  | succ m ih =>
    intro hK hpos j hj
    have hmpos : 0 < elemSymm m x := elemSymm_pred_pos x hx hK hpos
    rcases Nat.eq_or_lt_of_le hj with h | h
    · rw [h]; exact hpos
    · exact ih (by omega) hmpos j (by omega)

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

/-- The multiplicative Maclaurin core, **from positivity of the normalized means**:
    `p_{k+1}^k ≤ p_k^{k+1}`, proved from Newton's log-concavity by induction on `k`,
    using ONLY `ℕ`-powers. The positivity hypothesis is on the `pⱼ` (not on the inputs
    `xᵢ`), so this version applies to the non-negative case once the prefix lemma
    `elemSymm_pos_of_top_pos` supplies `0 < pⱼ` for `j ≤ k+1` from `e_{k+1} > 0`. -/
theorem maclaurin_core_of_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ k : ℕ, k + 1 ≤ n → (∀ j, j ≤ k + 1 → 0 < normElemSymm j x) →
      normElemSymm (k + 1) x ^ k ≤ normElemSymm k x ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _ _
    simp [normElemSymm_zero]
  | succ m ih =>
    intro hk hpos
    have hm : m + 1 ≤ n := by omega
    have IH := ih hm (fun j hj => hpos j (by omega))
    -- positivity of the three relevant normalized means (from the hypothesis)
    have hA : 0 < normElemSymm m x := hpos m (by omega)
    have hB : 0 < normElemSymm (m + 1) x := hpos (m + 1) (by omega)
    have hC : 0 < normElemSymm (m + 2) x := hpos (m + 2) (by omega)
    -- Newton at j = m+1 :  p_m · p_{m+2} ≤ p_{m+1}²
    have hNewton : normElemSymm m x * normElemSymm (m + 2) x
        ≤ normElemSymm (m + 1) x ^ 2 := by
      have h := newton_log_concavity (m + 1) (by omega) (by omega) x hx
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

/-- The multiplicative Maclaurin core for **strictly positive inputs**:
    `p_{k+1}^k ≤ p_k^{k+1}`. A specialization of `maclaurin_core_of_pos`, since
    strictly positive inputs make every `pⱼ` positive (`normElemSymm_pos`). -/
theorem maclaurin_core {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ k : ℕ, k + 1 ≤ n →
      normElemSymm (k + 1) x ^ k ≤ normElemSymm k x ^ (k + 1) := fun k hk =>
  maclaurin_core_of_pos x (fun i => (hx i).le) k hk
    (fun j hj => normElemSymm_pos j (le_trans hj hk) x hx)

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
  have hstep := rpow_cross hp hq hk (Nat.succ_pos k) hcore
  simpa only [maclaurinMean, normElemSymm] using hstep

/-- **Maclaurin's step inequality, full non-negative case** — `Mₖ₊₁ ≤ Mₖ` for all
    non-negative inputs, derived from `newton_log_concavity` alone. This is exactly the
    statement of the `maclaurin_step` axiom in `AmgmInequalityOQ02.lean`, so it
    discharges that axiom.

    Two cases on `e_{k+1}`:
    * `e_{k+1} = 0`: then `Mₖ₊₁ = 0^{1/(k+1)} = 0 ≤ Mₖ` (Maclaurin means are
      non-negative for non-negative inputs).
    * `e_{k+1} > 0`: the prefix lemma `elemSymm_pos_of_top_pos` gives `pⱼ > 0` for all
      `j ≤ k+1`, so `maclaurin_core_of_pos` applies and `rpow_cross` finishes — exactly
      as in `maclaurin_step_pos`, but with positivity sourced from `e_{k+1} > 0` rather
      than from strict positivity of the inputs. -/
theorem maclaurin_step {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean (k + 1) x ≤ maclaurinMean k x := by
  by_cases hek1 : 0 < elemSymm (k + 1) x
  · -- positive case: every pⱼ (j ≤ k+1) is positive by the prefix lemma
    have hpos : ∀ j, j ≤ k + 1 → 0 < normElemSymm j x := by
      intro j hj
      have hej : 0 < elemSymm j x :=
        elemSymm_pos_of_top_pos x hx (k + 1) hkn hek1 j hj
      exact div_pos hej (by exact_mod_cast Nat.choose_pos (le_trans hj hkn))
    have hcore := maclaurin_core_of_pos x hx k hkn hpos
    have hp : 0 < normElemSymm k x := hpos k (by omega)
    have hq : 0 < normElemSymm (k + 1) x := hpos (k + 1) (le_refl _)
    have hstep := rpow_cross hp hq hk (Nat.succ_pos k) hcore
    simpa only [maclaurinMean, normElemSymm] using hstep
  · -- e_{k+1} = 0  ⟹  Mₖ₊₁ = 0 ≤ Mₖ
    have hzero : elemSymm (k + 1) x = 0 :=
      le_antisymm (not_lt.1 hek1) (elemSymm_nonneg (k + 1) x hx)
    have hMk1 : maclaurinMean (k + 1) x = 0 := by
      rw [maclaurinMean, hzero, zero_div, Real.zero_rpow (by positivity)]
    rw [hMk1, maclaurinMean]
    exact Real.rpow_nonneg (div_nonneg (elemSymm_nonneg k x hx) (by positivity)) _

end MaclaurinStepFromNewton
