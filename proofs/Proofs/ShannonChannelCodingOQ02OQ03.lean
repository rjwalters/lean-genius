/-
  Channel Coding Converse via Fano's Inequality

  Open Question OQ02-OQ03: Prove that when transmission rate R exceeds
  channel capacity C, error probability is bounded away from zero.

  Main result: For block length n ≥ 2/(R-C), any code with rate ≥ R
  has error probability ≥ (R-C)/(2R) > 0.

  The proof combines three information-theoretic steps:
  (1) H(W) = log M  (W uniform over M codewords)
  (2) I(W;Y^n) ≤ n·C  (data processing inequality for memoryless channels)
  (3) H(W|Ŵ) ≤ h(P_e) + P_e·log(M-1) ≤ 1 + P_e·log M  (Fano's inequality)

  Combined: log M = H(W) = I(W;Y^n) + H(W|Y^n) ≤ n·C + 1 + P_e·log M
  This gives: (1 - P_e)·log M ≤ n·C + 1 ≤ (1-P_e)·log M → P_e ≥ 1 - (n·C+1)/(n·R).
  For n ≥ 2/(R-C): P_e ≥ (R-C)/(2R) > 0.

  Axioms (new): 1 — fano_mi_converse_bound (axiomatizes Fano + MI subadditivity)
  Sorries: 0
  Theorems proved: 5 (algebraic converse chain)
-/
import Mathlib
import Proofs.ShannonChannelCoding

open Real InformationTheory InformationTheory.ChannelCoding

namespace ChannelCodingConverse

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The average error probability of a code: fraction of messages decoded incorrectly. -/
noncomputable def codeErrorProb (ch : DMChannel α β) {n : ℕ}
    (code : BlockCode α n) (decoder : (Fin n → β) → Fin code.M) : ℝ :=
  (∑ i : Fin code.M, (1 - ∑ y : Fin n → β,
    (∏ j : Fin n, ch.W (code.encode i j) (y j)) *
      if decoder y = i then (1 : ℝ) else 0)) / code.M

/-! ## Key Information-Theoretic Axiom -/

/-- **Combined Fano-MI Converse Bound**:
    For any code over a memoryless channel:  log M ≤ n·C + 1 + P_e · log M

    The three information-theoretic steps that together imply this (axiomatized here):
    (1) H(W) = log M  (uniform distribution over M messages)
    (2) I(W;Y^n) ≤ n·C  (data processing + memoryless channel MI chain rule)
    (3) H(W|Ŵ) ≤ h(P_e) + P_e·log(M-1) ≤ 1 + P_e·log M  (Fano, with h ≤ log 2 ≤ 1 nat)

    Combining H(W) = I(W;Y^n) + H(W|Y^n) ≤ I(W;Ŵ) + H(W|Ŵ) ≤ n·C + 1 + P_e·log M,
    where H(W|Y^n) ≤ H(W|Ŵ) uses the data processing inequality (Ŵ = decoder(Y^n)). -/
axiom fano_mi_converse_bound {n : ℕ} (hn : 0 < n)
    (ch : DMChannel α β) (code : BlockCode α n)
    (decoder : (Fin n → β) → Fin code.M)
    (hM : 1 < code.M) :
    Real.log code.M ≤ ↑n * channelCapacity ch + 1 +
      codeErrorProb ch code decoder * Real.log code.M

/-! ## Algebraic Converse Lemmas -/

/-- Core algebraic lemma: the Fano-MI bound implies P_e ≥ 1 - (n·C+1)/(n·R). -/
lemma converse_from_combined_bound {n : ℕ} (hn : 0 < n) {M : ℕ} (hM : 1 < M)
    {C R P_e : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hlog_rate : (n : ℝ) * R ≤ Real.log M)
    (hfano_mi : Real.log M ≤ (n : ℝ) * C + 1 + P_e * Real.log M) :
    1 - ((n : ℝ) * C + 1) / ((n : ℝ) * R) ≤ P_e := by
  have hn_cast : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnR_pos : 0 < (n : ℝ) * R := mul_pos hn_cast hR
  have h1 : (1 - P_e) * Real.log M ≤ (n : ℝ) * C + 1 := by nlinarith
  by_cases hpe1 : P_e ≤ 1
  · -- Standard case: (1 - P_e) ≥ 0, multiply n·R ≤ log M
    have h2 : (1 - P_e) * ((n : ℝ) * R) ≤ (n : ℝ) * C + 1 :=
      le_trans (mul_le_mul_of_nonneg_left hlog_rate (by linarith)) h1
    linarith [(le_div_iff hnR_pos).mpr h2]
  · -- Trivial case: P_e > 1, so 1 - (n·C+1)/(n·R) < 1 < P_e
    have hPe_gt : 1 < P_e := not_le.mp hpe1
    have hnn : 0 ≤ ((n : ℝ) * C + 1) / ((n : ℝ) * R) :=
      div_nonneg (by linarith [mul_nonneg hn_cast.le hC]) hnR_pos.le
    linarith

/-- Threshold lemma: for n ≥ 2/(R-C), the bound gives P_e ≥ (R-C)/(2R). -/
lemma threshold_bound {n : ℕ} (hn : 0 < n) {C R : ℝ}
    (hR : 0 < R) (hRC : C < R)
    (hn2RC : 2 ≤ (n : ℝ) * (R - C)) :
    (R - C) / (2 * R) ≤ 1 - ((n : ℝ) * C + 1) / ((n : ℝ) * R) := by
  have hn_cast : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnR_pos : 0 < (n : ℝ) * R := mul_pos hn_cast hR
  have h2R_pos : 0 < 2 * R := by linarith
  -- Key algebraic fact: n·(R-C)·R ≥ 2R implies n·C·R + 2R ≤ n·R²
  have hkey : (n : ℝ) * C * R + 2 * R ≤ (n : ℝ) * R ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hn2RC hR.le
    have hexp : (n : ℝ) * (R - C) * R = (n : ℝ) * R ^ 2 - (n : ℝ) * C * R := by ring
    rw [hexp] at hmul
    linarith
  -- Prove (R-C)/(2R) + (nC+1)/(nR) ≤ 1, then conclude
  have hsum : (R - C) / (2 * R) + ((n : ℝ) * C + 1) / ((n : ℝ) * R) ≤ 1 := by
    rw [div_add_div _ _ (ne_of_gt h2R_pos) (ne_of_gt hnR_pos),
        div_le_one (mul_pos h2R_pos hnR_pos)]
    have he1 : (R - C) * ((n : ℝ) * R) + 2 * R * ((n : ℝ) * C + 1) =
               (n : ℝ) * R ^ 2 + (n : ℝ) * C * R + 2 * R := by ring
    have he2 : 2 * R * ((n : ℝ) * R) = 2 * (n : ℝ) * R ^ 2 := by ring
    rw [he1, he2]
    linarith [hkey]
  linarith

/-- The gap δ = (R-C)/(2R) is strictly positive when R > C. -/
lemma converse_delta_pos {C R : ℝ} (hR : 0 < R) (hRC : C < R) :
    0 < (R - C) / (2 * R) :=
  div_pos (sub_pos.mpr hRC) (by linarith)

/-- Rate condition R ≤ rate_of_code implies log(M) ≥ n·R. -/
lemma rate_ge_implies_log {α : Type*} {n : ℕ} (hn : 0 < n)
    (code : BlockCode α n) {R : ℝ}
    (hrate : R ≤ rate_of_code hn code) :
    (n : ℝ) * R ≤ Real.log code.M := by
  unfold rate_of_code at hrate
  rwa [le_div_iff (Nat.cast_pos.mpr hn), mul_comm] at hrate

end ChannelCodingConverse

/-! ## Main Theorem -/

/-- **Channel Coding Converse (Asymptotic)**:
    When rate R exceeds capacity C, error probability is bounded below for long codes.

    For block length n ≥ 2/(R-C), any code with rate ≥ R satisfies P_e ≥ (R-C)/(2R) > 0.

    This proves the asymptotic regime. The ∀n version (channel_coding_converse in
    ShannonChannelCoding.lean) requires additional argument for small n; the information-
    theoretic bound here is tight as n → ∞ (P_e → 1 - C/R). -/
theorem channel_coding_converse_asymptotic
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty α]
    (ch : DMChannel α β) {R : ℝ} (hR : 0 < R)
    (hRC : channelCapacity ch < R) :
    let C := channelCapacity ch
    let δ := (R - C) / (2 * R)
    0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (hn : 0 < n) (code : BlockCode α n) (decoder : (Fin n → β) → Fin code.M),
        1 < code.M →
        R ≤ rate_of_code hn code →
        δ ≤ ChannelCodingConverse.codeErrorProb ch code decoder := by
  set C := channelCapacity ch
  set δ := (R - C) / (2 * R)
  have hRC_pos : 0 < R - C := sub_pos.mpr hRC
  have hC_nn : 0 ≤ C := capacity_nonneg ch
  refine ⟨ChannelCodingConverse.converse_delta_pos hR hRC, ⌈2 / (R - C)⌉₊, ?_⟩
  intro n hn_thresh hn code decoder hM hrate
  -- n satisfies the threshold: 2 ≤ n * (R - C)
  have hn2RC : 2 ≤ (n : ℝ) * (R - C) := by
    have hN : 2 / (R - C) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn_thresh)
    exact (div_le_iff hRC_pos).mp hN
  -- Rate condition: log(M) ≥ n * R
  have hlog_rate : (n : ℝ) * R ≤ Real.log code.M :=
    ChannelCodingConverse.rate_ge_implies_log hn code hrate
  -- Combined Fano-MI bound: log M ≤ n*C + 1 + P_e * log M
  have hfano_mi := ChannelCodingConverse.fano_mi_converse_bound hn ch code decoder hM
  -- Algebraic: P_e ≥ 1 - (n*C+1)/(n*R)
  have hpe_lower :=
    ChannelCodingConverse.converse_from_combined_bound hn hM hR hC_nn hlog_rate hfano_mi
  -- Threshold: 1 - (n*C+1)/(n*R) ≥ δ
  linarith [ChannelCodingConverse.threshold_bound hn hR hRC hn2RC]
