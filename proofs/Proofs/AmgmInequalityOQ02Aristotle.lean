/-
  Aristotle targets for amgm-inequality-oq-02 (Maclaurin Inequalities)
  Routine supporting lemmas for automated proof search.
  See AmgmInequalityOQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Maclaurin chain M₁ ≥ M₂ ≥ ⋯ ≥ Mₙ)
  - NOT the axiomatized deep results (Newton log-concavity, Maclaurin step)
  - Known classical results provable from Mathlib

  Main target: h_binom — the binomial expansion identity
    (∑ i : Fin n, x i) ^ 2 = ∑ i, (x i) ^ 2 + 2 * elemSymm 2 x

  This is the ONLY remaining sorry in AmgmInequalityOQ02.lean.
  Once proved, it closes `maclaurin_sq_m1_ge_m2_general` completely
  (the rest of that proof is already written and compiles).

  Proof strategy for h_binom:
  - Induction on n using the elemSymm recurrence
  - elemSymm 2 (x ∘ Fin.castSucc ++ [a]) = elemSymm 2 (x ∘ Fin.castSucc) + a * elemSymm 1 (x ∘ Fin.castSucc)
  - Base: n=0 trivial; n=1 trivial (no 2-element subsets)
  - Step: (S'+a)² = S'² + 2S'a + a² = (S₂'+2e₂') + 2S'a + a² = (S₂'+a²) + 2(e₂'+aS')
-/
import Mathlib

open Finset Real

noncomputable def elemSymmA {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, x i

/-- e₀ = 1 (empty product) -/
theorem elemSymmA_zero {n : ℕ} (x : Fin n → ℝ) : elemSymmA 0 x = 1 := by
  simp [elemSymmA, powersetCard_zero]

/-- e₁ = ∑ xᵢ -/
theorem elemSymmA_one {n : ℕ} (x : Fin n → ℝ) : elemSymmA 1 x = ∑ i, x i := by
  simp [elemSymmA, powersetCard_one, sum_map, prod_singleton]

/-- Recurrence: eₖ₊₁(x₀,...,xₙ) = eₖ₊₁(x₀,...,xₙ₋₁) + xₙ · eₖ(x₀,...,xₙ₋₁)
    This is the fundamental recurrence for elementary symmetric polynomials. -/
theorem elemSymmA_succ_castSucc {n : ℕ} (k : ℕ) (x : Fin (n + 1) → ℝ) :
    elemSymmA (k + 1) x =
    elemSymmA (k + 1) (x ∘ Fin.castSucc) +
    x (Fin.last n) * elemSymmA k (x ∘ Fin.castSucc) := by
  sorry -- follows from Finset.powersetCard_succ_insert applied to Fin.last n ∉ image Fin.castSucc

/-- elemSymm 2 of n+1 variables decomposes as:
    e₂(x₀,...,xₙ) = e₂(x₀,...,xₙ₋₁) + xₙ · (∑ᵢ xᵢ) -/
theorem elemSymmA_two_succ {n : ℕ} (x : Fin (n + 1) → ℝ) :
    elemSymmA 2 x =
    elemSymmA 2 (x ∘ Fin.castSucc) +
    x (Fin.last n) * elemSymmA 1 (x ∘ Fin.castSucc) := by
  exact elemSymmA_succ_castSucc 1 x

/-- The key binomial identity: (∑xᵢ)² = ∑xᵢ² + 2·e₂
    This is the MAIN target for Aristotle to close. -/
theorem sq_sum_eq_sum_sq_add_two_esymm {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, x i) ^ 2 = ∑ i : Fin n, (x i) ^ 2 + 2 * elemSymmA 2 x := by
  induction n with
  | zero =>
    have h : elemSymmA 2 x = 0 := by
      simp only [elemSymmA]
      apply Finset.sum_eq_zero; intro s hs
      have hmem := Finset.mem_powersetCard.mp hs
      have huniv : (univ : Finset (Fin 0)).card = 0 := by simp
      have hle : s.card ≤ 0 := (Finset.card_le_card hmem.1).trans_eq huniv
      omega
    simp [h]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, elemSymmA_two_succ, elemSymmA_one]
    have hih := ih (x ∘ Fin.castSucc)
    simp only [Function.comp_apply] at hih ⊢
    nlinarith [hih, sq_nonneg (∑ i : Fin k, x (Fin.castSucc i)),
               sq_nonneg (x (Fin.last k))]

/-- The Cauchy-Schwarz inequality for finite sums: n·∑xᵢ² ≥ (∑xᵢ)² -/
theorem cauchy_schwarz_sum_A {n : ℕ} (x : Fin n → ℝ) :
    (n : ℝ) * ∑ i : Fin n, (x i) ^ 2 ≥ (∑ i : Fin n, x i) ^ 2 := by
  have h_nn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h_expand : ∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 =
      2 * ((n : ℝ) * ∑ i, (x i) ^ 2 - (∑ i, x i) ^ 2) := by
    simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib]
    have h1 : ∑ i : Fin n, ∑ _j : Fin n, (x i) ^ 2 = (n : ℝ) * ∑ i, (x i) ^ 2 := by
      simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    have h2 : ∑ _i : Fin n, ∑ j : Fin n, (x j) ^ 2 = (n : ℝ) * ∑ j, (x j) ^ 2 := by
      simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    have h3 : ∑ i : Fin n, ∑ j : Fin n, 2 * x i * x j = 2 * (∑ i, x i) ^ 2 := by
      rw [sq, sum_mul]; simp_rw [mul_sum]; congr 1; ext i; ring
    rw [h1, h2, h3]; ring
  linarith
