import Mathlib

/-! # Odd-column signed Gram obstruction
Odd column sums force a lower bound on the Gram energy of every sign vector.
The terminal consumes the Gram identity and joint eigenvector equations.
-/
open scoped BigOperators Matrix
namespace Erdos85
noncomputable section

private theorem odd_signed_column {C : Type*} [Fintype C]
    (b s : C → ℤ) (hs : ∀ x, s x = 1 ∨ s x = -1)
    (hb : Odd (∑ x, b x)) : Odd (∑ x, b x * s x) := by
  classical
  have heq : (∑ x, b x * s x) = (∑ x, b x) -
      2 * ∑ x, if s x = -1 then b x else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases hs x with h | h
    · simp [h]
    · simp [h]
      ring
  rcases hb with ⟨k, hk⟩
  refine ⟨k - ∑ x, if s x = -1 then b x else 0, ?_⟩
  rw [heq, hk]
  ring

/-- Odd column sums suffice; binary entries are not needed. -/
theorem oddColumn_signedGram_lower_bound
    {C F : Type*} [Fintype C] [Fintype F]
    (B : Matrix C F ℤ) (s : C → ℤ)
    (hs : ∀ x, s x = 1 ∨ s x = -1)
    (hodd : ∀ f, Odd (∑ x, B x f)) :
    (Fintype.card F : ℤ) ≤ s ⬝ᵥ ((B * Bᵀ) *ᵥ s) := by
  have hnorm : s ⬝ᵥ ((B * Bᵀ) *ᵥ s) =
      ∑ f, ((Bᵀ *ᵥ s) f) ^ 2 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hv : s ᵥ* B = Bᵀ *ᵥ s := by
      simpa using (Matrix.vecMul_transpose Bᵀ s)
    rw [hv]
    simp [dotProduct, pow_two]
  rw [hnorm]
  have hsum : (∑ _f : F, (1 : ℤ)) ≤ ∑ f, ((Bᵀ *ᵥ s) f) ^ 2 := by
    apply Finset.sum_le_sum
    intro f _
    have ho : Odd ((Bᵀ *ᵥ s) f) :=
      odd_signed_column (fun x => B x f) s hs (hodd f)
    have hn : (Bᵀ *ᵥ s) f ≠ 0 := by
      rcases ho with ⟨k, hk⟩
      omega
    have hz : (Bᵀ *ᵥ s) f ≤ -1 ∨ 1 ≤ (Bᵀ *ᵥ s) f := by omega
    rcases hz with hz | hz <;> nlinarith [sq_nonneg ((Bᵀ *ᵥ s) f + 1),
      sq_nonneg ((Bᵀ *ᵥ s) f - 1)]
  simpa using hsum

/-- A balanced joint sign eigenvector obstructs the actual incidence Gram. -/
theorem oddColumn_gram_jointSign_false
    {C F : Type*} [Fintype C] [Fintype F] [DecidableEq C]
    (B : Matrix C F ℤ) (H D : Matrix C C ℤ) (s : C → ℤ)
    (q h d : ℤ)
    (hs : ∀ x, s x = 1 ∨ s x = -1)
    (hbalance : ∑ x, s x = 0)
    (hodd : ∀ f, Odd (∑ x, B x f))
    (hH : H *ᵥ s = h • s) (hD : D *ᵥ s = d • s)
    (hGram : B * Bᵀ = (q - 1) • (1 : Matrix C C ℤ) +
      Matrix.of (fun _ _ => (1 : ℤ)) - D - H * H)
    (hsmall : (Fintype.card C : ℤ) * (q - 1 - d - h ^ 2) < Fintype.card F) :
    False := by
  have hJ : (Matrix.of (fun _ _ : C => (1 : ℤ))) *ᵥ s = 0 := by
    ext x
    simpa [Matrix.mulVec, dotProduct] using hbalance
  have haction : (B * Bᵀ) *ᵥ s = (q - 1 - d - h ^ 2) • s := by
    rw [hGram, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hJ, ← Matrix.mulVec_mulVec,
      hH, Matrix.mulVec_smul, hH, hD]
    ext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have henergy : s ⬝ᵥ ((B * Bᵀ) *ᵥ s) =
      (Fintype.card C : ℤ) * (q - 1 - d - h ^ 2) := by
    rw [haction]
    have hterm : ∀ x, s x * ((q - 1 - d - h ^ 2) • s) x =
        q - 1 - d - h ^ 2 := by
      intro x
      rcases hs x with hx | hx <;> simp [hx]
    simp only [dotProduct, hterm]
    simp
    ring
  have hbound := oddColumn_signedGram_lower_bound B s hs hodd
  rw [henergy] at hbound
  omega

/-- The q16 Clebsch numerical terminal. The geometric character equations
remain explicit hypotheses; no concrete carrier definition is hidden here. -/
theorem clebsch_signedGram_no_incidence
    (B : Matrix (Fin 48) (Fin 208) ℤ)
    (H D : Matrix (Fin 48) (Fin 48) ℤ) (s : Fin 48 → ℤ)
    (hs : ∀ x, s x = 1 ∨ s x = -1)
    (hbalance : ∑ x, s x = 0)
    (hcolumn : ∀ f, ∑ x, B x f = 3)
    (hH : H *ᵥ s = (-3 : ℤ) • s) (hD : D *ᵥ s = (3 : ℤ) • s)
    (hGram : B * Bᵀ = (15 : ℤ) • (1 : Matrix (Fin 48) (Fin 48) ℤ) +
      Matrix.of (fun _ _ => (1 : ℤ)) - D - H * H) : False := by
  apply oddColumn_gram_jointSign_false B H D s 16 (-3) 3 hs hbalance
  · intro f
    rw [hcolumn f]
    decide
  · exact hH
  · exact hD
  · exact hGram
  · norm_num

#print axioms oddColumn_signedGram_lower_bound
#print axioms oddColumn_gram_jointSign_false
#print axioms clebsch_signedGram_no_incidence
end
end Erdos85
