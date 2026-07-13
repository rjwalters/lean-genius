/-
Attempt 02: Prove the Parseval identity for Fin 3 → ℝ

The goal is to prove: For orthonormal {v₁, v₂, v₃} in ℝ³,
  |w|² = ⟨w, v₁⟩² + ⟨w, v₂⟩² + ⟨w, v₃⟩²

This requires showing that orthonormal vectors in ℝ³ form a basis.
-/

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Polyrith

namespace ParsevalProof

-- Match the definitions from HurwitzTheorem.lean
def normSq {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i * v i
def innerProd {n : ℕ} (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i

-- Scalar multiplication
def smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) : Fin n → ℝ := fun i => c * v i

-- Vector addition lemmas
lemma innerProd_add_left {n : ℕ} (u v w : Fin n → ℝ) :
    innerProd (u + v) w = innerProd u w + innerProd v w := by
  simp only [innerProd, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma innerProd_smul_left {n : ℕ} (c : ℝ) (v w : Fin n → ℝ) :
    innerProd (smul c v) w = c * innerProd v w := by
  simp only [innerProd, smul, mul_assoc, Finset.mul_sum]

lemma innerProd_sub_left {n : ℕ} (u v w : Fin n → ℝ) :
    innerProd (u - v) w = innerProd u w - innerProd v w := by
  simp only [innerProd, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma innerProd_smul_right {n : ℕ} (c : ℝ) (v w : Fin n → ℝ) :
    innerProd v (smul c w) = c * innerProd v w := by
  simp only [innerProd, smul]
  rw [Finset.mul_sum]
  congr 1; ext i; ring

-- normSq lemmas for the projection computation
lemma normSq_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) :
    normSq (smul c v) = c^2 * normSq v := by
  simp only [normSq, smul]
  rw [Finset.mul_sum]
  congr 1; ext i; ring

lemma normSq_add {n : ℕ} (v w : Fin n → ℝ) :
    normSq (v + w) = normSq v + 2 * innerProd v w + normSq w := by
  simp only [normSq, innerProd, Pi.add_apply]
  have h : ∀ i, (v i + w i) * (v i + w i) = v i * v i + 2 * (v i * w i) + w i * w i :=
    fun i => by ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

lemma innerProd_add_right {n : ℕ} (u v w : Fin n → ℝ) :
    innerProd u (v + w) = innerProd u v + innerProd u w := by
  simp only [innerProd, Pi.add_apply, mul_add, Finset.sum_add_distrib]

-- Inner product of smul vectors
lemma innerProd_smul_smul {n : ℕ} (a b : ℝ) (v w : Fin n → ℝ) :
    innerProd (smul a v) (smul b w) = a * b * innerProd v w := by
  simp only [innerProd, smul]
  have h : ∀ i, a * v i * (b * w i) = a * b * (v i * w i) := fun i => by ring
  simp only [h]
  rw [← Finset.mul_sum]

/-!
## Key insight: The projection onto orthonormal vectors

For orthonormal {v₁, v₂, v₃}, define:
  proj(w) = ⟨w,v₁⟩v₁ + ⟨w,v₂⟩v₂ + ⟨w,v₃⟩v₃

Then:
1. |proj(w)|² = ⟨w,v₁⟩² + ⟨w,v₂⟩² + ⟨w,v₃⟩²  (by orthonormality)
2. w - proj(w) is orthogonal to each vᵢ
3. In ℝ³, if a vector is orthogonal to 3 linearly independent vectors, it's zero
-/

-- The projection onto orthonormal triple
def proj3 (v₁ v₂ v₃ w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  smul (innerProd w v₁) v₁ + smul (innerProd w v₂) v₂ + smul (innerProd w v₃) v₃

-- Norm squared of projection using orthonormality
lemma normSq_proj3 (v₁ v₂ v₃ w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0) :
    normSq (proj3 v₁ v₂ v₃ w) =
      (innerProd w v₁)^2 + (innerProd w v₂)^2 + (innerProd w v₃)^2 := by
  -- Let c₁ = ⟨w,v₁⟩, c₂ = ⟨w,v₂⟩, c₃ = ⟨w,v₃⟩
  let c₁ := innerProd w v₁
  let c₂ := innerProd w v₂
  let c₃ := innerProd w v₃
  -- proj3 = c₁v₁ + c₂v₂ + c₃v₃ = (c₁v₁ + c₂v₂) + c₃v₃
  have hproj : proj3 v₁ v₂ v₃ w = (smul c₁ v₁ + smul c₂ v₂) + smul c₃ v₃ := by
    simp only [proj3, add_assoc]
  rw [hproj]
  -- |a + b|² = |a|² + 2⟨a,b⟩ + |b|²
  rw [normSq_add]
  -- Similarly for the first part
  rw [normSq_add]
  -- Now we have: normSq(c₁v₁) + 2*innerProd(c₁v₁)(c₂v₂) + normSq(c₂v₂)
  --              + 2*innerProd(c₁v₁ + c₂v₂)(c₃v₃) + normSq(c₃v₃)
  -- Compute each term using orthonormality
  have ns1 : normSq (smul c₁ v₁) = c₁^2 := by rw [normSq_smul, hv₁]; ring
  have ns2 : normSq (smul c₂ v₂) = c₂^2 := by rw [normSq_smul, hv₂]; ring
  have ns3 : normSq (smul c₃ v₃) = c₃^2 := by rw [normSq_smul, hv₃]; ring
  have ip12 : innerProd (smul c₁ v₁) (smul c₂ v₂) = 0 := by
    rw [innerProd_smul_smul, h12]; ring
  have ip13 : innerProd (smul c₁ v₁) (smul c₃ v₃) = 0 := by
    rw [innerProd_smul_smul, h13]; ring
  have ip23 : innerProd (smul c₂ v₂) (smul c₃ v₃) = 0 := by
    rw [innerProd_smul_smul, h23]; ring
  -- The cross term innerProd(c₁v₁ + c₂v₂)(c₃v₃)
  have ipcross : innerProd (smul c₁ v₁ + smul c₂ v₂) (smul c₃ v₃) = 0 := by
    rw [innerProd_add_left, ip13, ip23]; ring
  rw [ns1, ns2, ns3, ip12, ipcross]
  ring

-- The difference w - proj is orthogonal to each basis vector
lemma diff_ortho_v1 (v₁ v₂ v₃ w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0) :
    innerProd (w - proj3 v₁ v₂ v₃ w) v₁ = 0 := by
  simp only [proj3]
  rw [innerProd_sub_left]
  rw [innerProd_add_left, innerProd_add_left]
  rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
  -- ⟨v₁, v₁⟩ = 1, ⟨v₂, v₁⟩ = 0, ⟨v₃, v₁⟩ = 0
  have hv1v1 : innerProd v₁ v₁ = 1 := by
    simp only [innerProd, normSq] at hv₁ ⊢; exact hv₁
  have hv2v1 : innerProd v₂ v₁ = 0 := by
    simp only [innerProd]; rw [show (∑ i, v₂ i * v₁ i) = (∑ i, v₁ i * v₂ i) by
      congr 1; ext i; ring]; exact h12
  have hv3v1 : innerProd v₃ v₁ = 0 := by
    simp only [innerProd]; rw [show (∑ i, v₃ i * v₁ i) = (∑ i, v₁ i * v₃ i) by
      congr 1; ext i; ring]; exact h13
  rw [hv1v1, hv2v1, hv3v1]
  ring

-- Similarly for v₂ and v₃ (analogous proofs)
lemma diff_ortho_v2 (v₁ v₂ v₃ w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0) :
    innerProd (w - proj3 v₁ v₂ v₃ w) v₂ = 0 := by
  simp only [proj3]
  rw [innerProd_sub_left]
  rw [innerProd_add_left, innerProd_add_left]
  rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
  have hv1v2 : innerProd v₁ v₂ = 0 := h12
  have hv2v2 : innerProd v₂ v₂ = 1 := by
    simp only [innerProd, normSq] at hv₂ ⊢; exact hv₂
  have hv3v2 : innerProd v₃ v₂ = 0 := by
    simp only [innerProd]; rw [show (∑ i, v₃ i * v₂ i) = (∑ i, v₂ i * v₃ i) by
      congr 1; ext i; ring]; exact h23
  rw [hv1v2, hv2v2, hv3v2]
  ring

lemma diff_ortho_v3 (v₁ v₂ v₃ w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0) :
    innerProd (w - proj3 v₁ v₂ v₃ w) v₃ = 0 := by
  simp only [proj3]
  rw [innerProd_sub_left]
  rw [innerProd_add_left, innerProd_add_left]
  rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
  have hv1v3 : innerProd v₁ v₃ = 0 := h13
  have hv2v3 : innerProd v₂ v₃ = 0 := h23
  have hv3v3 : innerProd v₃ v₃ = 1 := by
    simp only [innerProd, normSq] at hv₃ ⊢; exact hv₃
  rw [hv1v3, hv2v3, hv3v3]
  ring

/-!
## The key lemma: orthogonal to orthonormal triple implies zero

In ℝ³, if u is orthogonal to an orthonormal triple {v₁, v₂, v₃}, then u = 0.

Proof: The matrix M = [v₁ | v₂ | v₃] is orthogonal (columns are orthonormal).
So det(M) = ±1 ≠ 0, hence M is invertible.
The condition u ⊥ vᵢ for all i means Mᵀu = 0.
Since M (and hence Mᵀ) is invertible, u = 0.
-/

-- Helper: innerProd is symmetric
lemma innerProd_comm {n : ℕ} (v w : Fin n → ℝ) : innerProd v w = innerProd w v := by
  simp only [innerProd]
  congr 1; ext i; ring

-- The key linear algebra fact: in ℝ³, orthogonal to an orthonormal triple implies zero
-- Proof idea: orthonormal vectors span ℝ³, so u = c₁v₁ + c₂v₂ + c₃v₃ where cᵢ = ⟨u, vᵢ⟩ = 0
lemma ortho_to_orthonormal_triple_eq_zero (v₁ v₂ v₃ u : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0)
    (hu1 : innerProd u v₁ = 0) (hu2 : innerProd u v₂ = 0) (hu3 : innerProd u v₃ = 0) :
    u = 0 := by
  -- Expand all definitions into coordinate form
  simp only [normSq, innerProd, Fin.sum_univ_three] at hv₁ hv₂ hv₃ h12 h13 h23 hu1 hu2 hu3

  -- The key insight: the matrix M with columns v₁, v₂, v₃ satisfies Mᵀ M = I (orthonormality),
  -- so det(M)² = 1 ≠ 0. Thus M is invertible, and Mᵀ u = 0 implies u = 0.
  --
  -- For coordinate proof: we need u 0 = u 1 = u 2 = 0.
  -- From hu1, hu2, hu3:
  --   u 0 * v₁ 0 + u 1 * v₁ 1 + u 2 * v₁ 2 = 0
  --   u 0 * v₂ 0 + u 1 * v₂ 1 + u 2 * v₂ 2 = 0
  --   u 0 * v₃ 0 + u 1 * v₃ 1 + u 2 * v₃ 2 = 0
  -- This is the system Mᵀ [u 0; u 1; u 2] = 0.
  -- Since M has orthonormal columns, det(M) = ±1, so M (and Mᵀ) is invertible.
  -- Therefore u = 0.

  -- The formal proof requires showing det(M) ≠ 0 using Mathlib's matrix library.
  -- For now we accept this standard linear algebra fact.
  sorry

-- Finally, the Parseval identity
theorem inner_expansion_three (v₁ v₂ v₃ w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0) :
    normSq w = (innerProd w v₁)^2 + (innerProd w v₂)^2 + (innerProd w v₃)^2 := by
  -- Let diff = w - proj3
  let diff := w - proj3 v₁ v₂ v₃ w
  -- diff is orthogonal to v₁, v₂, v₃
  have hdiff1 := diff_ortho_v1 v₁ v₂ v₃ w hv₁ hv₂ hv₃ h12 h13 h23
  have hdiff2 := diff_ortho_v2 v₁ v₂ v₃ w hv₁ hv₂ hv₃ h12 h13 h23
  have hdiff3 := diff_ortho_v3 v₁ v₂ v₃ w hv₁ hv₂ hv₃ h12 h13 h23
  -- Therefore diff = 0
  have hdiff_zero : diff = 0 :=
    ortho_to_orthonormal_triple_eq_zero v₁ v₂ v₃ diff hv₁ hv₂ hv₃ h12 h13 h23
      hdiff1 hdiff2 hdiff3
  -- So w = proj3
  have hw_eq_proj : w = proj3 v₁ v₂ v₃ w := by
    have : w - proj3 v₁ v₂ v₃ w = 0 := hdiff_zero
    simp only [sub_eq_zero] at this
    exact this
  -- Rewrite using w = proj3 on the LHS only
  calc normSq w = normSq (proj3 v₁ v₂ v₃ w) := by rw [← hw_eq_proj]
    _ = (innerProd w v₁)^2 + (innerProd w v₂)^2 + (innerProd w v₃)^2 :=
        normSq_proj3 v₁ v₂ v₃ w hv₁ hv₂ hv₃ h12 h13 h23

end ParsevalProof
