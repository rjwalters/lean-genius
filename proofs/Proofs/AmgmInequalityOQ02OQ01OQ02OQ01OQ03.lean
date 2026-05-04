/-
  Newton-Girard Recurrence: Independent Inductive Proof

  Open Question (amgm-inequality-oq-02-oq-01-oq-02-oq-01-oq-03):
  Prove the general Newton-Girard recurrence by induction on the number of
  variables, without using Mathlib's MvPolynomial.psum_eq_mul_esymm_sub_sum.

  Newton-Girard identity (Newton's form):
    k · eₖ(x) = ∑_{j=0}^{k-1} (-1)^j · eₖ₋₁₋ⱼ(x) · pⱼ₊₁(x)

  where eₖ = k-th elementary symmetric polynomial, pₖ = k-th power sum.

  Proof: Induction on n. Base n=0: both sides 0. Inductive step uses:
    eₖ(x',Y) = eₖ(x') + Y · eₖ₋₁(x')       (elemSymm_succ from OQ02)
    pⱼ(x',Y) = pⱼ(x') + Yʲ                   (powerSum_succ below)
  plus the sign-cancellation identity:
    ∑_{j≤k} (-1)^j · e(k-j) · Y^j + ∑_{j<k} (-1)^j · e(k-1-j) · Y^(j+1) = e(k)
  which follows termwise from (-1)^k + (-1)^{k-1} = 0.

  Status: PROVED — 0 sorries, 0 axioms
  Tags: algebra, symmetric-functions, newton-girard, power-sums, induction
-/

import Mathlib
import Proofs.AmgmInequalityOQ02

namespace AmgmInequalityOQ02OQ01OQ02OQ01OQ03

open Finset Real BigOperators

-- ============================================================
-- Part I: Power Sum
-- ============================================================

/-- k-th power sum: pₖ(x) = ∑ᵢ xᵢᵏ -/
noncomputable def powerSum (k : ℕ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i ^ k

/-- Adding one variable: pₖ(x',Y) = pₖ(x') + Yᵏ -/
theorem powerSum_succ (k : ℕ) {n : ℕ} (x : Fin (n + 1) → ℝ) :
    powerSum k x = powerSum k (x ∘ Fin.castSucc) + x (Fin.last n) ^ k := by
  simp [powerSum, Fin.sum_univ_castSucc]

-- ============================================================
-- Part II: Sign-Cancellation Lemma
-- ============================================================

/-- The algebraic identity underlying Newton-Girard:
    ∑_{j≤k} (-1)^j · e(k-j) · Y^j + ∑_{j<k} (-1)^j · e(k-1-j) · Y^(j+1) = e(k)

    Proof by induction on k: the boundary terms at j=k of each sum cancel via
    (-1)^k + (-1)^(k-1) = 0, and the bracket = e(k) by IH with e'(j) = e(j+1). -/
private lemma cancel_sum (k : ℕ) (e : ℕ → ℝ) (Y : ℝ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * e (k - j) * Y ^ j +
    ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * e (k - 1 - j) * Y ^ (j + 1) = e k := by
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ (f := fun j => (-1 : ℝ) ^ j * e (k + 1 - j) * Y ^ j),
        Finset.sum_range_succ (f := fun j => (-1 : ℝ) ^ j * e (k - j) * Y ^ (j + 1))]
    simp only [Nat.sub_self, Nat.add_sub_cancel]
    have h_sign : (-1 : ℝ) ^ (k + 1) + (-1 : ℝ) ^ k = 0 := by rw [pow_succ]; ring
    have h_cancel : (-1 : ℝ) ^ (k + 1) * e 0 * Y ^ (k + 1) +
                    (-1 : ℝ) ^ k * e 0 * Y ^ (k + 1) = 0 :=
      by linear_combination e 0 * Y ^ (k + 1) * h_sign
    have h_bracket : ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * e (k + 1 - j) * Y ^ j +
                     ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * e (k - j) * Y ^ (j + 1) = e (k + 1) := by
      have := ih (fun j => e (j + 1)) Y
      have hconv1 : ∀ j ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ j * e (k + 1 - j) * Y ^ j =
          (-1 : ℝ) ^ j * (fun m => e (m + 1)) (k - j) * Y ^ j := by
        intro j hj; rw [Finset.mem_range] at hj; congr 2; omega
      have hconv2 : ∀ j ∈ Finset.range k,
          (-1 : ℝ) ^ j * e (k - j) * Y ^ (j + 1) =
          (-1 : ℝ) ^ j * (fun m => e (m + 1)) (k - 1 - j) * Y ^ (j + 1) := by
        intro j hj; rw [Finset.mem_range] at hj; congr 2; omega
      rw [Finset.sum_congr rfl hconv1, Finset.sum_congr rfl hconv2, this]
    linarith

-- ============================================================
-- Part III: Newton-Girard Theorem
-- ============================================================

/-- **Newton-Girard Recurrence** (inductive proof, no MvPolynomial):
    k · eₖ(x) = ∑_{j=0}^{k-1} (-1)^j · eₖ₋₁₋ⱼ(x) · pⱼ₊₁(x)

    Proof by induction on n: base n=0 is trivial; the inductive step expands
    via the variable-adding recurrences (elemSymm_succ, powerSum_succ), applies
    IH at degrees k and k-1, and uses cancel_sum for the cross terms. -/
theorem newton_girard (n k : ℕ) (x : Fin n → ℝ) :
    (k : ℝ) * elemSymm k x =
    ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * elemSymm (k - 1 - j) x * powerSum (j + 1) x := by
  induction n generalizing k x with
  | zero =>
    simp only [powerSum, Finset.univ_eq_empty, Finset.sum_empty]
    cases k with
    | zero => simp [elemSymm, powersetCard_zero]
    | succ k =>
      rw [elemSymm_fin_zero (k + 1) (Nat.succ_pos k) x]
      simp [powerSum]
  | succ n ih =>
    cases k with
    | zero => simp [elemSymm, powerSum]
    | succ k =>
      -- IH for x' = x ∘ Fin.castSucc
      have ihkp1 : (↑(k + 1) : ℝ) * elemSymm (k + 1) (x ∘ Fin.castSucc) =
          ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * elemSymm (k - j) (x ∘ Fin.castSucc) *
            powerSum (j + 1) (x ∘ Fin.castSucc) := by
        have h := ih (k + 1) (x ∘ Fin.castSucc)
        simp only [Nat.add_sub_cancel] at h; exact h
      have ihk : (↑k : ℝ) * elemSymm k (x ∘ Fin.castSucc) =
          ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * elemSymm (k - 1 - j) (x ∘ Fin.castSucc) *
            powerSum (j + 1) (x ∘ Fin.castSucc) := ih k (x ∘ Fin.castSucc)
      -- LHS: apply elemSymm_succ
      rw [elemSymm_succ k x]
      simp only [Nat.add_sub_cancel]
      -- RHS: split last term j=k
      rw [Finset.sum_range_succ]
      rw [show k + 1 - 1 - k = 0 from by omega, elemSymm_zero x, mul_one, powerSum_succ]
      -- Expand inner sum (j < k) using splitting lemmas
      have h_inner :
          ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * elemSymm (k - j) x * powerSum (j + 1) x =
          (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * elemSymm (k - j) (x ∘ Fin.castSucc) *
              powerSum (j + 1) (x ∘ Fin.castSucc)) +
          x (Fin.last n) * (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j *
              elemSymm (k - 1 - j) (x ∘ Fin.castSucc) * powerSum (j + 1) (x ∘ Fin.castSucc)) +
          (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * elemSymm (k - j) (x ∘ Fin.castSucc) *
              x (Fin.last n) ^ (j + 1)) +
          x (Fin.last n) * (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j *
              elemSymm (k - 1 - j) (x ∘ Fin.castSucc) * x (Fin.last n) ^ (j + 1)) := by
        simp_rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [show elemSymm (k - j) x = elemSymm (k - j - 1 + 1) x from by congr 1; omega]
        rw [elemSymm_succ (k - j - 1) x, powerSum_succ (j + 1) x]
        have h_eq : k - j - 1 = k - 1 - j := by omega
        rw [h_eq]; ring
      rw [h_inner]
      -- Name four sums and apply key identities
      set A := ∑ j ∈ Finset.range k, (-1:ℝ)^j * elemSymm (k-j) (x ∘ Fin.castSucc) *
               powerSum (j+1) (x ∘ Fin.castSucc) with hA_def
      set B' := ∑ j ∈ Finset.range k, (-1:ℝ)^j * elemSymm (k-1-j) (x ∘ Fin.castSucc) *
                powerSum (j+1) (x ∘ Fin.castSucc) with hB'_def
      set C := ∑ j ∈ Finset.range k, (-1:ℝ)^j * elemSymm (k-j) (x ∘ Fin.castSucc) *
               x (Fin.last n) ^ (j+1) with hC_def
      set D' := ∑ j ∈ Finset.range k, (-1:ℝ)^j * elemSymm (k-1-j) (x ∘ Fin.castSucc) *
                x (Fin.last n) ^ (j+1) with hD'_def
      -- (1) A + (-1)^k * powerSum (k+1) x' = (k+1) * elemSymm (k+1) x'
      have hA : A + (-1:ℝ)^k * powerSum (k+1) (x ∘ Fin.castSucc) =
                (↑(k+1):ℝ) * elemSymm (k+1) (x ∘ Fin.castSucc) := by
        have : A + (-1:ℝ)^k * elemSymm 0 (x ∘ Fin.castSucc) *
               powerSum (k+1) (x ∘ Fin.castSucc) =
               ∑ j ∈ Finset.range (k+1), (-1:ℝ)^j * elemSymm (k-j) (x ∘ Fin.castSucc) *
                 powerSum (j+1) (x ∘ Fin.castSucc) := by
          simp only [A, Finset.sum_range_succ, Nat.sub_self]
        rw [elemSymm_zero, mul_one] at this
        linarith [ihkp1]
      -- (2) Y * B' = Y * k * elemSymm k x'
      have hB : x (Fin.last n) * B' =
                x (Fin.last n) * ((↑k:ℝ) * elemSymm k (x ∘ Fin.castSucc)) := by
        rw [← ihk]
      -- (3) C + Y*D' + (-1)^k * Y^(k+1) = Y * elemSymm k x'
      have hCD : C + x (Fin.last n) * D' + (-1:ℝ)^k * x (Fin.last n)^(k+1) =
                 x (Fin.last n) * elemSymm k (x ∘ Fin.castSucc) := by
        set Y := x (Fin.last n)
        set x' := x ∘ Fin.castSucc
        set F1 := ∑ j ∈ Finset.range (k+1), (-1:ℝ)^j * elemSymm (k-j) x' * Y^j
        set F2 := ∑ j ∈ Finset.range k, (-1:ℝ)^j * elemSymm (k-1-j) x' * Y^(j+1)
        have hF1 : C + (-1:ℝ)^k * Y^(k+1) = Y * F1 := by
          simp only [F1, C, Finset.mul_sum, Finset.sum_range_succ, Nat.sub_self,
                     elemSymm_zero, mul_one]
          congr 1; apply Finset.sum_congr rfl; intro j _; ring
        have hF2 : Y * D' = Y * F2 := by simp [D', F2]
        have hcs : F1 + F2 = elemSymm k x' := cancel_sum k (fun j => elemSymm j x') Y
        have hmul : Y * F1 + Y * F2 = Y * elemSymm k x' := by
          rw [← mul_add]; exact congr_arg (Y * ·) hcs
        linarith [hF1, hF2, hmul]
      -- Final: (k+1)*(e' + Y*e) = A + Y*B' + C + Y*D' + (-1)^k*(p' + Y^(k+1))
      have hfinal : (↑(k+1):ℝ) * x (Fin.last n) * elemSymm k (x ∘ Fin.castSucc) =
                    x (Fin.last n) * ((↑k:ℝ) * elemSymm k (x ∘ Fin.castSucc)) +
                    x (Fin.last n) * elemSymm k (x ∘ Fin.castSucc) := by push_cast; ring
      push_cast
      linarith [hA, hB, hCD, hfinal]

end AmgmInequalityOQ02OQ01OQ02OQ01OQ03
