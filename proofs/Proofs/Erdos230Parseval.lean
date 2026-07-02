/-
  Erdős #230 — discrete Parseval witness (fully proved).

  Goal: prove that for a unimodular polynomial of degree n ≥ 1 there is a point
  on the unit circle (an n-th root of unity) where |P(ω)|² ≥ n.

  Mathematical content (averaging over the n-th roots of unity ζ^j, j < n):
    Σ_{j<n} |P(ζ^j)|² = Σ_{j<n} Σ_{k,l} a_k conj(a_l) (ζ^j)^{k+1} conj((ζ^j)^{l+1})
                       = Σ_{k,l} a_k conj(a_l) Σ_{j<n} (ζ^{k+1} conj(ζ)^{l+1})^j.
  The inner geometric sum is n when k = l (the base equals 1, since ζ·conj ζ = 1)
  and 0 otherwise (root-of-unity orthogonality, `geom_sum_mul` with base^n = 1,
  base ≠ 1).  Hence the total is n · Σ_k |a_k|² = n · n = n², so the average over
  the n points is n and the maximum is ≥ n.

  This file separates the argument into:

    * `geom_root_sum`           — the *orthogonality core*.  For any `w` with
      `w^n = 1`, `Σ_{j<n} w^j` is `n` if `w = 1` and `0` otherwise.  Proved from
      `geom_sum_mul` (elementary; the one genuinely computational ingredient).

    * `exists_of_sum_normSq`    — the *averaging / pigeonhole* step.  If `n`
      unit-circle points carry total mass `Σ |P(pts j)|² = n²`, then one of them
      has `|P(z)|² ≥ n`.  Elementary.

    * `exists_roots_sum_normSq` — the *discrete Parseval identity* itself
      `Σ_j |P(ζ^j)|² = n²`, assembled from `geom_root_sum` and the
      root-of-unity orthogonality bookkeeping.  Previously a `sorry`; now proved.

  Combining them gives `exists_root_normSq_ge`, which
  `Erdos230.LowerBound.supNorm_ge_sqrt_of` turns into the sup-norm lower bound
  `‖P‖_∞ ≥ √n`, discharging the axiom `Erdos230.supNorm_ge_l2norm`.
-/

import Mathlib
import Proofs.Erdos230Problem

namespace Erdos230.Parseval

open Erdos230 Complex Finset ComplexConjugate

/-- **Orthogonality core (root-of-unity geometric sum).**
For any complex `w` with `w ^ n = 1`, the sum of its first `n` powers is `n`
when `w = 1` and `0` otherwise.  This is the sole genuinely computational
ingredient of the discrete Parseval identity; it follows from `geom_sum_mul`
(no harmonic analysis). -/
theorem geom_root_sum {n : ℕ} {w : ℂ} (hw : w ^ n = 1) :
    ∑ j : Fin n, w ^ (j : ℕ) = if w = 1 then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => w ^ i)]
  by_cases h1 : w = 1
  · subst h1
    rw [if_pos rfl]
    simp [Finset.card_range]
  · rw [if_neg h1]
    have hsub : w - 1 ≠ 0 := sub_ne_zero_of_ne h1
    have hgs := geom_sum_mul w n
    rw [hw, sub_self] at hgs
    exact (mul_eq_zero.mp hgs).resolve_right hsub

/-- **Averaging / pigeonhole step (elementary).**
If `n` points on the unit circle carry total squared mass `Σ_j |P(pts j)|² = n²`,
then at least one of them satisfies `|P(z)|² ≥ n`.  Pure averaging — no harmonic
analysis is used. -/
theorem exists_of_sum_normSq {n : ℕ} (hn : 1 ≤ n) (P : UnimodularPolynomial n)
    (pts : Fin n → ℂ) (hpts : ∀ j, ‖pts j‖ = 1)
    (hsum : ∑ j : Fin n, Complex.normSq (evaluate P (pts j)) = (n : ℝ) ^ 2) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (n : ℝ) ≤ Complex.normSq (evaluate P z) := by
  by_contra h
  push_neg at h
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  -- every term is strictly below `n`, so the total is strictly below `n · n`
  have hlt : ∀ j : Fin n, Complex.normSq (evaluate P (pts j)) < (n : ℝ) :=
    fun j => h (pts j) (hpts j)
  have hsum_lt : ∑ j : Fin n, Complex.normSq (evaluate P (pts j))
      < ∑ _j : Fin n, (n : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hlt j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum,
    pow_two] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-- **Discrete Parseval identity.**
There exist `n` unit-circle points — the n-th roots of unity `ζ^j` — whose total
squared mass under `P` is exactly `n²`.  This packages the root-of-unity
orthogonality computation. -/
theorem exists_roots_sum_normSq {n : ℕ} (hn : 1 ≤ n) (P : UnimodularPolynomial n) :
    ∃ pts : Fin n → ℂ, (∀ j, ‖pts j‖ = 1) ∧
      ∑ j : Fin n, Complex.normSq (evaluate P (pts j)) = (n : ℝ) ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by omega
  -- The primitive n-th root of unity.
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζpow : ζ ^ n = 1 := hζ.pow_eq_one
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζpow hn0
  have hζne : ζ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm
  -- ζ · conj ζ = 1 and conj ζ · ζ = 1.
  have hcc : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj]
    have hns : Complex.normSq ζ = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [hns]; norm_num
  have hccl : conj ζ * ζ = 1 := by rw [mul_comm]; exact hcc
  -- (conj ζ) ^ n = 1.
  have hconjpow : (conj ζ) ^ n = 1 := by rw [← map_pow, hζpow, map_one]
  -- Orthogonality of the shifted powers ζ^{k+1}·conj(ζ)^{l+1}.
  have hβeq : ∀ k l : Fin n,
      (∑ j : Fin n, (ζ ^ (k.val + 1) * (conj ζ) ^ (l.val + 1)) ^ (j : ℕ))
        = if k = l then (n : ℂ) else 0 := by
    intro k l
    have hwn : (ζ ^ (k.val + 1) * (conj ζ) ^ (l.val + 1)) ^ n = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k.val + 1) n, mul_comm (l.val + 1) n,
        pow_mul, pow_mul, hζpow, hconjpow, one_pow, one_pow, mul_one]
    rw [geom_root_sum hwn]
    by_cases hkl : k = l
    · have hb1 : ζ ^ (k.val + 1) * (conj ζ) ^ (l.val + 1) = 1 := by
        subst hkl; rw [← mul_pow, hcc, one_pow]
      rw [if_pos hb1, if_pos hkl]
    · have hb0 : ζ ^ (k.val + 1) * (conj ζ) ^ (l.val + 1) ≠ 1 := by
        intro hb
        apply hkl
        -- from base = 1 derive ζ^{k+1} = ζ^{l+1}
        have e1 : (conj ζ) ^ (l.val + 1) * ζ ^ (l.val + 1) = 1 := by
          rw [← mul_pow, hccl, one_pow]
        have key : ζ ^ (k.val + 1) = ζ ^ (l.val + 1) := by
          calc ζ ^ (k.val + 1)
              = ζ ^ (k.val + 1) * ((conj ζ) ^ (l.val + 1) * ζ ^ (l.val + 1)) := by
                rw [e1, mul_one]
            _ = (ζ ^ (k.val + 1) * (conj ζ) ^ (l.val + 1)) * ζ ^ (l.val + 1) := by
                ring
            _ = 1 * ζ ^ (l.val + 1) := by rw [hb]
            _ = ζ ^ (l.val + 1) := by rw [one_mul]
        -- cancel the extra factor of ζ and use injectivity of ζ^· on Fin n
        rw [pow_succ, pow_succ] at key
        have hc : ζ ^ k.val = ζ ^ l.val := mul_right_cancel₀ hζne key
        exact Fin.ext (hζ.pow_inj k.isLt l.isLt hc)
      rw [if_neg hb0, if_neg hkl]
  -- Assemble.
  refine ⟨fun j => ζ ^ (j : ℕ), ?_, ?_⟩
  · intro j
    rw [norm_pow, hnorm, one_pow]
  · -- Prove the identity over ℂ, then descend to ℝ.
    have hkey : (∑ j : Fin n, (Complex.normSq (evaluate P (ζ ^ (j : ℕ))) : ℂ))
        = (n : ℂ) ^ 2 := by
      -- Expand each squared modulus into a double sum.
      have expand : ∀ j : Fin n,
          (Complex.normSq (evaluate P (ζ ^ (j : ℕ))) : ℂ)
            = ∑ k : Fin n, ∑ l : Fin n,
                (P.coeffs k * conj (P.coeffs l)) *
                  ((ζ ^ (j : ℕ)) ^ (k.val + 1) * conj ((ζ ^ (j : ℕ)) ^ (l.val + 1))) := by
        intro j
        rw [← Complex.mul_conj]
        simp only [evaluate, map_sum, map_mul]
        rw [Fintype.sum_mul_sum]
        exact Finset.sum_congr rfl
          (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
      simp_rw [expand]
      -- Pull the coefficient product out of the innermost sum and apply orthogonality:
      -- for each fixed `k`, the double sum over `j` and `l` collapses to `n`.
      have hfull : ∀ k : Fin n,
          (∑ j : Fin n, ∑ l : Fin n,
              (P.coeffs k * conj (P.coeffs l)) *
                ((ζ ^ (j : ℕ)) ^ (k.val + 1) * conj ((ζ ^ (j : ℕ)) ^ (l.val + 1))))
            = (n : ℂ) := by
        intro k
        rw [Finset.sum_comm]
        have hinner : ∀ l : Fin n,
            (∑ j : Fin n,
                (P.coeffs k * conj (P.coeffs l)) *
                  ((ζ ^ (j : ℕ)) ^ (k.val + 1) * conj ((ζ ^ (j : ℕ)) ^ (l.val + 1))))
              = (P.coeffs k * conj (P.coeffs l)) * (if k = l then (n : ℂ) else 0) := by
          intro l
          rw [← Finset.mul_sum, ← hβeq k l]
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_pow, map_pow, pow_right_comm ζ, pow_right_comm (conj ζ), ← mul_pow]
        simp_rw [hinner]
        -- Only the diagonal l = k survives.
        rw [Finset.sum_eq_single k]
        · rw [if_pos rfl]
          have hone : P.coeffs k * conj (P.coeffs k) = 1 := by
            rw [Complex.mul_conj]
            have : Complex.normSq (P.coeffs k) = 1 := by
              rw [Complex.normSq_eq_norm_sq, P.unimodular k]; norm_num
            rw [this]; norm_num
          rw [hone, one_mul]
        · intro l _ hlk
          rw [if_neg (fun h => hlk h.symm), mul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      -- Reorder ∑_j ∑_k ∑_l  →  ∑_k ∑_j ∑_l, then collapse via `hfull`.
      rw [Finset.sum_comm]
      simp_rw [hfull]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    exact_mod_cast hkey

/-- **Discrete Parseval witness.**
For `n ≥ 1` and a unimodular polynomial `P` of degree `n`, some point on the
unit circle has `|P(z)|² ≥ n`.  Assembled from the averaging step
`exists_of_sum_normSq` and the discrete-Parseval identity
`exists_roots_sum_normSq`. -/
theorem exists_root_normSq_ge {n : ℕ} (hn : 1 ≤ n) (P : UnimodularPolynomial n) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (n : ℝ) ≤ Complex.normSq (evaluate P z) := by
  obtain ⟨pts, hpts, hsum⟩ := exists_roots_sum_normSq hn P
  exact exists_of_sum_normSq hn P pts hpts hsum

end Erdos230.Parseval
