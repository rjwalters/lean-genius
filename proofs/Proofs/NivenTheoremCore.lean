import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

/-! Scratch attempt at the Niven algebraic-integer core (Route A: roots of unity).

    ⚠️ UNVERIFIED — build NOT confirmed. The Docker build was SIGTERM-killed during
    Mathlib cache decompression under host saturation (8+ concurrent lean4 containers,
    likely OOM) on 2026-06-16, and Aristotle was down (404). This file is a concrete
    next-session starting point, NOT a verified proof. It is an orphan (not imported by
    Proofs.lean) so it does not enter the `lake build` graph. Fragile Mathlib names to
    confirm first: `Complex.exp_int_mul_two_pi_mul_I`, `Complex.exp_mul_I`,
    `Complex.ofReal_cos`, `monic_X_pow_sub_C`, `isIntegral_algHom_iff`,
    `IsScalarTower.toAlgHom`, `IsIntegrallyClosed.isIntegral_iff`. -/

namespace NivenTheoremCore

open Polynomial

theorem two_cos_int_of_rational
    (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * Real.pi)
    (hcos : ∃ r : ℚ, Real.cos θ = r) :
    ∃ k : ℤ, 2 * Real.cos θ = k := by
  obtain ⟨r, hr⟩ := hcos
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  -- n * θ = m * π
  have hnθ : (n : ℝ) * θ = (m : ℝ) * Real.pi := by
    rw [hθ]; field_simp
  -- (n.natAbs : ℝ) * θ = M * π for some integer M
  obtain ⟨M, hM⟩ : ∃ M : ℤ, (n.natAbs : ℝ) * θ = (M : ℝ) * Real.pi := by
    rcases Int.natAbs_eq n with hpos | hneg
    · refine ⟨m, ?_⟩
      have hc : (n.natAbs : ℝ) = (n : ℝ) := by rw [hpos]; push_cast; ring
      rw [hc]; exact hnθ
    · refine ⟨-m, ?_⟩
      have hc : (n.natAbs : ℝ) = -(n : ℝ) := by rw [hneg]; push_cast; ring
      rw [hc]; push_cast; rw [neg_mul, hnθ]; ring
  set N : ℕ := 2 * n.natAbs with hNdef
  have hNge1 : 1 ≤ N := by
    have : 1 ≤ n.natAbs := Int.one_le_abs (by exact_mod_cast hn) |>.trans_eq (by rfl)
    omega
  set z : ℂ := Complex.exp (↑θ * Complex.I) with hz
  -- z ^ N = 1
  have hroot : z ^ N = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have hexp : (↑N : ℂ) * (↑θ * Complex.I) = (M : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      have hreal : (N : ℝ) * θ = (M : ℝ) * (2 * Real.pi) := by
        rw [hNdef]; push_cast; linear_combination (2 : ℝ) * hM
      have hcast : (↑N : ℂ) * (↑θ * Complex.I) = ((N : ℝ) * θ : ℝ) * Complex.I := by
        push_cast; ring
      rw [hcast, hreal]; push_cast; ring
    rw [hexp]; exact Complex.exp_int_mul_two_pi_mul_I M
  -- z ≠ 0
  have hz_ne : z ≠ 0 := Complex.exp_ne_zero _
  -- z is an algebraic integer (root of monic X^N - 1)
  have hz_int : IsIntegral ℤ z := by
    refine ⟨X ^ N - C 1, monic_X_pow_sub_C 1 (by omega), ?_⟩
    rw [map_sub, aeval_X_pow, map_one, hroot, sub_self]
  -- z⁻¹ = z ^ (N-1), also integral
  have hzinv_pow : z⁻¹ = z ^ (N - 1) := by
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← pow_succ, Nat.sub_add_cancel hNge1, hroot]
  have hzinv_int : IsIntegral ℤ z⁻¹ := by
    rw [hzinv_pow]; exact hz_int.pow _
  -- z + z⁻¹ = 2 cos θ  (as a complex number)
  have hzinv_exp : z⁻¹ = Complex.exp ((-↑θ) * Complex.I) := by
    rw [hz, ← Complex.exp_neg]; ring_nf
  have hsum : z + z⁻¹ = ((2 * Real.cos θ : ℝ) : ℂ) := by
    rw [hz, hzinv_exp, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos]
    push_cast; ring
  -- 2 cos θ is an algebraic integer over ℤ (viewed in ℂ)
  have hint_c : IsIntegral ℤ (((2 * Real.cos θ : ℝ)) : ℂ) := by
    rw [← hsum]; exact hz_int.add hzinv_int
  -- rewrite as a rational cast
  have hqc : (((2 * Real.cos θ : ℝ)) : ℂ) = ((2 * r : ℚ) : ℂ) := by
    rw [hr]; push_cast; ring
  have hint_q_c : IsIntegral ℤ (((2 * r : ℚ)) : ℂ) := hqc ▸ hint_c
  -- reflect integrality along the injective ℤ-algebra map ℚ → ℂ
  have hinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
  have hint_q : IsIntegral ℤ (2 * r : ℚ) := by
    have key := (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℂ) hinj)
    have : (IsScalarTower.toAlgHom ℤ ℚ ℂ) (2 * r) = ((2 * r : ℚ) : ℂ) := rfl
    rw [← key]; rw [this]; exact hint_q_c
  -- a rational algebraic integer is an integer
  obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hint_q
  refine ⟨k, ?_⟩
  have : ((k : ℚ) : ℝ) = ((2 * r : ℚ) : ℝ) := by rw [hk]
  push_cast at this ⊢
  rw [hr]; push_cast; linarith [this]

end NivenTheoremCore
