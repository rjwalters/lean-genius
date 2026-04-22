/-
# Erdős Problem #1151 OQ04 — Lebesgue Function Approach to Interpolation Divergence

## Goal

Prove `erdos_1941_divergence` by formalizing the connection between:
1. The Lebesgue function Λₙ(x) = Σₖ |ℓₖⁿ(x)| (sum of absolute Lagrange basis values)
2. Its growth at rational cosine points: Λₙ(cos(πp/q)) → ∞ for odd p, q
3. The consequence: existence of continuous f with Chebyshev interpolation → +∞

## Proof Architecture

The main theorem `erdos_1941_divergence_from_growth` is FULLY PROVED
(i.e., is a valid mathematical deduction), assuming two sorry lemmas:

  `chebyshev_lebesgue_growth` [SORRY: trig sum lower bound]
  `divergence_from_lebesgue_growth` [SORRY: lacunary series construction]

The non-sorry results proved here:
  - `lebesgue_upper_bound`: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x)
  - `chebyshev_interp_linear_left`, `chebyshev_interp_linear_right`: linearity
  - `chebyshev_T_at_cos`: Tₙ(cos θ) = cos(nθ) — from Mathlib
  - `cos_rational_pi_multiple`: cos(kπp) = ±1 for integer k and odd p
  - `erdos_1941_divergence_from_growth`: main reduction theorem

## Sorry 1: chebyshev_lebesgue_growth
Proof requires:
  a) Explicit formula for Lagrange basis at Chebyshev nodes (uses Tₙ(cos θ) = cos(nθ))
  b) Lower bound on Σₖ sin(φₖ)/|cos θ - cos φₖ| growing like log(n)
  c) Nonvanishing of cos(nπp/q) along n = kq subsequence

## Sorry 2: divergence_from_lebesgue_growth
Proof requires:
  a) For each n, existence of optimizing continuous function with ‖f‖ ≤ 1 and Lₙf(x) = Λₙ(x)
  b) Lacunary subsequence construction: choose nₖ doubly exponential so cross terms
     |Lₙₖfⱼ(x)| ≤ Λₙₖ(x) are dominated by the main term Λₙₖ(x)/k²

Tags: analysis, approximation-theory, chebyshev, lebesgue-function, erdos-problems
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Tactic

namespace Erdos1151OQ04

open Finset Real Polynomial.Chebyshev

/-! ## Definitions: Chebyshev Nodes, Lagrange Interpolation, Lebesgue Function -/

/-- The k-th Chebyshev node of degree n: cos((2k+1)π/(2n)) for k = 0,...,n-1.
    These are the zeros of the n-th Chebyshev polynomial Tₙ. -/
noncomputable def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))

/-- Lagrange basis polynomial: ℓₖ(x) = Π_{i≠k} (x - xᵢ)/(xₖ - xᵢ). -/
noncomputable def lagrangeBasis (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (x - nodes i) / (nodes k - nodes i)

/-- Lagrange interpolation: Lₙf(x) = Σₖ f(xₖ) · ℓₖ(x). -/
noncomputable def lagrangeInterp (n : ℕ) (nodes : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, f (nodes k) * lagrangeBasis n nodes k x

/-- Chebyshev interpolation at the standard Chebyshev nodes. -/
noncomputable def chebyshevInterp (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  lagrangeInterp n (chebyshevNode n) f x

/-- The Lebesgue function: Λₙ(x) = Σₖ |ℓₖⁿ(x)|.
    Measures worst-case amplification: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x). -/
noncomputable def chebyshevLebesgue (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis n (chebyshevNode n) k x|

/-! ## Proved Results: Interpolation Bound -/

/-- The Lebesgue function is nonneg. -/
theorem chebyshevLebesgue_nonneg (n : ℕ) (x : ℝ) : 0 ≤ chebyshevLebesgue n x :=
  Finset.sum_nonneg fun k _ => abs_nonneg _

/-- **Key bound**: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x).

    The Lebesgue function Λₙ(x) is the operator norm of the evaluation functional
    f ↦ Lₙf(x) restricted to the unit sup-norm ball of C[-1,1]. -/
theorem lebesgue_upper_bound (n : ℕ) (nodes : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ)
    (M : ℝ) (hM : ∀ t, |f t| ≤ M) :
    |lagrangeInterp n nodes f x| ≤ M * ∑ k : Fin n, |lagrangeBasis n nodes k x| := by
  simp only [lagrangeInterp]
  calc |∑ k : Fin n, f (nodes k) * lagrangeBasis n nodes k x|
      ≤ ∑ k : Fin n, |f (nodes k) * lagrangeBasis n nodes k x| :=
          abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |f (nodes k)| * |lagrangeBasis n nodes k x| := by
          congr 1; ext k; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, M * |lagrangeBasis n nodes k x| := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
    _ = M * ∑ k : Fin n, |lagrangeBasis n nodes k x| := (Finset.mul_sum _ _ _).symm

/-- Chebyshev interpolation bound via the Lebesgue function. -/
theorem chebyshev_upper_bound (n : ℕ) (f : ℝ → ℝ) (x : ℝ) (M : ℝ)
    (hM : ∀ t, |f t| ≤ M) :
    |chebyshevInterp n f x| ≤ M * chebyshevLebesgue n x :=
  lebesgue_upper_bound n (chebyshevNode n) f x M hM

/-! ## Proved Results: Linearity -/

/-- Chebyshev interpolation is linear in f. -/
theorem chebyshevInterp_add (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t + g t) x =
    chebyshevInterp n f x + chebyshevInterp n g x := by
  simp only [chebyshevInterp, lagrangeInterp]
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

/-- Chebyshev interpolation scales with scalar multiplication. -/
theorem chebyshevInterp_smul (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => c * f t) x = c * chebyshevInterp n f x := by
  simp only [chebyshevInterp, lagrangeInterp]
  simp_rw [mul_assoc]
  exact (Finset.mul_sum _ _ _).symm

/-! ## Proved Results: Chebyshev Polynomial Connection -/

/-- **Chebyshev identity**: Tₙ(cos θ) = cos(nθ).
    This is the key identity for computing Lagrange basis at Chebyshev nodes:
    Since Tₙ vanishes at its roots (the Chebyshev nodes), we have
    Tₙ(x) = 2^(n-1) · ∏ₖ (x - xₖⁿ), giving an explicit formula for ℓₖ.
    Available in Mathlib as `Polynomial.Chebyshev.T_real_cos`. -/
theorem chebyshev_T_at_cos (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval (Real.cos θ) = Real.cos (n * θ) :=
  Polynomial.Chebyshev.T_real_cos θ n

/-- cos(kπ) = (-1)^k for any integer k.
    Mathlib has `Real.cos_int_mul_pi` for this exact statement.
    Used for proving cos(nπp/q) ≠ 0 along n = mq (then cos(mπp) = (-1)^(mp) ≠ 0). -/
theorem cos_int_pi (k : ℤ) : Real.cos (k * Real.pi) = (-1 : ℝ) ^ k :=
  Real.cos_int_mul_pi k

/-- Along the subsequence n = mq, the value cos(nπp/q) = cos(mπp) = ±1.
    This ensures the Lebesgue function is not killed by a vanishing cosine factor
    in the explicit formula ℓₖⁿ(x) ∝ cos(nθ)/sin(θ - φₖ). -/
theorem cos_rational_pi_at_multiples (p q m : ℕ) (hq_pos : 0 < q) :
    Real.cos ((m * q : ℕ) * (↑p * Real.pi / ↑q)) =
    Real.cos (↑m * ↑p * Real.pi) := by
  congr 1
  have hq' : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq_pos).ne'
  push_cast
  field_simp

/-! ## Key Lemmas with Sorry -/

/-- **[Key Step] Lagrange basis explicit formula at Chebyshev nodes.**

    For x = cos θ ≠ cos φₖ (where φₖ = (2k+1)π/(2n) are Chebyshev angles), the
    k-th Lagrange basis polynomial satisfies:
      ℓₖⁿ(cos θ) = cos(nθ) · sin(φₖ) / (n · (cos θ - cos φₖ) · (-1)^k)

    Proof via Chebyshev polynomial theory:
    1. Tₙ(x) = 2^{n-1} · Π_{i=0}^{n-1}(x - cos φᵢ) (leading coeff 2^{n-1})
       [This product formula is NOT currently in Mathlib — see TODO in Chebyshev.lean]
    2. So ℓₖⁿ(x) = Tₙ(x) / (Tₙ'(cos φₖ) · (x - cos φₖ))
    3. Tₙ'(x) = n · Uₙ₋₁(x) [T_derivative_eq_U from Mathlib]
    4. Uₙ₋₁(cos φₖ) = sin(nφₖ)/sin(φₖ) = (-1)^k/sin(φₖ) [U_real_cos + node formula]
    5. Result follows from Tₙ(cos θ) = cos(nθ) [T_real_cos from Mathlib] -/
theorem lagrange_basis_chebyshev_formula (n : ℕ) (hn : 0 < n) (k : Fin n) (θ : ℝ)
    (hne : Real.cos θ ≠ chebyshevNode n k) :
    lagrangeBasis n (chebyshevNode n) k (Real.cos θ) =
    Real.cos (n * θ) * Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
    (n * (Real.cos θ - chebyshevNode n k) * (-1 : ℝ)^k.val) := by
  sorry  -- Requires Chebyshev product formula (not in Mathlib v4.26.0)

/-- **[Key Step] Lebesgue function lower bound via explicit formula.**

    For x = cos θ with θ ≠ φₖ for all k:
    Λₙ(x) = |cos(nθ)| / n · Σₖ sin(φₖ) / |cos θ - cos φₖ|

    This is immediate from `lagrange_basis_chebyshev_formula`. -/
theorem chebyshev_lebesgue_eq (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (hne : ∀ k : Fin n, Real.cos θ ≠ chebyshevNode n k) :
    chebyshevLebesgue n (Real.cos θ) =
    |Real.cos (n * θ)| / n *
    ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                 |Real.cos θ - chebyshevNode n k| := by
  sorry  -- Follows from lagrange_basis_chebyshev_formula + triangle equality

/-- **[SORRY] Lebesgue function growth at rational cosines.**

    For x = cos(πp/q) with p, q odd and q ≥ 1, the Chebyshev Lebesgue
    function Λₙ(x) → ∞ as n → ∞.

    Proof outline (given lagrange_basis_chebyshev_formula):
    1. Along the subsequence n = mq:
       |cos(nπp/q)| = |cos(mπp)| = 1 (cos_rational_pi_nonzero_along_multiples)
    2. So Λₙ(x) = (1/n) · Σₖ sin(φₖ) / |cos(πp/q) - cos φₖ|  (chebyshev_lebesgue_eq)
    3. Using cos A - cos B = 2 sin((A+B)/2) sin((B-A)/2):
       |cos(πp/q) - cos φₖ| ≤ 2 · |πp/q - φₖ| (since sin t ≤ t for t ≥ 0)
    4. The Riemann sum Σₖ sin(φₖ) / |cos(πp/q) - cos φₖ| ≥ Σₖ C/|p/q - k/n| ≥ C'·log(n)
       (harmonic sum lower bound, avoiding the k near nπp/q term) -/
theorem chebyshev_lebesgue_growth (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hq_pos : 0 < q) :
    Filter.Tendsto (fun n => chebyshevLebesgue n (Real.cos (↑p * Real.pi / ↑q)))
      Filter.atTop Filter.atTop := by
  sorry

/-- **[SORRY] Divergence from Lebesgue growth.**

    If Λₙ(x) → ∞, then ∃ continuous f with Lₙf(x) → +∞.

    Proof outline:
    1. For each n, there exists fₙ with |fₙ| ≤ 1 and Lₙ(fₙ)(x) = Λₙ(x).
       Construction: fₙ(xₖⁿ) = sign(ℓₖⁿ(x)), extended piecewise linearly.
       Then Lₙfₙ(x) = Σₖ sign(ℓₖⁿ(x)) · ℓₖⁿ(x) = Σₖ |ℓₖⁿ(x)| = Λₙ(x). ✓

    2. Choose n₁ < n₂ < ... with Λₙₖ(x) ≥ k⁴ (possible since Λₙ → ∞).

    3. Define f = Σₖ (1/k²) · fₙₖ. This converges uniformly (Σ 1/k² < ∞)
       and f is continuous (uniform limit of continuous functions).

    4. Lₙₖ(f)(x) = (1/k²) · Λₙₖ(x) + Σⱼ≠ₖ (1/j²) · Lₙₖ(fₙⱼ)(x)
       Main term: Λₙₖ(x)/k² ≥ k²
       Cross terms: |Lₙₖ(fₙⱼ)(x)| ≤ Λₙₖ(x) [since ‖fₙⱼ‖_∞ ≤ 1]
       Cross sum: ≤ Λₙₖ(x) · Σⱼ≠ₖ (1/j²) ≤ Λₙₖ(x) · π²/6

    Note: Step 4 has a gap — the cross terms can dominate since Λₙₖ >> Λₙₖ/k².
    The fix requires choosing n₁ << n₂ << ... such that for j < k,
    |Lₙₖ(fₙⱼ)(x)| << Λₙₖ(x)/k² (lacunary condition on the subsequence).
    For Chebyshev interpolation specifically, functions supported near
    the n₁-node grid have small interpolation values at the nₖ-node grid
    when nₖ >> nⱼ (this requires additional analysis). -/
theorem divergence_from_lebesgue_growth (x : ℝ)
    (hgrowth : Filter.Tendsto (fun n => chebyshevLebesgue n x)
               Filter.atTop Filter.atTop) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterp n f x := by
  sorry

/-! ## Main Theorem (Proof Complete Modulo Sorries) -/

/-- **Erdős's Result (1941) — Lebesgue function proof.**

    For x = cos(πp/q) with odd p, q ≥ 1, there exists a continuous f
    such that the Chebyshev interpolation sequence Lₙf(x) → +∞.

    This theorem is a VALID MATHEMATICAL DEDUCTION: its proof is complete
    modulo two explicitly stated sorry lemmas (see above). The logical chain is:

      chebyshev_lebesgue_growth (sorry) ──┐
                                           ├──► erdos_1941_divergence_from_growth ✓
      divergence_from_lebesgue_growth (sorry)

    Progress: We have reduced the original axiom to two well-defined subgoals. -/
theorem erdos_1941_divergence_from_growth (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hq_pos : 0 < q) :
    let x := Real.cos (↑p * Real.pi / ↑q)
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterp n f x :=
  divergence_from_lebesgue_growth _
    (chebyshev_lebesgue_growth p q hp hq hq_pos)

/-! ## Auxiliary: Chebyshev Node Properties -/

/-- The Chebyshev nodes are zeros of T_n.
    Proof sketch: simp [chebyshevNode, T_real_cos] rewrites to cos(n·(2k+1)π/(2n)) = 0;
    simplify to cos(kπ + π/2) = 0 using Real.cos_add + cos_pi_div_two + sin_int_mul_pi. -/
theorem chebyshevNode_is_root (n : ℕ) (hn : 0 < n) (k : Fin n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (chebyshevNode n k) = 0 := by
  sorry  -- Aristotle candidate: routine trig computation via T_real_cos

/-- The Chebyshev nodes are distinct.
    Proof sketch: angles (2k+1)π/(2n) ∈ (0,π) are distinct (linear in k),
    and Real.cos_injOn_Icc gives injectivity of cos on [0,π]. -/
theorem chebyshevNode_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (chebyshevNode n) := by
  sorry  -- Aristotle candidate: injectivity of cos on [0,π] + linear ordering of nodes

/-- The Chebyshev nodes are contained in [-1, 1]. -/
theorem chebyshevNode_mem_Icc (n : ℕ) (k : Fin n) :
    chebyshevNode n k ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_cos _, cos_le_one _⟩

/-- The absolute value of cosine at integer multiples of π equals 1.
    From Mathlib: `Real.abs_cos_int_mul_pi`. -/
theorem abs_cos_int_pi_mul (k : ℤ) : |Real.cos (k * Real.pi)| = 1 :=
  Real.abs_cos_int_mul_pi k

/-- Along n = mq, cos(nπp/q) = cos(mπp) = (-1)^(mp) ≠ 0 for odd p.
    The proof uses cos_int_pi combined with the fact that (-1)^(mp) = ±1. -/
theorem cos_rational_pi_nonzero_along_multiples (p q m : ℕ) (hp : Odd p)
    (hq_pos : 0 < q) :
    Real.cos ((m * q : ℕ) * (↑p * Real.pi / ↑q)) ≠ 0 := by
  rw [cos_rational_pi_at_multiples p q m hq_pos]
  -- cos(mπp) = (-1)^(mp) ≠ 0
  rw [show (↑m * ↑p * Real.pi) = (↑(m * p) : ℤ) * Real.pi by push_cast; ring]
  rw [cos_int_pi]
  exact zpow_ne_zero _ (by norm_num)

end Erdos1151OQ04
