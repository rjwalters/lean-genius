/-
  Newton's Inequality for Signed (Real) Inputs — Reciprocal Duality
  Research: amgm-inequality-oq-02-oq-02-oq-01

  Background.  The parent entry (amgm-inequality-oq-02-oq-02,
  `NewtonLogConcavity`) proves Newton's log-concavity
      (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1))·(eₖ₊₁/C(n,k+1))
  for **non-negative** inputs, by an induction on n that uses the sign of the
  eⱼ in an essential way.  Classically, however, Newton's inequalities hold for
  **all real** inputs (the polynomial ∏(t - xᵢ) is real-rooted regardless of the
  signs of its roots).  This file works toward the signed statement.

  What is already signed in the gallery.  The k = 1 case is already fully
  general: `maclaurin_sq_m1_ge_m2_general` (in `AmgmInequalityOQ02Defs`) proves
      C(n,2)·(∑ xᵢ)² ≥ n²·e₂
  for arbitrary `x : Fin n → ℝ`, with no sign hypothesis (it is exactly
  Cauchy–Schwarz / `∑ᵢⱼ (xᵢ - xⱼ)² ≥ 0`).  In cleared form this is Newton at
  k = 1: `p₁² ≥ p₀ p₂`.

  New content here.
  * `elemSymm_inv_mul`: the reciprocal identity
        eₖ(1/x₁,…,1/xₙ)·eₙ(x) = e_{n-k}(x)      (all xᵢ ≠ 0),
    proved by the complement bijection S ↦ Sᶜ on k-subsets.
  * `newton_signed_top`: Newton's inequality at the **top index** k = n-1, for
    all n and all nonzero real inputs:
        C(n,2)·e_{n-1}² ≥ n²·e_{n-2}·eₙ,
    obtained by applying the (already signed) k = 1 inequality to the
    reciprocals yᵢ = 1/xᵢ and clearing eₙ².  This transports signedness from
    the bottom index to the top index for every n.
  * `newton_n3_k2_signed`: the n = 3, k = 2 case for arbitrary reals (including
    zeros), by an explicit sum-of-squares certificate
        (ab+bc+ca)² - 3abc(a+b+c) = ½[(ab-bc)² + (bc-ca)² + (ca-ab)²].
    The gallery's `newton_n3_k2` states the same inequality but assumes
    a,b,c ≥ 0; the certificate above shows the hypothesis is unnecessary.

  Frontier.  The intermediate indices 1 < k < n-1 for general n still require
  the real-rootedness / Rolle machinery (differentiate ∏(t-xᵢ), which stays
  real-rooted, to reduce k) and are NOT proved here; see the note at the end.

  References:
  - Hardy–Littlewood–Pólya, "Inequalities" (1934), §2.22, Theorem 51.
  - Niculescu–Persson, "Convex Functions and Their Applications" (2006), §4.
-/

import Mathlib
import Proofs.AmgmInequalityOQ02Defs

open Finset Real

namespace NewtonSigned

/-
## Part I: The reciprocal identity  eₖ(1/x)·eₙ(x) = e_{n-k}(x)
-/

/-- **Reciprocal duality for elementary symmetric polynomials.**
For nonzero reals `x₁,…,xₙ` and `k ≤ n`,
    eₖ(1/x₁,…,1/xₙ) · eₙ(x) = e_{n-k}(x).
Proof: multiply through by eₙ(x) = ∏ xᵢ; the term for a `k`-subset `S`,
`(∏_{i∈S} xᵢ⁻¹)·∏ᵢ xᵢ = ∏_{i∈Sᶜ} xᵢ`, and `S ↦ Sᶜ` is a bijection from
`k`-subsets to `(n-k)`-subsets. -/
lemma elemSymm_inv_mul {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ≠ 0) :
    elemSymm k (fun i => (x i)⁻¹) * elemSymm n x = elemSymm (n - k) x := by
  rw [show elemSymm n x = ∏ i, x i from elemSymm_n_eq_prod x]
  simp only [elemSymm]
  rw [Finset.sum_mul]
  -- Transform each summand `(∏_{i∈S} xᵢ⁻¹)·∏ᵢ xᵢ` into `∏_{i∈Sᶜ} xᵢ`.
  have step : ∀ S ∈ (univ : Finset (Fin n)).powersetCard k,
      (∏ i ∈ S, (x i)⁻¹) * ∏ i, x i = ∏ i ∈ Sᶜ, x i := by
    intro S _
    have hSne : (∏ i ∈ S, x i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
    rw [Finset.prod_inv_distrib, ← Finset.prod_mul_prod_compl S x,
        inv_mul_cancel_left₀ hSne]
  rw [Finset.sum_congr rfl step]
  -- Reindex by the complement bijection S ↦ Sᶜ.
  refine Finset.sum_bij' (fun S _ => Sᶜ) (fun T _ => Tᶜ) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_compl, Fintype.card_fin, hS.2]⟩
  · intro T hT
    rw [Finset.mem_powersetCard] at hT ⊢
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_compl, Fintype.card_fin, hT.2]; omega
  · intro S _; exact compl_compl S
  · intro T _; exact compl_compl T
  · intro S _; rfl

/-
## Part II: Signed Newton at the top index  k = n-1
-/

/-- **Newton's inequality at the top index, for signed inputs.**
For all `n ≥ 2` and all nonzero reals `x₁,…,xₙ`,
    C(n,2)·e_{n-1}(x)² ≥ n²·e_{n-2}(x)·eₙ(x).
This is the cleared form of `p_{n-1}² ≥ p_{n-2} p_n`.  It is obtained by
applying the (already signed) k = 1 inequality
`maclaurin_sq_m1_ge_m2_general` to the reciprocals `yᵢ = 1/xᵢ` and clearing the
positive factor `eₙ(x)²`, using the reciprocal identity `elemSymm_inv_mul`. -/
theorem newton_signed_top {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ≠ 0) :
    (Nat.choose n 2 : ℝ) * (elemSymm (n - 1) x) ^ 2
      ≥ (n : ℝ) ^ 2 * (elemSymm (n - 2) x * elemSymm n x) := by
  -- The k = 1 inequality applied to the reciprocals.
  have hk1 := maclaurin_sq_m1_ge_m2_general hn (fun i => (x i)⁻¹)
  rw [← elemSymm_one] at hk1
  have hk1' : (n : ℝ) ^ 2 * elemSymm 2 (fun i => (x i)⁻¹)
      ≤ (Nat.choose n 2 : ℝ) * (elemSymm 1 (fun i => (x i)⁻¹)) ^ 2 := hk1
  -- eₙ(x) ≠ 0, hence eₙ(x)² > 0.
  have e_n_ne : elemSymm n x ≠ 0 := by
    rw [elemSymm_n_eq_prod]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  have hpos : (0 : ℝ) < (elemSymm n x) ^ 2 := by
    rw [pow_two]; exact mul_self_pos.mpr e_n_ne
  -- Reciprocal identities.
  have id1 : elemSymm 1 (fun i => (x i)⁻¹) * elemSymm n x = elemSymm (n - 1) x :=
    elemSymm_inv_mul 1 (by omega) x hx
  have id2 : elemSymm 2 (fun i => (x i)⁻¹) * elemSymm n x = elemSymm (n - 2) x :=
    elemSymm_inv_mul 2 (by omega) x hx
  -- Multiply the k = 1 inequality by eₙ(x)² and substitute.
  have key := mul_le_mul_of_nonneg_right hk1' hpos.le
  have h1 : elemSymm 1 (fun i => (x i)⁻¹) ^ 2 * elemSymm n x ^ 2
      = elemSymm (n - 1) x ^ 2 := by rw [← mul_pow, id1]
  have h2 : elemSymm 2 (fun i => (x i)⁻¹) * elemSymm n x ^ 2
      = elemSymm (n - 2) x * elemSymm n x := by rw [pow_two, ← mul_assoc, id2]
  have hL : (n : ℝ) ^ 2 * elemSymm 2 (fun i => (x i)⁻¹) * elemSymm n x ^ 2
      = (n : ℝ) ^ 2 * (elemSymm (n - 2) x * elemSymm n x) := by rw [mul_assoc, h2]
  have hR : (Nat.choose n 2 : ℝ) * elemSymm 1 (fun i => (x i)⁻¹) ^ 2 * elemSymm n x ^ 2
      = (Nat.choose n 2 : ℝ) * elemSymm (n - 1) x ^ 2 := by rw [mul_assoc, h1]
  rw [hL, hR] at key
  exact key

/-
## Part III: The n = 3, k = 2 case for arbitrary reals (via sum of squares)
-/

/-- **Newton's inequality for n = 3, k = 2, signed inputs (including zeros).**
    ((ab+bc+ca)/3)² ≥ ((a+b+c)/3)·(abc)
for all reals `a, b, c`.  The gallery's `newton_n3_k2` proves the same
inequality assuming `a, b, c ≥ 0`; the sum-of-squares certificate below shows
that hypothesis is unnecessary:
    (ab+bc+ca)² - 3abc(a+b+c) = ½[(ab-bc)² + (bc-ca)² + (ca-ab)²] ≥ 0. -/
theorem newton_n3_k2_signed (a b c : ℝ) :
    ((a * b + b * c + c * a) / 3) ^ 2 ≥ ((a + b + c) / 3) * (a * b * c) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
             sq_nonneg (c * a - a * b)]

/-
## Frontier: the intermediate indices 1 < k < n-1

For general `n`, the indices strictly between the bottom (k = 1, Cauchy–Schwarz)
and the top (k = n-1, this file, via reciprocal duality) are not covered by an
elementary sum-of-squares or duality argument.  The classical route is:

  1.  P(t) = ∏ᵢ (t - xᵢ) has all real roots.
  2.  P'(t) has all real roots (Rolle between consecutive roots of P).
  3.  The coefficients of P' are `(n-j)·eⱼ(x)`, so the eⱼ of the roots of P'
      are proportional to those of x; differentiating k-1 times and reversing
      reduces Newton at index k to the discriminant of a real quadratic.

Step 2 (differentiation preserves real-rootedness) requires Rolle's theorem
applied across a multiset of real roots and Vieta's formulas for the
derivative; this is a substantial analytic formalization (Mathlib has
`Polynomial.derivative` and mean-value infrastructure but not a packaged
"derivative of a real-rooted polynomial is real-rooted" lemma).  It is left as
the open piece of this problem.
-/

end NewtonSigned
