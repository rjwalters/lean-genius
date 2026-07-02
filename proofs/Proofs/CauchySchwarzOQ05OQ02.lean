import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Proofs.CauchySchwarzOQ05

/-
# The Binet–Cauchy Identity: Lagrange's Identity as a Product of Determinants (cauchy-schwarz-oq-05-oq-02)

## What This Proves

The parent entry `cauchy-schwarz-oq-05` proves **Lagrange's identity** — the exact
Cauchy–Schwarz defect — for two finite real sequences `a, b`:

  (∑ aᵢ²)(∑ bᵢ²) − (∑ aᵢbᵢ)² = ∑_{i<j} (aᵢbⱼ − aⱼbᵢ)².

Its open question asks whether this is the `n = 2` (two-row) case of a genuine
**Binet–Cauchy identity for products of determinants**. This file answers that
affirmatively by formalizing the four-sequence identity

  (∑ aᵢcᵢ)(∑ bᵢdᵢ) − (∑ aᵢdᵢ)(∑ bᵢcᵢ)
      = ∑_{i<j} (aᵢbⱼ − aⱼbᵢ)(cᵢdⱼ − cⱼdᵢ),

and then recovering Lagrange's identity as the diagonal specialization `c := a`, `d := b`.

Every factor here is a `2 × 2` determinant:
  * `aᵢbⱼ − aⱼbᵢ = det !![aᵢ, aⱼ; bᵢ, bⱼ]`  (a minor of the `2 × n` matrix `[a; b]`),
  * `cᵢdⱼ − cⱼdᵢ = det !![cᵢ, cⱼ; dᵢ, dⱼ]`,
  * the left-hand side `= det !![∑aᵢcᵢ, ∑aᵢdᵢ; ∑bᵢcᵢ, ∑bᵢdᵢ]` (the `2 × 2` Gram-type
    determinant of the row-pair `[a; b]` against `[c; d]`).

So `binet_cauchy_det` is literally the **Cauchy–Binet formula** for the product of a
`2 × n` and an `n × 2` matrix: the determinant of the product equals the sum over
increasing pairs `i < j` of the products of the corresponding `2 × 2` minors. Lagrange's
identity is the case where the two row-pairs coincide, so each pair of minors becomes a
square.

## Proof strategy

The core `binet_cauchy` mirrors the parent's proof of Lagrange's identity. Let
`F i j = (aᵢbⱼ − aⱼbᵢ)(cᵢdⱼ − cⱼdᵢ)`; it is symmetric (`F i j = F j i`) and vanishes on
the diagonal. The full double sum `∑ᵢ ∑ⱼ F i j` equals `2 · (LHS)` by expanding `F` into
four rank-one products and factoring each double sum, and equals `2 · (RHS)` by splitting
`s ×ˢ s` into diagonal + off-diagonal and applying the parent's triangle-doubling lemma
`LagrangeIdentityCS.sum_offDiag_eq_two_mul_sum_filter_lt`. Cancelling the `2` gives the result.

## Results
- `binet_cauchy`      : the four-sequence Binet–Cauchy identity (strict-upper-triangle form)
- `binet_cauchy_det`  : the same identity written entirely with `2 × 2` determinants
- `lagrange_identity` : Lagrange's identity recovered as the `c := a`, `d := b` case
- `cauchy_schwarz`    : Cauchy–Schwarz inequality as a corollary (RHS is a sum of squares)

Verified, 0-axiom (`propext` / `Classical.choice` / `Quot.sound` only).
-/

open Finset Matrix

namespace BinetCauchyCS

variable {ι : Type*} [LinearOrder ι]

/-- **Binet–Cauchy identity (two-row form).** For four finite real sequences the
"cross defect" of dot products equals the sum, over strictly increasing index pairs,
of the products of the corresponding `2 × 2` minors of `[a; b]` and `[c; d]`.

This is the honest generalization of Lagrange's identity: setting `c := a`, `d := b`
turns each product of minors into a square and recovers the parent entry. -/
theorem binet_cauchy (s : Finset ι) (a b c d : ι → ℝ) :
    (∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i)
        - (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i)
      = ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
          (a p.1 * b p.2 - a p.2 * b p.1) * (c p.1 * d p.2 - c p.2 * d p.1) := by
  set F : ι → ι → ℝ := fun i j => (a i * b j - a j * b i) * (c i * d j - c j * d i) with hF
  -- The symmetric double sum equals twice the cross defect.
  have hdouble : ∑ i ∈ s, ∑ j ∈ s, F i j
      = 2 * ((∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i)
             - (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i)) := by
    have hexp : ∀ i j, F i j =
        (a i * c i) * (b j * d j) - (a i * d i) * (b j * c j)
          - (b i * c i) * (a j * d j) + (b i * d i) * (a j * c j) := by
      intro i j; simp only [hF]; ring
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ i ∈ s, ∑ j ∈ s, (a i * c i) * (b j * d j)
        = (∑ i ∈ s, a i * c i) * (∑ j ∈ s, b j * d j) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    have h2 : ∑ i ∈ s, ∑ j ∈ s, (a i * d i) * (b j * c j)
        = (∑ i ∈ s, a i * d i) * (∑ j ∈ s, b j * c j) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    have h3 : ∑ i ∈ s, ∑ j ∈ s, (b i * c i) * (a j * d j)
        = (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; rw [mul_comm]
    have h4 : ∑ i ∈ s, ∑ j ∈ s, (b i * d i) * (a j * c j)
        = (∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; rw [mul_comm]
    rw [h1, h2, h3, h4]; ring
  -- The same double sum, split diagonal (zero) + off-diagonal (doubled upper triangle).
  have hsplit : ∑ i ∈ s, ∑ j ∈ s, F i j
      = 2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 := by
    have hprod : ∑ i ∈ s, ∑ j ∈ s, F i j = ∑ p ∈ s ×ˢ s, F p.1 p.2 := by
      rw [Finset.sum_product']
    rw [hprod, ← diag_union_offDiag s, Finset.sum_union (disjoint_diag_offDiag s),
        Finset.sum_diag]
    have hdiag : ∑ i ∈ s, F i i = 0 := by
      simp only [hF]; apply Finset.sum_eq_zero; intro i _; ring
    rw [hdiag, zero_add,
        LagrangeIdentityCS.sum_offDiag_eq_two_mul_sum_filter_lt s F
          (fun i j => by simp only [hF]; ring)]
  have hupper : 2 * ((∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i)
        - (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i))
      = 2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 := by
    rw [← hdouble, hsplit]
  have := mul_left_cancel₀ (two_ne_zero) hupper
  simpa only [hF] using this

/-- **Cauchy–Binet formula for the product of a `2 × n` and an `n × 2` matrix.**
The `binet_cauchy` identity written entirely with `2 × 2` determinants: the determinant
of the `2 × 2` Gram-type matrix of `[a; b]` against `[c; d]` equals the sum over
increasing pairs `i < j` of the products of the matching `2 × 2` minors. -/
theorem binet_cauchy_det (s : Finset ι) (a b c d : ι → ℝ) :
    Matrix.det !![∑ i ∈ s, a i * c i, ∑ i ∈ s, a i * d i;
                  ∑ i ∈ s, b i * c i, ∑ i ∈ s, b i * d i]
      = ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
          Matrix.det !![a p.1, a p.2; b p.1, b p.2]
            * Matrix.det !![c p.1, c p.2; d p.1, d p.2] := by
  simp only [Matrix.det_fin_two_of]
  exact binet_cauchy s a b c d

/-- **Lagrange's identity**, recovered as the diagonal case `c := a`, `d := b` of the
Binet–Cauchy identity: each product of minors becomes a squared minor. This reproduces
the statement of the parent entry `cauchy-schwarz-oq-05`. -/
theorem lagrange_identity (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2
      = ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
          (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 := by
  have h := binet_cauchy s a b a b
  have hcomm : ∑ i ∈ s, b i * a i = ∑ i ∈ s, a i * b i :=
    Finset.sum_congr rfl fun i _ => mul_comm (b i) (a i)
  rw [hcomm] at h
  simpa only [pow_two] using h

/-- **Cauchy–Schwarz inequality** as a corollary of Lagrange's identity: the defect is a
sum of squares, hence non-negative. -/
theorem cauchy_schwarz (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  have h := lagrange_identity s a b
  have hnn : 0 ≤ ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
      (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

end BinetCauchyCS
