/-
  Variance of Sums (Second Moment Method — Generic Decomposition)

  The variance computation for indicator sums, in the discrete Finset-ℚ
  setting consistent with `ProbMethodSecondMoment.lean`.

  The headline identity is the bilinear pair-sum form

      Var(∑_{i ∈ t} X i) = ∑_{(i,j) ∈ t ×ˢ t} Cov(X i, X j),

  which a follow-up PR can split into the textbook decomposition

      Var(∑_{i ∈ t} X i) = ∑_{i ∈ t} Var(X i) + ∑_{i ≠ j} Cov(X i, X j)

  via `Finset.diag_union_offDiag`.

  This is the algebraic backbone of any second-moment threshold argument:
  applying Chebyshev / Paley-Zygmund (the parent file) to a sum of
  indicators reduces to a per-pair covariance computation. The identity
  itself is purely algebraic — no indicator hypothesis is required.

  Working setting (matches parent): the "sample space" is a Finset `s`
  with counting measure, and a "random variable" is `f : α → ℚ`. Means
  and (co)variances are defined over ℚ via Finset sums and cardinalities,
  avoiding measure theory.

  Open question OQ-02 (parent: prob-method-second-moment):
  "Can the variance computation for indicator sums be formalized
  generically to handle subgraph counting in G(n,p) and derive specific
  threshold functions?" This file ships §A: the generic pair-sum form of
  variance and the bilinear/symmetric API needed to instantiate it. The
  G(n,p) construction and explicit threshold functions are follow-up
  scope (see state.md "Sequence A / §B / §C").
-/
import Mathlib
import Proofs.ProbMethodSecondMoment

set_option linter.unusedVariables false

namespace ProbMethod.SecondMoment

/-! ## Mean, variance, and covariance over a Finset

We work with ℚ-valued functions on a Finset `s`. The mean is the
arithmetic average; variance is the mean of the squared deviation;
covariance is the bilinear analogue.
-/

/-- Arithmetic mean of `f : α → ℚ` on a Finset `s`. -/
def mean {α : Type*} (s : Finset α) (f : α → ℚ) : ℚ :=
  s.sum f / s.card

/-- Variance of `f` on `s`: mean of `(f − mean f)²`. -/
def variance {α : Type*} (s : Finset α) (f : α → ℚ) : ℚ :=
  s.sum (fun a => (f a - mean s f) ^ 2) / s.card

/-- Covariance of `f` and `g` on `s`: mean of `(f − mean f) · (g − mean g)`. -/
def covariance {α : Type*} (s : Finset α) (f g : α → ℚ) : ℚ :=
  s.sum (fun a => (f a - mean s f) * (g a - mean s g)) / s.card

/-! ## Basic identities: symmetry and additivity -/

/-- Variance is the covariance of `f` with itself. -/
theorem variance_eq_covariance_self {α : Type*} (s : Finset α) (f : α → ℚ) :
    variance s f = covariance s f f := by
  simp only [variance, covariance, sq]

/-- Covariance is symmetric. -/
theorem covariance_symm {α : Type*} (s : Finset α) (f g : α → ℚ) :
    covariance s f g = covariance s g f := by
  simp only [covariance]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- The mean is additive. -/
theorem mean_add {α : Type*} (s : Finset α) (f g : α → ℚ) :
    mean s (fun a => f a + g a) = mean s f + mean s g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

/-- Covariance is additive in its first slot. -/
theorem covariance_add_left {α : Type*} (s : Finset α) (f₁ f₂ g : α → ℚ) :
    covariance s (fun a => f₁ a + f₂ a) g =
      covariance s f₁ g + covariance s f₂ g := by
  simp only [covariance, mean_add]
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- Covariance is additive in its second slot. -/
theorem covariance_add_right {α : Type*} (s : Finset α) (f g₁ g₂ : α → ℚ) :
    covariance s f (fun a => g₁ a + g₂ a) =
      covariance s f g₁ + covariance s f g₂ := by
  rw [covariance_symm, covariance_add_left,
      covariance_symm s f g₁, covariance_symm s f g₂]

/-! ## Variance of a sum -/

/-- Variance of a pair sum:
    `Var(f + g) = Var f + Var g + 2 · Cov(f, g)`. -/
theorem variance_add {α : Type*} (s : Finset α) (f g : α → ℚ) :
    variance s (fun a => f a + g a) =
      variance s f + variance s g + 2 * covariance s f g := by
  rw [variance_eq_covariance_self s (fun a => f a + g a),
      variance_eq_covariance_self s f, variance_eq_covariance_self s g,
      covariance_add_left, covariance_add_right, covariance_add_right,
      covariance_symm s g f]
  ring

/-- Covariance of a Finset-indexed sum (first slot). -/
theorem covariance_sum_left {α ι : Type*} [DecidableEq ι] (s : Finset α)
    (t : Finset ι) (X : ι → α → ℚ) (g : α → ℚ) :
    covariance s (fun a => t.sum (fun i => X i a)) g =
      t.sum (fun i => covariance s (X i) g) := by
  induction t using Finset.induction_on with
  | empty =>
    -- LHS: covariance s (fun a => 0) g = 0; RHS: empty sum = 0.
    have hzero :
        (fun a : α => (∅ : Finset ι).sum (fun i => X i a)) = (fun _ : α => (0 : ℚ)) := by
      funext a; simp
    rw [hzero, Finset.sum_empty]
    -- covariance s (fun _ => 0) g = 0
    simp only [covariance, mean, Finset.sum_const_zero, zero_div, sub_zero, zero_mul]
  | @insert i t hi ih =>
    have hpoint :
        (fun a : α => (insert i t).sum (fun j => X j a)) =
          (fun a : α => X i a + t.sum (fun j => X j a)) := by
      funext a
      rw [Finset.sum_insert hi]
    rw [hpoint, covariance_add_left, ih, Finset.sum_insert hi]

/-- Covariance of a Finset-indexed sum (second slot). -/
theorem covariance_sum_right {α ι : Type*} [DecidableEq ι] (s : Finset α)
    (t : Finset ι) (f : α → ℚ) (Y : ι → α → ℚ) :
    covariance s f (fun a => t.sum (fun j => Y j a)) =
      t.sum (fun j => covariance s f (Y j)) := by
  rw [covariance_symm, covariance_sum_left]
  exact Finset.sum_congr rfl (fun j _ => covariance_symm _ _ _)

/-- **Pair-sum form** of the variance decomposition: the variance of a
finite sum equals the double sum of covariances over all index pairs.

This is the cleanest algebraic form and directly serves the second-moment
method: applying Chebyshev / Paley-Zygmund to `∑ X i` reduces to bounding
the pair-covariance sum, which for independent indicators collapses to a
diagonal `∑ Var(X i)` plus zero off-diagonal terms. -/
theorem variance_sum_eq_sum_covariance {α ι : Type*} [DecidableEq ι]
    (s : Finset α) (t : Finset ι) (X : ι → α → ℚ) :
    variance s (fun a => t.sum (fun i => X i a)) =
      (t ×ˢ t).sum (fun p => covariance s (X p.1) (X p.2)) := by
  rw [variance_eq_covariance_self, covariance_sum_left, Finset.sum_product]
  exact Finset.sum_congr rfl (fun i _ => covariance_sum_right _ _ _ _)

end ProbMethod.SecondMoment
