import Mathlib

/-! # Near-regular cut arithmetic at order 81

This file kernel-packages the finite arithmetic step in the q=9 three-high
second-profile connectivity argument.  It is not a graph census: the
hypotheses are precisely the two cut-variance lower bounds and the parity
condition satisfied by the colour-incidence vector of a union of ordinary
defect components.
-/

namespace Erdos85

set_option maxHeartbeats 10000000

/-- Minimum possible sum of squares of `78` natural numbers having the given
sum.  The balanced sequence has `total % 78` entries one above the quotient. -/
def orderNineBalancedSquareSum (total : ℕ) : ℕ :=
  let a := total / 78
  let r := total % 78
  (78 - r) * a ^ 2 + r * (a + 1) ^ 2

/-- The cut-variance lower bound for an ordinary shore of order `s` and
three high-root incidence counts `b₁,b₂,b₃`. -/
def orderNineNearRegularCutLower (s b₁ b₂ b₃ : ℕ) : ℤ :=
  (orderNineBalancedSquareSum (9 * s - (b₁ + b₂ + b₃)) : ℤ) - s ^ 2 +
    (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1) : ℕ)

/-- Both a shore and its complement satisfy the necessary zero-boundary
cut-variance inequality. -/
def orderNineNearRegularComponentAdmissible (s b₁ b₂ b₃ : ℕ) : Prop :=
  orderNineNearRegularCutLower s b₁ b₂ b₃ ≤ 0 ∧
    orderNineNearRegularCutLower (78 - s) (10 - b₁) (10 - b₂) (10 - b₃) ≤ 0

instance (s b₁ b₂ b₃ : ℕ) :
    Decidable (orderNineNearRegularComponentAdmissible s b₁ b₂ b₃) := by
  unfold orderNineNearRegularComponentAdmissible
  infer_instance

/-- Exact finite classification of proper ordinary component orders allowed
by the two cut-variance inequalities and the defect-handshake parity law.

The colour vectors are retained in the hypotheses because the classification
is a necessary-condition calculation, not an assertion that any listed order
is realized by a graph. -/
theorem orderNine_nearRegular_proper_component_order_classification :
    ∀ (s : Fin 78) (b₁ b₂ b₃ : Fin 11),
      s.1 ≠ 0 →
      (b₁.1 + b₂.1 + b₃.1) % 2 = 0 →
      orderNineNearRegularComponentAdmissible s.1 b₁.1 b₂.1 b₃.1 →
      s.1 = 9 ∨ s.1 = 18 ∨ s.1 = 19 ∨ s.1 = 26 ∨ s.1 = 27 ∨
        s.1 = 35 ∨ s.1 = 43 ∨ s.1 = 51 ∨ s.1 = 52 ∨ s.1 = 59 ∨
        s.1 = 60 ∨ s.1 = 69 := by
  set_option maxHeartbeats 10000000 in
  set_option maxRecDepth 100000 in
    decide

/-- Decisive arithmetic consumer for connectivity: no proper order allowed by
the cut-variance classification is divisible by eight.  A non-owner component
in the pointwise bin ledger has order `5k+3k=8k`, so this is the numerical
contradiction used by the graph-level argument. -/
theorem orderNine_nearRegular_no_eight_dvd_proper_component_order :
    ∀ (s : Fin 78) (b₁ b₂ b₃ : Fin 11),
      s.1 ≠ 0 →
      (b₁.1 + b₂.1 + b₃.1) % 2 = 0 →
      orderNineNearRegularComponentAdmissible s.1 b₁.1 b₂.1 b₃.1 →
      s.1 % 8 ≠ 0 := by
  intro s b₁ b₂ b₃ hs hparity hadm
  have hclass := orderNine_nearRegular_proper_component_order_classification
    s b₁ b₂ b₃ hs hparity hadm
  rcases hclass with h | h | h | h | h | h | h | h | h | h | h | h <;>
    omega

/-- Divisibility-shaped form of the preceding finite terminal. -/
theorem orderNine_nearRegular_eight_not_dvd_proper_component_order
    (s : Fin 78) (b₁ b₂ b₃ : Fin 11)
    (hs : s.1 ≠ 0)
    (hparity : (b₁.1 + b₂.1 + b₃.1) % 2 = 0)
    (hadm : orderNineNearRegularComponentAdmissible s.1 b₁.1 b₂.1 b₃.1) :
    ¬ 8 ∣ s.1 := by
  intro hdvd
  exact orderNine_nearRegular_no_eight_dvd_proper_component_order
    s b₁ b₂ b₃ hs hparity hadm (Nat.mod_eq_zero_of_dvd hdvd)

#print axioms orderNine_nearRegular_proper_component_order_classification
#print axioms orderNine_nearRegular_no_eight_dvd_proper_component_order
#print axioms orderNine_nearRegular_eight_not_dvd_proper_component_order

end Erdos85
