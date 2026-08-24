import Proofs.Erdos85OddSquareOrderNineNearRegularCutArithmetic

/-!
# Parametric near-regular cut arithmetic

This is the order-independent arithmetic layer behind the q=9 cut-variance
classifier.  Both the ordinary population and the high-root index type are
parameters, so the same interface can be used by the binary-q NONBIP lane.
-/

open scoped BigOperators

namespace Erdos85

/-- Minimum sum of squares of `n` natural numbers with prescribed total.
The definition is meaningful at `n = 0`, while the sharp bound below assumes
`0 < n`. -/
def nearRegularBalancedSquareSum (n total : ℕ) : ℕ :=
  let a := total / n
  let r := total % n
  (n - r) * a ^ 2 + r * (a + 1) ^ 2

/-- Parametric cut-variance lower expression.  `ordinaryCount` is the number
of ordinary vertices, `q` their ambient degree, and `b` records incidence
with each exceptional/high root. -/
def nearRegularCutLower {ι : Type*} [Fintype ι]
    (ordinaryCount q s : ℕ) (b : ι → ℕ) : ℤ :=
  (nearRegularBalancedSquareSum ordinaryCount
      (q * s - ∑ i, b i) : ℤ) - s ^ 2 +
    (∑ i, b i * (b i - 1) : ℕ)

private theorem nearRegular_balancedSquare_point (a x : ℕ) :
    ((2 * a + 1 : ℕ) : ℤ) * x ≤
      (x : ℤ) ^ 2 + (a : ℤ) * (a + 1) := by
  push_cast
  by_cases hle : x ≤ a
  · have hnonneg :
        0 ≤ ((a : ℤ) - x) * ((a : ℤ) + 1 - x) :=
      mul_nonneg (by exact_mod_cast Nat.zero_le (a - x)) (by omega)
    have hid :
        (x : ℤ) ^ 2 + (a : ℤ) * ((a : ℤ) + 1) -
            (2 * (a : ℤ) + 1) * x =
          ((a : ℤ) - x) * ((a : ℤ) + 1 - x) := by ring
    omega
  · have hnonneg :
        0 ≤ ((x : ℤ) - a) * ((x : ℤ) - (a + 1)) :=
      mul_nonneg (by omega) (by omega)
    have hid :
        (x : ℤ) ^ 2 + (a : ℤ) * ((a : ℤ) + 1) -
            (2 * (a : ℤ) + 1) * x =
          ((x : ℤ) - a) * ((x : ℤ) - ((a : ℤ) + 1)) := by ring
    omega

/-- Generic balanced-square bound for any positive finite population. -/
theorem nearRegularBalancedSquareSum_le_sum_sq
    {O : Type*} [Fintype O] [DecidableEq O]
    (n : ℕ) (hn : 0 < n) (hcard : Fintype.card O = n) (f : O → ℕ) :
    nearRegularBalancedSquareSum n (∑ x, f x) ≤ ∑ x, (f x) ^ 2 := by
  let M := ∑ x, f x
  let a := M / n
  let r := M % n
  have hM : M = n * a + r := by
    dsimp only [a, r]
    exact (Nat.div_add_mod M n).symm
  have hr : r < n := by
    dsimp only [r]
    exact Nat.mod_lt _ hn
  have hpoint : ∀ x : O,
      ((2 * a + 1 : ℕ) : ℤ) * f x ≤
        (f x : ℤ) ^ 2 + (a : ℤ) * (a + 1) :=
    fun x => nearRegular_balancedSquare_point a (f x)
  have hsum := Finset.sum_le_sum fun x (_hx : x ∈ Finset.univ) => hpoint x
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hcard, ← Finset.mul_sum] at hsum
  have hgoalZ :
      (nearRegularBalancedSquareSum n M : ℤ) ≤
        ((∑ x, (f x) ^ 2 : ℕ) : ℤ) := by
    rw [show nearRegularBalancedSquareSum n M =
        (n - r) * a ^ 2 + r * (a + 1) ^ 2 by rfl]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hr)]
    push_cast
    have hsumF : (∑ x, (f x : ℤ)) = (M : ℤ) := by simp [M]
    have hsumSq : (∑ x, (f x : ℤ) ^ 2) =
        ((∑ x, f x ^ 2 : ℕ) : ℤ) := by simp
    rw [hsumF, hsumSq] at hsum
    push_cast at hsum
    have hMZ : (M : ℤ) = n * (a : ℤ) + r := by exact_mod_cast hM
    have hid :
        ((n : ℤ) - r) * (a : ℤ) ^ 2 +
            (r : ℤ) * ((a : ℤ) + 1) ^ 2 +
            n * (a : ℤ) * ((a : ℤ) + 1) =
          (2 * (a : ℤ) + 1) * (M : ℤ) := by
      rw [hMZ]
      ring
    ring_nf at hsum hid ⊢
    linarith
  exact_mod_cast hgoalZ

/-- Parametric arbitrary-boundary moment bound `CutLower ≤ δ`. -/
theorem nearRegularCutLower_le_of_moments
    {O ι : Type*} [Fintype O] [DecidableEq O]
    [Fintype ι] [DecidableEq ι]
    (ordinaryCount q : ℕ) (hcount : 0 < ordinaryCount)
    (hcard : Fintype.card O = ordinaryCount)
    (f : O → ℕ) (s δ : ℕ) (b : ι → ℕ)
    (hsum : (∑ x, f x) = q * s - ∑ i, b i)
    (hsq : (∑ x, (f x) ^ 2) + (∑ i, b i * (b i - 1)) ≤
      s ^ 2 + δ) :
    nearRegularCutLower ordinaryCount q s b ≤ δ := by
  have hbal := nearRegularBalancedSquareSum_le_sum_sq
    ordinaryCount hcount hcard f
  rw [hsum] at hbal
  let c := ∑ i, b i * (b i - 1)
  have hnat : nearRegularBalancedSquareSum ordinaryCount
        (q * s - ∑ i, b i) + c ≤ s ^ 2 + δ :=
    (Nat.add_le_add_right hbal c).trans hsq
  have hnatZ :
      (nearRegularBalancedSquareSum ordinaryCount
        (q * s - ∑ i, b i) : ℤ) + (c : ℤ) ≤
        ((s ^ 2 + δ : ℕ) : ℤ) := by
    exact_mod_cast hnat
  unfold nearRegularCutLower
  dsimp only [c] at hnatZ
  push_cast at hnatZ ⊢
  ring_nf at hnatZ ⊢
  linarith

/-- Zero-boundary specialization of the parametric moment bound. -/
theorem nearRegularCutLower_nonpos_of_moments
    {O ι : Type*} [Fintype O] [DecidableEq O]
    [Fintype ι] [DecidableEq ι]
    (ordinaryCount q : ℕ) (hcount : 0 < ordinaryCount)
    (hcard : Fintype.card O = ordinaryCount)
    (f : O → ℕ) (s : ℕ) (b : ι → ℕ)
    (hsum : (∑ x, f x) = q * s - ∑ i, b i)
    (hsq : (∑ x, (f x) ^ 2) + (∑ i, b i * (b i - 1)) ≤ s ^ 2) :
    nearRegularCutLower ordinaryCount q s b ≤ 0 := by
  simpa using nearRegularCutLower_le_of_moments
    ordinaryCount q hcount hcard f s 0 b hsum (by simpa using hsq)

/-- The parametric balanced-square expression is definitionally the existing
q=9 expression when the ordinary population is 78. -/
theorem nearRegularBalancedSquareSum_orderNine (total : ℕ) :
    nearRegularBalancedSquareSum 78 total = orderNineBalancedSquareSum total :=
  rfl

/-- Compatibility with the existing q=9 three-high cut classifier. -/
theorem nearRegularCutLower_orderNine_threeHigh
    (s b₁ b₂ b₃ : ℕ) :
    nearRegularCutLower 78 9 s ![b₁, b₂, b₃] =
      orderNineNearRegularCutLower s b₁ b₂ b₃ := by
  simp [nearRegularCutLower, orderNineNearRegularCutLower,
    nearRegularBalancedSquareSum_orderNine, Fin.sum_univ_three]

#print axioms Erdos85.nearRegularBalancedSquareSum_le_sum_sq
#print axioms Erdos85.nearRegularCutLower_le_of_moments
#print axioms Erdos85.nearRegularCutLower_nonpos_of_moments
#print axioms Erdos85.nearRegularCutLower_orderNine_threeHigh

end Erdos85
