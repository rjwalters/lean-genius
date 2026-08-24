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

private theorem nearRegular_balancedSquare_point_eq_iff (a x : ℕ) :
    ((2 * a + 1 : ℕ) : ℤ) * x =
        (x : ℤ) ^ 2 + (a : ℤ) * (a + 1) ↔
      x = a ∨ x = a + 1 := by
  have hid :
      (x : ℤ) ^ 2 + (a : ℤ) * (a + 1) -
          ((2 * a + 1 : ℕ) : ℤ) * x =
        ((x : ℤ) - a) * ((x : ℤ) - (a + 1)) := by
    push_cast
    ring
  constructor
  · intro h
    have hz : ((x : ℤ) - a) * ((x : ℤ) - (a + 1)) = 0 := by
      rw [← hid, h]
      ring
    rcases mul_eq_zero.mp hz with hz | hz
    · left
      exact_mod_cast (sub_eq_zero.mp hz)
    · right
      exact_mod_cast (sub_eq_zero.mp hz)
  · rintro (rfl | rfl) <;> push_cast <;> ring

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

/-- Equality in the generic balanced-square bound forces every entry to one
of the two adjacent quotient values. -/
theorem nearRegularBalancedSquare_eq_pointwise
    {O : Type*} [Fintype O] [DecidableEq O]
    (n : ℕ) (hn : 0 < n) (hcard : Fintype.card O = n) (f : O → ℕ)
    (heq : nearRegularBalancedSquareSum n (∑ x, f x) =
      ∑ x, (f x) ^ 2) :
    ∀ x, f x = (∑ y, f y) / n ∨ f x = (∑ y, f y) / n + 1 := by
  let M := ∑ x, f x
  let a := M / n
  let r := M % n
  have hM : M = n * a + r := by
    dsimp only [a, r]
    exact (Nat.div_add_mod M n).symm
  have hr : r < n := by
    dsimp only [r]
    exact Nat.mod_lt _ hn
  have htotal :
      ∑ x, ((2 * a + 1 : ℕ) : ℤ) * f x =
        ∑ x, ((f x : ℤ) ^ 2 + (a : ℤ) * (a + 1)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [hcard, ← Finset.mul_sum]
    have hsumF : (∑ x, (f x : ℤ)) = (M : ℤ) := by simp [M]
    have hsumSq : (∑ x, (f x : ℤ) ^ 2) =
        ((∑ x, f x ^ 2 : ℕ) : ℤ) := by simp
    rw [hsumF, hsumSq, ← heq]
    have hbalancedCast : (nearRegularBalancedSquareSum n M : ℤ) =
        ((n : ℤ) - r) * (a : ℤ) ^ 2 +
          (r : ℤ) * ((a : ℤ) + 1) ^ 2 := by
      rw [show nearRegularBalancedSquareSum n M =
          (n - r) * a ^ 2 + r * (a + 1) ^ 2 by rfl]
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hr)]
      push_cast
      rfl
    rw [hbalancedCast]
    have hMZ : (M : ℤ) = n * (a : ℤ) + r := by exact_mod_cast hM
    rw [hMZ]
    push_cast
    ring
  intro x
  apply (nearRegular_balancedSquare_point_eq_iff a (f x)).mp
  have hle : ∀ y : O,
      ((2 * a + 1 : ℕ) : ℤ) * f y ≤
        (f y : ℤ) ^ 2 + (a : ℤ) * (a + 1) :=
    fun y => nearRegular_balancedSquare_point a (f y)
  by_contra hne
  have hlt : ((2 * a + 1 : ℕ) : ℤ) * f x <
      (f x : ℤ) ^ 2 + (a : ℤ) * (a + 1) :=
    lt_of_le_of_ne (hle x) hne
  have hsumlt := Finset.sum_lt_sum
    (s := (Finset.univ : Finset O))
    (fun y _ => hle y) ⟨x, Finset.mem_univ x, hlt⟩
  rw [htotal] at hsumlt
  exact lt_irrefl _ hsumlt

/-- In the equality case, the upper quotient occurs exactly `total % n`
times. -/
theorem nearRegularBalancedSquare_eq_upper_card
    {O : Type*} [Fintype O] [DecidableEq O]
    (n : ℕ) (hn : 0 < n) (hcard : Fintype.card O = n) (f : O → ℕ)
    (heq : nearRegularBalancedSquareSum n (∑ x, f x) =
      ∑ x, (f x) ^ 2) :
    (Finset.univ.filter fun x =>
      f x = (∑ y, f y) / n + 1).card = (∑ y, f y) % n := by
  let M := ∑ x, f x
  let a := M / n
  let r := M % n
  let Z := Finset.univ.filter fun x => f x = a + 1
  have hM : M = n * a + r := by
    dsimp only [a, r]
    exact (Nat.div_add_mod M n).symm
  have hpoint := nearRegularBalancedSquare_eq_pointwise n hn hcard f heq
  have hf : ∀ x, f x = a + if x ∈ Z then 1 else 0 := by
    intro x
    have hx := hpoint x
    by_cases hxZ : x ∈ Z
    · have hxUpper : f x = a + 1 := (Finset.mem_filter.mp hxZ).2
      simp [hxZ, hxUpper]
    · have hxNotUpper : f x ≠ a + 1 := by
        intro hxUpper
        exact hxZ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxUpper⟩)
      have hxLower : f x = a := hx.resolve_right hxNotUpper
      simp [hxZ, hxLower]
  have hsum : M = n * a + Z.card := by
    calc
      M = ∑ x, f x := rfl
      _ = ∑ x, (a + if x ∈ Z then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hf x
      _ = n * a + Z.card := by
        rw [Finset.sum_add_distrib]
        simp [hcard, mul_comm]
  change Z.card = r
  omega

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

/-- Attainment of the parametric cut lower bound forces equality in the
ordinary balanced-square estimate. -/
theorem nearRegularBalancedSquare_eq_of_cutLower_eq
    {O ι : Type*} [Fintype O] [DecidableEq O]
    [Fintype ι] [DecidableEq ι]
    (ordinaryCount q : ℕ) (f : O → ℕ) (s δ : ℕ) (b : ι → ℕ)
    (hsum : (∑ x, f x) = q * s - ∑ i, b i)
    (hsq : (∑ x, (f x) ^ 2) + (∑ i, b i * (b i - 1)) =
      s ^ 2 + δ)
    (hsharp : nearRegularCutLower ordinaryCount q s b = δ) :
    nearRegularBalancedSquareSum ordinaryCount (∑ x, f x) =
      ∑ x, (f x) ^ 2 := by
  let c := ∑ i, b i * (b i - 1)
  have hsharpZ := hsharp
  unfold nearRegularCutLower at hsharpZ
  have hbalZ :
      (nearRegularBalancedSquareSum ordinaryCount
        (q * s - ∑ i, b i) : ℤ) + (c : ℤ) =
        ((s ^ 2 + δ : ℕ) : ℤ) := by
    dsimp only [c]
    push_cast at hsharpZ ⊢
    linarith
  have hbal : nearRegularBalancedSquareSum ordinaryCount
        (q * s - ∑ i, b i) + c = s ^ 2 + δ := by
    exact_mod_cast hbalZ
  rw [← hsum] at hbal
  dsimp only [c] at hbal
  omega

/-- Complete generic sharp-cut consumer: the ordinary degrees take the two
balanced values, and the upper level has the quotient-remainder cardinality. -/
theorem nearRegular_partition_of_cutLower_eq
    {O ι : Type*} [Fintype O] [DecidableEq O]
    [Fintype ι] [DecidableEq ι]
    (ordinaryCount q : ℕ) (hcount : 0 < ordinaryCount)
    (hcard : Fintype.card O = ordinaryCount)
    (f : O → ℕ) (s δ : ℕ) (b : ι → ℕ)
    (hsum : (∑ x, f x) = q * s - ∑ i, b i)
    (hsq : (∑ x, (f x) ^ 2) + (∑ i, b i * (b i - 1)) =
      s ^ 2 + δ)
    (hsharp : nearRegularCutLower ordinaryCount q s b = δ) :
    (∀ x, f x = (∑ y, f y) / ordinaryCount ∨
      f x = (∑ y, f y) / ordinaryCount + 1) ∧
    (Finset.univ.filter fun x =>
      f x = (∑ y, f y) / ordinaryCount + 1).card =
        (∑ y, f y) % ordinaryCount := by
  have heq := nearRegularBalancedSquare_eq_of_cutLower_eq
    ordinaryCount q f s δ b hsum hsq hsharp
  exact ⟨nearRegularBalancedSquare_eq_pointwise
      ordinaryCount hcount hcard f heq,
    nearRegularBalancedSquare_eq_upper_card
      ordinaryCount hcount hcard f heq⟩

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
#print axioms Erdos85.nearRegularBalancedSquare_eq_pointwise
#print axioms Erdos85.nearRegularBalancedSquare_eq_upper_card
#print axioms Erdos85.nearRegularCutLower_le_of_moments
#print axioms Erdos85.nearRegularCutLower_nonpos_of_moments
#print axioms Erdos85.nearRegularBalancedSquare_eq_of_cutLower_eq
#print axioms Erdos85.nearRegular_partition_of_cutLower_eq
#print axioms Erdos85.nearRegularCutLower_orderNine_threeHigh

end Erdos85
