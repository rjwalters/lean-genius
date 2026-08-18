import Proofs.Erdos85SquareTrace

/-!
# Fourier square expansion at a prime root

This file converts the scalar identity produced by the square trace branch
into the convolution Fourier identity consumed by
`Erdos85PrimeFourierConvolution`.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

/-- The multiplicative character of `ZMod p` associated to a primitive
`p`-th root. -/
def primitiveRootCharacter {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (x : ZMod p) : K :=
  let ζu : Kˣ := (hζ.isUnit NeZero.out).unit
  let hζu : IsPrimitiveRoot ζu p := hζ.isUnit_unit NeZero.out
  ((((hζu.zmodEquivZPowers x).toMul : Subgroup.zpowers ζu) : Kˣ) : K)

@[simp] theorem primitiveRootCharacter_zero
    {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    primitiveRootCharacter hζ 0 = 1 := by
  simp [primitiveRootCharacter]

@[simp] theorem primitiveRootCharacter_add
    {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (x y : ZMod p) :
    primitiveRootCharacter hζ (x + y) =
      primitiveRootCharacter hζ x * primitiveRootCharacter hζ y := by
  simp [primitiveRootCharacter]

@[simp] theorem primitiveRootCharacter_natCast
    {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (i : ℕ) :
    primitiveRootCharacter hζ (i : ZMod p) = ζ ^ i := by
  simp [primitiveRootCharacter]

theorem primitiveRootCharacter_eq_pow_val
    {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (x : ZMod p) :
    primitiveRootCharacter hζ x = ζ ^ x.val := by
  calc
    primitiveRootCharacter hζ x =
        primitiveRootCharacter hζ (x.val : ZMod p) :=
      congrArg (primitiveRootCharacter hζ) (ZMod.natCast_rightInverse x).symm
    _ = ζ ^ x.val := primitiveRootCharacter_natCast hζ x.val

theorem sum_translate_mul_primitiveRootCharacter
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (d : ZMod p → ℤ) (x : ZMod p) :
    (∑ t : ZMod p, (d (t - x) : K) * primitiveRootCharacter hζ t) =
      primitiveRootCharacter hζ x *
        ∑ y : ZMod p, (d y : K) * primitiveRootCharacter hζ y := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ ?_
  intro y
  simp only [Equiv.subRight_apply]
  have hchar := primitiveRootCharacter_add hζ x (y - x)
  have hsum : x + (y - x) = y := by abel
  rw [hsum] at hchar
  rw [hchar]
  ring

/-- Fourier transform turns cyclic convolution into multiplication. -/
theorem sum_cyclicConvolution_mul_primitiveRootCharacter
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c d : ZMod p → ℤ) :
    (∑ t : ZMod p,
        (cyclicConvolution c d t : K) * primitiveRootCharacter hζ t) =
      (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) *
        ∑ y : ZMod p, (d y : K) * primitiveRootCharacter hζ y := by
  simp only [cyclicConvolution, Int.cast_sum, Int.cast_mul]
  have hexpand :
      (∑ t : ZMod p, (∑ x : ZMod p,
          (c x : K) * (d (t - x) : K)) * primitiveRootCharacter hζ t) =
        ∑ t : ZMod p, ∑ x : ZMod p,
          ((c x : K) * (d (t - x) : K)) * primitiveRootCharacter hζ t := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_mul]
  rw [hexpand, Finset.sum_comm]
  calc
    (∑ x : ZMod p, ∑ t : ZMod p,
        ((c x : K) * (d (t - x) : K)) * primitiveRootCharacter hζ t) =
        ∑ x : ZMod p, (c x : K) *
          ∑ t : ZMod p,
            (d (t - x) : K) * primitiveRootCharacter hζ t := by
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t _
              ring
    _ = ∑ x : ZMod p, (c x : K) *
          (primitiveRootCharacter hζ x *
            ∑ y : ZMod p, (d y : K) * primitiveRootCharacter hζ y) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [sum_translate_mul_primitiveRootCharacter hζ d x]
    _ = (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) *
          ∑ y : ZMod p, (d y : K) * primitiveRootCharacter hζ y := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            ring

@[simp] theorem primitiveRootCharacter_one
    {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    primitiveRootCharacter hζ (1 : ZMod p) = ζ := by
  simpa using primitiveRootCharacter_natCast hζ 1

@[simp] theorem primitiveRootCharacter_neg_one
    {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    primitiveRootCharacter hζ (-1 : ZMod p) = ζ⁻¹ := by
  have hadd := primitiveRootCharacter_add hζ (-1 : ZMod p) 1
  simp only [neg_add_cancel, primitiveRootCharacter_zero,
    primitiveRootCharacter_one] at hadd
  exact eq_inv_of_mul_eq_one_left hadd.symm

/-- The three Fourier coefficients occurring in the square branch. -/
def squareFourierCorrection {p : ℕ} (u k : ℤ) (t : ZMod p) : ℤ :=
  (if t = 0 then u * u * k else 0) +
    (if t = 1 then -(u * u) else 0) +
      (if t = -1 then -(u * u) else 0)

theorem squareFourierCorrection_eq_zero_of_not_special
    {p : ℕ} (u k : ℤ) (t : ZMod p)
    (ht : t ∉ ({0, 1, -1} : Finset (ZMod p))) :
    squareFourierCorrection u k t = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  simp [squareFourierCorrection, ht.1, ht.2.1, ht.2.2]

theorem sum_squareFourierCorrection_mul_primitiveRootCharacter
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u k : ℤ) :
    (∑ t : ZMod p,
        (squareFourierCorrection u k t : K) *
          primitiveRootCharacter hζ t) =
      ((u * u : ℤ) : K) * ((k : K) - ζ - ζ⁻¹) := by
  simp only [squareFourierCorrection, Int.cast_add, add_mul,
    Finset.sum_add_distrib]
  simp
  ring

/-- A square-frequency identity produces the Fourier-zero relation with a
correction supported at `0`, `1`, and `-1`. -/
theorem sum_convolution_sub_squareCorrection_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c : ZMod p → ℤ) (u k : ℤ)
    (hsq :
      (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) *
          (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) =
        ((u * u : ℤ) : K) * ((k : K) - ζ - ζ⁻¹)) :
    (∑ t : ZMod p,
      ((cyclicConvolution c c t - squareFourierCorrection u k t : ℤ) : K) *
        primitiveRootCharacter hζ t) = 0 := by
  simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [sum_cyclicConvolution_mul_primitiveRootCharacter hζ c c,
    sum_squareFourierCorrection_mul_primitiveRootCharacter hζ u k,
    hsq, sub_self]

@[simp] theorem primitiveRootCharacter_finEquiv
    {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (i : Fin p) :
    primitiveRootCharacter hζ (ZMod.finEquiv p i) = ζ ^ i.val := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      change primitiveRootCharacter hζ i = ζ ^ i.val
      have hval : ZMod.val (show ZMod (n + 1) from i) = i.val := by
        rfl
      have hi := ZMod.natCast_zmod_val (show ZMod (n + 1) from i)
      rw [hval] at hi
      calc
        primitiveRootCharacter hζ i =
            primitiveRootCharacter hζ (i.val : ZMod (n + 1)) :=
          congrArg (primitiveRootCharacter hζ) hi.symm
        _ = ζ ^ i.val := primitiveRootCharacter_natCast hζ i.val

theorem fin_sum_convolution_sub_squareCorrection_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c : ZMod p → ℤ) (u k : ℤ)
    (hsq :
      (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) *
          (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) =
        ((u * u : ℤ) : K) * ((k : K) - ζ - ζ⁻¹)) :
    (∑ i : Fin p,
      (((cyclicConvolution c c (ZMod.finEquiv p i) -
        squareFourierCorrection u k (ZMod.finEquiv p i) : ℤ) : K) *
          ζ ^ i.val)) = 0 := by
  have hz := sum_convolution_sub_squareCorrection_eq_zero hζ c u k hsq
  calc
    (∑ i : Fin p,
      (((cyclicConvolution c c (ZMod.finEquiv p i) -
        squareFourierCorrection u k (ZMod.finEquiv p i) : ℤ) : K) *
          ζ ^ i.val)) =
        ∑ t : ZMod p,
          ((cyclicConvolution c c t - squareFourierCorrection u k t : ℤ) : K) *
            primitiveRootCharacter hζ t := by
              refine Fintype.sum_equiv (ZMod.finEquiv p) _ _ ?_
              intro i
              simp
    _ = 0 := hz

/-- The complete abstract square branch: the trace-derived scalar square
identity implies convolution constancy away from the five exceptional
residues used by the graph terminal. -/
theorem cyclicConvolution_anchor_constant_of_square_identity
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c : ZMod p → ℤ) (u k : ℤ) (a : ZMod p)
    (hsq :
      (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) *
          (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) =
        ((u * u : ℤ) : K) * ((k : K) - ζ - ζ⁻¹))
    (ha : a ∉ ({0, 1, -1} : Finset (ZMod p))) :
    ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution c c a = cyclicConvolution c c g := by
  apply cyclicConvolution_anchor_constant_of_prime_fourier_zero
    hp hζ c (squareFourierCorrection u k) a
  · exact squareFourierCorrection_eq_zero_of_not_special u k
  · exact fin_sum_convolution_sub_squareCorrection_eq_zero hζ c u k hsq
  · exact ha

/-- Square-trace branch in the form expected from the frequency-pair
operator.  Once its scalar is itself a square and its trace is twice the
anchor Fourier coefficient, convolution constancy follows automatically. -/
theorem cyclicConvolution_anchor_constant_of_frequencyPair_trace
    {K E : Type*} [Field K] [CharZero K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (T : E →ₗ[K] E) (s : K) (c : ZMod p → ℤ) (k : ℤ)
    (a : ZMod p) (hs : s ≠ 0)
    (hTsq : T * T = (s * s) • LinearMap.id)
    (heven : Even (Module.finrank K E))
    (htrace : LinearMap.trace K E T =
      2 * ∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x)
    (hscalar : s * s = (k : K) - ζ - ζ⁻¹)
    (ha : a ∉ ({0, 1, -1} : Finset (ZMod p))) :
    ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution c c a = cyclicConvolution c c g := by
  obtain ⟨u, hu⟩ :=
    LinearMap.exists_int_fourier_sq_eq_of_trace_eq_two_mul
      T s (∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x)
        hs hTsq heven htrace
  apply cyclicConvolution_anchor_constant_of_square_identity
    hp hζ c u k a
  · simpa [hscalar] using hu
  · exact ha

end

end Erdos85
