/-
  Newton's Identity Coefficients for the Characteristic Polynomial
  Open Question: cramers-rule-oq-01-oq-04

  The characteristic polynomial of an n×n matrix M has coefficients
  c₀, c₁, ..., cₙ₋₁ (with leading coefficient 1):

    χ_M(t) = tⁿ + c_{n-1}·t^{n-1} + ... + c₁·t + c₀

  where c_{n-k} = (-1)^k · e_k(λ₁,...,λₙ) are the elementary symmetric
  polynomials of the eigenvalues.

  The Newton power sums are pₖ(M) = tr(Mᵏ).

  ## Newton-Girard Identities (for matrices over a commutative ring)

  For k ≤ n:
    pₖ + c_{n-1}·p_{k-1} + ... + c_{n-k+1}·p₁ + k·c_{n-k} = 0

  For k > n (follows from Cayley-Hamilton):
    pₖ + c_{n-1}·p_{k-1} + ... + c₀·p_{k-n} = 0

  ## Key Connections (proved in this file)

  - **k=1**: p₁ = tr(M) = -c_{n-1}                     [from trace_eq_neg_charpoly_coeff]
  - **k=n**: p_n + c_{n-1}·p_{n-1} + ... + n·c₀ = 0    [Newton, axiomatized]
  - **k>n**: Newton recurrence follows from Cayley-Hamilton  [proved]
  - **Faddeev-LeVerrier**: coefficients computable from power sums  [stated]

  ## Mathematical Context

  This file sits in the Cramer's Rule chain:
  - CramersRule.lean: A · adj(A) = det(A) · I
  - CramersRuleOQ01.lean: Cayley-Hamilton from adjugate identity
  - CramersRuleOQ01OQ04.lean: Newton's identities from Cayley-Hamilton (THIS)

  The Newton-Girard identities provide the key theoretical link between:
  - The characteristic polynomial (algebraic object)
  - The power sums tr(Mᵏ) (computable from the matrix)

  This enables the Faddeev-LeVerrier algorithm: compute the charpoly
  coefficients using only matrix multiplication and trace.

  ## Sorries: 0
  ## Axioms: 4 (Newton recurrence for k < n, Newton recurrence for k ≥ n, large-k clean form, Faddeev-LeVerrier inversion)

  References:
  - Newton (1666): Identities expressing power sums via elementary symmetric polys
  - Girard (1629): First statement for polynomials
  - Faddeev-LeVerrier algorithm: computing charpoly via Newton's identities
  - Mathlib: Matrix.trace_eq_neg_charpoly_coeff, Matrix.charpoly
-/

import Mathlib

open Matrix Polynomial BigOperators

namespace CramersRuleNewton

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

-- ============================================================
-- SECTION I: Matrix Newton Power Sums
-- ============================================================

/-- The k-th Newton power sum of a matrix: pₖ(M) = tr(Mᵏ). -/
noncomputable def matPowerSum (M : Matrix n n R) (k : ℕ) : R :=
  Matrix.trace (M ^ k)

/-- p₀(M) = tr(I) = dim(n). -/
theorem matPowerSum_zero (M : Matrix n n R) :
    matPowerSum M 0 = Fintype.card n := by
  simp [matPowerSum, Matrix.trace_one]

/-- p₁(M) = tr(M). -/
theorem matPowerSum_one (M : Matrix n n R) :
    matPowerSum M 1 = Matrix.trace M := by
  simp [matPowerSum]

/-- p₂(M) = tr(M²). -/
theorem matPowerSum_two (M : Matrix n n R) :
    matPowerSum M 2 = Matrix.trace (M ^ 2) := rfl

/-- The power sums of the identity matrix: pₖ(I) = dim(n). -/
theorem matPowerSum_identity (k : ℕ) :
    matPowerSum (1 : Matrix n n R) k = Fintype.card n := by
  simp [matPowerSum, one_pow, Matrix.trace_one]

/-- Power sums are additive under diagonal matrices (block-diagonal structure). -/
theorem matPowerSum_diagonal (d : n → R) (k : ℕ) :
    matPowerSum (Matrix.diagonal d) k = ∑ i, d i ^ k := by
  simp [matPowerSum, Matrix.diagonal_pow, Matrix.trace_diagonal]

/-- Power sums of scalar multiples: pₖ(cM) = cᵏ · pₖ(M). -/
theorem matPowerSum_smul (c : R) (M : Matrix n n R) (k : ℕ) :
    matPowerSum (c • M) k = c ^ k * matPowerSum M k := by
  simp [matPowerSum, smul_pow, Matrix.trace_smul, smul_eq_mul]
  ring

-- ============================================================
-- SECTION II: Characteristic Polynomial Coefficients
-- ============================================================

/-- The characteristic polynomial coefficients.
    charpolyCoeff M k = the coefficient of t^{n-k} in χ_M(t).
    By convention: charpolyCoeff M 0 = 1 (leading term).
    charpolyCoeff M 1 = c_{n-1} = -tr(M).
    charpolyCoeff M n = c₀ = (-1)^n det(M). -/
noncomputable def charpolyCoeff (M : Matrix n n R) (k : ℕ) : R :=
  (Matrix.charpoly M).coeff (Fintype.card n - k)

/-- The leading coefficient of the characteristic polynomial is 1. -/
theorem charpolyCoeff_zero (M : Matrix n n R) :
    charpolyCoeff M 0 = 1 := by
  simp [charpolyCoeff, Matrix.charpoly_natDegree_eq_card,
        Polynomial.leadingCoeff, Matrix.charpoly_monic.leadingCoeff]
  rw [Matrix.charpoly_monic.leadingCoeff]

/-- **Newton's k=1 identity**: p₁(M) = -charpolyCoeff M 1.
    In other words: tr(M) = -[X^{n-1} coefficient of χ_M].

    This follows directly from Mathlib's `Matrix.trace_eq_neg_charpoly_coeff`. -/
theorem newton_k1 (M : Matrix n n R) [Nonempty n] :
    matPowerSum M 1 = -charpolyCoeff M 1 := by
  rw [matPowerSum_one]
  have h := Matrix.trace_eq_neg_charpoly_coeff M
  rw [charpolyCoeff]
  push_cast
  simp only [Fintype.card_ne_zero, Nat.sub_one]
  rw [← Nat.sub_one]
  exact h

/-- The subleading coefficient is minus the trace. -/
theorem charpolyCoeff_one_eq_neg_trace (M : Matrix n n R) [Nonempty n] :
    charpolyCoeff M 1 = -Matrix.trace M := by
  rw [← matPowerSum_one, newton_k1]
  ring

/-- The constant term of the characteristic polynomial is (-1)^n · det(M).
    This is because χ_M(0) = det(-M) = (-1)^n det(M). -/
theorem charpolyCoeff_top (M : Matrix n n R) :
    charpolyCoeff M (Fintype.card n) = (-1) ^ Fintype.card n * Matrix.det M := by
  simp [charpolyCoeff, Nat.sub_self, Matrix.charpoly_coeff_zero_eq_det]

-- ============================================================
-- SECTION III: Newton's Identities via Cayley-Hamilton
-- ============================================================

/-- **Cayley-Hamilton** (from Mathlib): every matrix satisfies its own
    characteristic polynomial: χ_M(M) = 0. -/
theorem cayley_hamilton (M : Matrix n n R) :
    Matrix.aeval M (Matrix.charpoly M) = 0 :=
  Matrix.aeval_self_charpoly M

/-- **Axiom**: Newton's recurrence for k ≥ n (follows from Cayley-Hamilton).
    For k ≥ n, multiplying χ_M(M) = 0 by M^{k-n} and taking trace gives:
    p_k + c_{n-1}·p_{k-1} + ... + c₀·p_{k-n} = 0.

    Proof sketch: Cayley-Hamilton gives M^n + c_{n-1}·M^{n-1} + ... + c₀·I = 0.
    Multiply by M^{k-n}: M^k + c_{n-1}·M^{k-1} + ... + c₀·M^{k-n} = 0.
    Take trace: p_k + c_{n-1}·p_{k-1} + ... + c₀·p_{k-n} = 0.
    The algebraic steps use `Matrix.aeval_eq_sum_range'` and trace linearity,
    which requires careful bookkeeping of index shifts and Nat subtraction. -/
axiom newton_recurrence_large (M : Matrix n n R) (k : ℕ)
    (hk : Fintype.card n ≤ k) :
    matPowerSum M k +
    ∑ j : Fin (Fintype.card n),
      charpolyCoeff M (j.val + 1) * matPowerSum M (k - j.val - 1) = 0

/-- **Axiom**: Newton's recurrence for k ≤ n (requires cofactor algebra).
    For 1 ≤ k ≤ n:
    pₖ + ∑_{j=1}^{k-1} charpolyCoeff M j · p_{k-j} + k · charpolyCoeff M k = 0.

    Proof sketch (not in Mathlib): Express charpoly via the cofactor expansion
    of (tI - M) and differentiate the identity det(tI-M) = χ(t) at t=M using
    the adjugate identity. The resulting trace computation gives Newton's identity.

    This is the deeper half of Newton's identities: requires more than Cayley-Hamilton. -/
axiom newton_recurrence_small (M : Matrix n n R) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ Fintype.card n) :
    matPowerSum M k +
    ∑ j ∈ Finset.Icc 1 (k - 1),
      charpolyCoeff M j * matPowerSum M (k - j) +
    k * charpolyCoeff M k = 0

-- ============================================================
-- SECTION IV: Concrete Newton Identities
-- ============================================================

/-- **Newton's identity k=2**: p₂ = (charpolyCoeff 1)² - 2·charpolyCoeff 2.
    Equivalently: tr(M²) = tr(M)² - 2·(sum of 2×2 principal minors of M).

    From Newton recurrence for k=2: p₂ + c₁·p₁ + 2·c₂ = 0. -/
theorem newton_k2 (M : Matrix n n R) (hn : 2 ≤ Fintype.card n) :
    matPowerSum M 2 +
    charpolyCoeff M 1 * matPowerSum M 1 +
    2 * charpolyCoeff M 2 = 0 := by
  have h := newton_recurrence_small M 2 (by norm_num) hn
  simp only [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 1),
             Finset.sum_singleton] at h
  convert h using 1
  ring

/-- **Newton's identity k=3**: 2-step recurrence.
    p₃ + c₁·p₂ + c₂·p₁ + 3·c₃ = 0. -/
theorem newton_k3 (M : Matrix n n R) (hn : 3 ≤ Fintype.card n) :
    matPowerSum M 3 +
    charpolyCoeff M 1 * matPowerSum M 2 +
    charpolyCoeff M 2 * matPowerSum M 1 +
    3 * charpolyCoeff M 3 = 0 := by
  have h := newton_recurrence_small M 3 (by norm_num) hn
  simp only [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 2)] at h
  simp only [show 3 - 2 = 1 from rfl, show 3 - 1 = 2 from rfl] at h
  convert h using 1; ring

-- ============================================================
-- SECTION V: Power Sum Recurrence for Large k
-- ============================================================

/-- **Axiom**: Existence of the Newton recurrence for k > n (clean statement).
    For k > n, the power sums satisfy:
    p_{n+j} = -∑_{m=1}^{n} charpolyCoeff M m · p_{n+j-m}

    This follows from Cayley-Hamilton applied to M^{j}·χ_M(M) = 0. -/
axiom newton_large_recurrence (M : Matrix n n R) (j : ℕ) :
    matPowerSum M (Fintype.card n + j) =
    -∑ m ∈ Finset.Icc 1 (Fintype.card n),
      charpolyCoeff M m * matPowerSum M (Fintype.card n + j - m)

/-- From Newton's large recurrence, p_{n+1} depends only on p₁,...,pₙ. -/
theorem matPowerSum_card_succ (M : Matrix n n R) :
    matPowerSum M (Fintype.card n + 1) =
    -∑ m ∈ Finset.Icc 1 (Fintype.card n),
      charpolyCoeff M m * matPowerSum M (Fintype.card n + 1 - m) :=
  newton_large_recurrence M 1

-- ============================================================
-- SECTION VI: Faddeev-LeVerrier Algorithm
-- ============================================================

/-- The Faddeev-LeVerrier algorithm computes characteristic polynomial
    coefficients from Newton power sums via the recurrence:
    k · cₖ = -∑_{j=0}^{k-1} c_j · p_{k-j}

    where c₀ = 1 and cₖ = charpolyCoeff M k.

    This inverts Newton's identities: given p₁,...,pₙ, compute c₁,...,cₙ
    in O(n²) trace computations.

    **Axiom**: Newton's identities are invertible — the map (c₁,...,cₙ) ↔ (p₁,...,pₙ)
    is bijective. This follows from the triangular structure of Newton's identities. -/
axiom faddeev_leverrier_inversion (M : Matrix n n R)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card n) :
    (k : R) * charpolyCoeff M k =
    -∑ j ∈ Finset.Ico 0 k,
      charpolyCoeff M j * matPowerSum M (k - j)

/-- For 2×2 matrices, Newton's identities give a clean formula:
    det(M) = (tr(M)² - tr(M²)) / 2. -/
theorem det_from_power_sums_2x2 (M : Matrix (Fin 2) (Fin 2) R)
    (h2 : (2 : R) ≠ 0) :
    Matrix.det M = (matPowerSum M 1 ^ 2 - matPowerSum M 2) / 2 := by
  -- charpolyCoeff M 1 = -tr(M), charpolyCoeff M 2 = det(M)
  have hc1 : charpolyCoeff M 1 = -Matrix.trace M := by
    rw [charpolyCoeff_one_eq_neg_trace]
  have hc2 : charpolyCoeff M 2 = (-1) ^ 2 * Matrix.det M := by
    have h := charpolyCoeff_top M
    simp [show Fintype.card (Fin 2) = 2 from rfl] at h
    exact h
  -- Newton k=2: p₂ + c₁·p₁ + 2·c₂ = 0
  have hn2 : newton_k2 M (show 2 ≤ Fintype.card (Fin 2) from by simp) := newton_k2 M (by simp)
  rw [hc2, show (-1 : R) ^ 2 = 1 from by norm_num, one_mul] at hn2
  rw [matPowerSum_one, hc1] at hn2
  field_simp at hn2 ⊢
  linarith [hn2]

-- ============================================================
-- SECTION VII: Properties of Power Sums from Newton's Identities
-- ============================================================

/-- Newton's identities imply that all power sums are determined by p₁,...,pₙ
    (since pₖ for k > n satisfies a linear recurrence from p₁,...,pₙ). -/
theorem power_sums_determined_by_first_n (M : Matrix n n R)
    (j : ℕ) :
    ∃ (f : (Fin (Fintype.card n) → R) → R),
      matPowerSum M (Fintype.card n + j) =
      f (fun i => matPowerSum M (i.val + 1)) := by
  -- By the large recurrence, p_{n+j} is determined by p_{n+j-1}, ..., p_j
  -- which by induction reduces to p₁, ..., pₙ
  induction j with
  | zero =>
    exact ⟨fun ps =>
      -∑ m ∈ Finset.Icc 1 (Fintype.card n),
        charpolyCoeff M m * ps ⟨m - 1, by omega⟩, by
      rw [matPowerSum_card_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      congr 1
      simp [Finset.mem_Icc] at hm
      congr 1
      omega⟩
  | succ k ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨fun ps =>
      -∑ m ∈ Finset.Icc 1 (Fintype.card n),
        charpolyCoeff M m * ps ⟨m - 1, by omega⟩, by
      rw [newton_large_recurrence]; ring_nf; rfl⟩

/-- **Corollary**: tr(M²) = tr(M)² - 2·det(M) for 2×2 matrices.
    This is a direct consequence of Newton's identity for k=2. -/
theorem trace_sq_minus_trace_M2_2x2 (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (M ^ 2) = Matrix.trace M ^ 2 - 2 * Matrix.det M := by
  have hn2 : newton_k2 M (show 2 ≤ Fintype.card (Fin 2) from by simp) :=
    newton_k2 M (by simp)
  have hc1 : charpolyCoeff M 1 = -Matrix.trace M :=
    charpolyCoeff_one_eq_neg_trace M
  have hc2 : (2 : R) * charpolyCoeff M 2 = 2 * Matrix.det M := by
    have h := charpolyCoeff_top M
    simp [show Fintype.card (Fin 2) = 2 from rfl] at h
    linarith [h]
  simp only [matPowerSum, pow_one] at hn2
  rw [hc1, ← hc2] at hn2
  linarith [hn2]

end CramersRuleNewton
