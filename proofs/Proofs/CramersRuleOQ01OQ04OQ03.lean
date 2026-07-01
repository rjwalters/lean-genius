/-
  The Faddeev-LeVerrier Matrix Recursion, and its Cayley-Hamilton Terminus
  Open Question: cramers-rule-oq-01-oq-04-oq-03

  The parent entry (cramers-rule-oq-01-oq-04) develops Newton's identities linking
  the power sums pₖ(M) = tr(Mᵏ) to the characteristic-polynomial coefficients, and
  *axiomatizes* the Faddeev-LeVerrier inversion (`faddeev_leverrier_inversion`), i.e.
  the scalar recursion  k·cₖ = -∑_{j<k} c_j · p_{k-j}  that recovers the coefficients
  from the traces.  Proving that scalar recursion in general is exactly Newton's
  identities, which the parent leaves as an assumption.

  This entry answers the parent's open question -- "extend to the Faddeev-LeVerrier
  algorithm as a recursive Lean function" -- by formalizing the **matrix** half of the
  algorithm and discharging it with **zero axioms**.  The Faddeev-LeVerrier auxiliary
  matrices are defined by the recursion

      M₀ = I,     Mₖ = A · Mₖ₋₁ + cₖ · I

  where cₖ = charCoeff A k is the coefficient of t^{n-k} in χ_A(t).  We prove:

    * `flAux_eq_sum` : the recursion has the Horner closed form
                       Mⱼ = ∑_{k=0}^{j} cₖ · A^{j-k};
    * `flAux_card_eq_aeval` / `flAux_card_eq_zero`
                     : the n-th auxiliary matrix is χ_A(A), which **vanishes** by
                       Cayley-Hamilton -- so the recursion terminates exactly as the
                       algorithm requires;
    * `flAux_terminal` : A · M_{n-1} + cₙ · I = 0, the last algorithmic step;
    * `flAux_penultimate_mul`
                     : A · ((-1)^{n+1} · M_{n-1}) = det(A) · I, identifying the
                       penultimate auxiliary matrix with the adjugate up to sign --
                       the direct bridge back to Cramer's rule (`Matrix.mul_adjugate`).

  Everything is stated for an arbitrary commutative ring `R` (with `Nontrivial R`,
  which merely excludes the zero ring).  The classical first step
  `flAux_one : M₁ = A - tr(A)·I` is recorded as a sanity check that the recursion is
  genuinely Faddeev-LeVerrier.

  What this does NOT do: it does not make the coefficients themselves computable from
  traces (that is the parent's axiomatized scalar recursion / Newton's identities).
  The contribution here is that the *matrix* recursion and its Cayley-Hamilton /
  adjugate consequences are fully verified, with no axioms, in full generality.

  ## Sorries: 0
  ## Axioms: 0 (beyond Lean/Mathlib foundations)

  References:
  - Faddeev, Sominskii (1949); LeVerrier (1840); Souriau (1948): the algorithm
  - Householder, "The Theory of Matrices in Numerical Analysis" (1964), §6
  - Mathlib: Matrix.aeval_self_charpoly (Cayley-Hamilton), Matrix.mul_adjugate
  - Parent: CramersRuleOQ01OQ04.lean (Newton's identities; FL inversion axiomatized)
-/

import Mathlib

open Matrix Polynomial BigOperators

namespace FaddeevLeVerrier

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

-- ============================================================
-- SECTION I: Characteristic-polynomial coefficients
-- ============================================================

/-- The characteristic-polynomial coefficient `cₖ`: the coefficient of `t^{n-k}`
    in `χ_M(t)`.  Convention `c₀ = 1` (leading term), `cₙ = (-1)ⁿ·det M`. -/
noncomputable def charCoeff (M : Matrix n n R) (k : ℕ) : R :=
  (Matrix.charpoly M).coeff (Fintype.card n - k)

/-- The leading coefficient is `1`. -/
theorem charCoeff_zero [Nontrivial R] (M : Matrix n n R) :
    charCoeff M 0 = 1 := by
  rw [charCoeff, Nat.sub_zero, ← Matrix.charpoly_natDegree_eq_dim M]
  exact M.charpoly_monic.coeff_natDegree

/-- The subleading coefficient is minus the trace: `c₁ = -tr(M)`. -/
theorem charCoeff_one [Nonempty n] (M : Matrix n n R) :
    charCoeff M 1 = -Matrix.trace M := by
  rw [charCoeff, Matrix.trace_eq_neg_charpoly_coeff M, neg_neg]

/-- The top coefficient is `(-1)ⁿ·det M`. -/
theorem charCoeff_top [Nontrivial R] (M : Matrix n n R) :
    charCoeff M (Fintype.card n) = (-1) ^ Fintype.card n * M.det := by
  rw [charCoeff, Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add,
      show Fintype.card n + Fintype.card n = 2 * Fintype.card n from by ring, pow_mul]
  simp

-- ============================================================
-- SECTION II: The Faddeev-LeVerrier auxiliary matrices
-- ============================================================

/-- The Faddeev-LeVerrier auxiliary matrices, defined by the algorithm's own recursion
    `M₀ = I`, `Mⱼ₊₁ = A · Mⱼ + cⱼ₊₁ · I`. -/
noncomputable def flAux (M : Matrix n n R) : ℕ → Matrix n n R
  | 0 => 1
  | (j + 1) => M * flAux M j + charCoeff M (j + 1) • 1

@[simp] theorem flAux_zero (M : Matrix n n R) : flAux M 0 = 1 := rfl

theorem flAux_succ (M : Matrix n n R) (j : ℕ) :
    flAux M (j + 1) = M * flAux M j + charCoeff M (j + 1) • 1 := rfl

/-- **Classical first step.** `M₁ = A - tr(A)·I`, confirming the recursion is
    genuinely the Faddeev-LeVerrier algorithm. -/
theorem flAux_one [Nonempty n] (M : Matrix n n R) :
    flAux M 1 = M - Matrix.trace M • (1 : Matrix n n R) := by
  show M * flAux M 0 + charCoeff M 1 • 1 = M - Matrix.trace M • 1
  rw [flAux_zero, mul_one, charCoeff_one, neg_smul, ← sub_eq_add_neg]

/-- **Horner closed form.** The auxiliary matrix is the Horner partial sum
    `Mⱼ = ∑_{k=0}^{j} cₖ · A^{j-k}` of the characteristic polynomial. -/
theorem flAux_eq_sum [Nontrivial R] (M : Matrix n n R) (j : ℕ) :
    flAux M j = ∑ k ∈ Finset.range (j + 1), charCoeff M k • M ^ (j - k) := by
  induction j with
  | zero =>
    simp [charCoeff_zero]
  | succ i ih =>
    rw [flAux_succ, ih, Finset.sum_range_succ _ (i + 1), Nat.sub_self, pow_zero,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [Algebra.mul_smul_comm, ← pow_succ', show i - k + 1 = i + 1 - k from by omega]

-- ============================================================
-- SECTION III: Termination via Cayley-Hamilton
-- ============================================================

/-- The `n`-th auxiliary matrix is exactly `χ_M(M)`, the characteristic polynomial
    evaluated at the matrix. -/
theorem flAux_card_eq_aeval [Nontrivial R] (M : Matrix n n R) :
    flAux M (Fintype.card n) = (Polynomial.aeval M) M.charpoly := by
  rw [flAux_eq_sum, Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim,
      ← Finset.sum_range_reflect (fun i => M.charpoly.coeff i • M ^ i) (Fintype.card n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [Nat.add_sub_cancel]
  rfl

/-- **Cayley-Hamilton terminus.** The `n`-th auxiliary matrix vanishes; this is what
    makes the algorithm terminate correctly. -/
theorem flAux_card_eq_zero [Nontrivial R] (M : Matrix n n R) :
    flAux M (Fintype.card n) = 0 := by
  rw [flAux_card_eq_aeval, Matrix.aeval_self_charpoly]

/-- **Final algorithmic step.** `A · M_{n-1} + cₙ · I = 0`. -/
theorem flAux_terminal [Nontrivial R] (M : Matrix n n R) (hn : 0 < Fintype.card n) :
    M * flAux M (Fintype.card n - 1) + charCoeff M (Fintype.card n) • (1 : Matrix n n R) = 0 := by
  have h := flAux_succ M (Fintype.card n - 1)
  rw [Nat.sub_add_cancel hn] at h
  rw [← h]
  exact flAux_card_eq_zero M

-- ============================================================
-- SECTION IV: The adjugate / Cramer's-rule bridge
-- ============================================================

/-- **Adjugate bridge.** The penultimate Faddeev-LeVerrier matrix is the adjugate up to
    the sign `(-1)^{n+1}`: it satisfies the defining adjugate identity
    `A · ((-1)^{n+1}·M_{n-1}) = det(A)·I` (compare `Matrix.mul_adjugate`).  This is the
    Faddeev-LeVerrier route to `A⁻¹ = ((-1)^{n+1}/det A)·M_{n-1}`, closing the loop with
    Cramer's rule. -/
theorem flAux_penultimate_mul [Nontrivial R] (M : Matrix n n R) (hn : 0 < Fintype.card n) :
    M * ((-1 : R) ^ (Fintype.card n + 1) • flAux M (Fintype.card n - 1))
      = M.det • (1 : Matrix n n R) := by
  have hA : M * flAux M (Fintype.card n - 1) = -(charCoeff M (Fintype.card n) • 1) :=
    eq_neg_of_add_eq_zero_left (flAux_terminal M hn)
  rw [Algebra.mul_smul_comm, hA, charCoeff_top, smul_neg, smul_smul, ← neg_smul]
  congr 1
  have hpow : ((-1 : R) ^ (Fintype.card n + 1)) * ((-1 : R) ^ Fintype.card n) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨Fintype.card n, by ring⟩
  rw [← mul_assoc, hpow]; ring

end FaddeevLeVerrier
