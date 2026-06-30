import Mathlib

/-
# Sylvester Interpolation via Frobenius Covariants

Follow-up to `CayleyHamiltonOQ02` (open question oq-02-oq-02).

The parent file `CayleyHamiltonOQ02` shows that *any* polynomial function of an `n×n`
matrix `A` reduces, via Cayley–Hamilton, to a polynomial of degree `< n` in `A`. When `A`
is **diagonalizable** that reduction takes a sharp, fully explicit form — *Sylvester's
interpolation formula*:

  f(A) = ∑_λ f(λ) · Z_λ,

where the sum runs over the distinct eigenvalues `λ` of `A`, and the matrices `Z_λ` are the
**Frobenius covariants** — the spectral projections onto the eigenspaces. They are intrinsic
to `A` (independent of `f`) and satisfy

  Z_λ² = Z_λ,    Z_λ Z_μ = 0 (λ ≠ μ),    ∑_λ Z_λ = I,    A Z_λ = λ Z_λ,

so `f(A)` is obtained by simply *re-weighting the fixed spectral projections by the scalars
`f(λ)`*. This is the matrix analogue of Lagrange interpolation and the algebraic core of the
holomorphic functional calculus on a diagonalizable operator.

## Formalization

We encode "diagonalizable" by the data of a similarity `A = U · diagonal d · V` with
`diagonal d` the eigenvalue list and `U`, `V` mutually inverse (`U V = V U = 1`). The
eigenvalue running over the sum is `μ ∈ Finset.univ.image d`, the set of distinct entries of
`d`. The Frobenius covariant attached to `μ` is

  `frobeniusCovariant U V d μ = U · diagonal (1 on the μ-positions) · V`,

i.e. `U` conjugates the coordinate projection `E_μ` onto the `μ`-eigenspace back to the
original basis. The functional calculus is `Polynomial.aeval` (matrix polynomial evaluation).

## Main results

* `aeval_conj`           : conjugation commutes with the functional calculus,
                           `aeval (U A V) p = U · aeval A p · V`.
* `aeval_diagonal`       : `aeval (diagonal d) p = diagonal (i ↦ p.eval (d i))`.
* `sylvester`            : **Sylvester's formula** `aeval (U D V) p = ∑_μ p.eval μ • Z_μ`.
* `frobenius_idem`       : `Z_μ² = Z_μ` (idempotent).
* `frobenius_orthogonal` : `Z_μ Z_ν = 0` for `μ ≠ ν`.
* `frobenius_complete`   : `∑_μ Z_μ = 1` (resolution of the identity).
* `frobenius_eigen`      : `A · Z_μ = μ • Z_μ` (each covariant projects onto the μ-eigenspace).

Everything is `sorry`-free and `axiom`-free (only the foundational
`propext`/`Classical.choice`/`Quot.sound`; no `Lean.ofReduceBool`).
-/

-- `DecidableEq 𝕜` is needed for the eigenvalue indicators / `Finset.image` from
-- `coordProj` onward; the early transport lemmas don't use it, which the section-var
-- linter would otherwise flag.
set_option linter.unusedSectionVars false

namespace CayleyHamiltonOQ02OQ02

open Matrix Polynomial Finset

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [CommRing 𝕜] [DecidableEq 𝕜]

/-! ## Conjugation commutes with the functional calculus -/

/-- Powers of a conjugate are conjugates of powers: `(U A V)^k = U Aᵏ V`, using only
`U V = V U = 1`. -/
theorem conj_pow (U V A : Matrix n n 𝕜) (hUV : U * V = 1) (hVU : V * U = 1) :
    ∀ k : ℕ, (U * A * V) ^ k = U * A ^ k * V
  | 0 => by simpa using hUV.symm
  | (k + 1) => by
      rw [pow_succ, conj_pow U V A hUV hVU k]
      calc U * A ^ k * V * (U * A * V)
          = U * A ^ k * (V * U) * A * V := by noncomm_ring
        _ = U * A ^ k * 1 * A * V := by rw [hVU]
        _ = U * (A ^ k * A) * V := by noncomm_ring
        _ = U * A ^ (k + 1) * V := by rw [pow_succ]

/-- **Conjugation commutes with `aeval`.** If `U V = V U = 1`, then the polynomial functional
calculus of a conjugate is the conjugate of the functional calculus:
`aeval (U A V) p = U · aeval A p · V`. -/
theorem aeval_conj (U V A : Matrix n n 𝕜) (hUV : U * V = 1) (hVU : V * U = 1) (p : 𝕜[X]) :
    aeval (U * A * V) p = U * aeval A p * V := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
      rw [aeval_monomial, aeval_monomial, conj_pow U V A hUV hVU k,
        ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

/-! ## The functional calculus on a diagonal matrix is diagonal -/

/-- `aeval` of a diagonal matrix evaluates entrywise:
`aeval (diagonal d) p = diagonal (i ↦ p.eval (d i))`. -/
theorem aeval_diagonal (d : n → 𝕜) (p : 𝕜[X]) :
    aeval (diagonal d) p = diagonal (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext i j
      by_cases h : i = j <;> simp [Matrix.add_apply, h, eval_add]
  | monomial k a =>
      rw [aeval_monomial, ← Algebra.smul_def, diagonal_pow, ← diagonal_smul]
      congr 1
      funext i
      simp [eval_monomial, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]

/-! ## Frobenius covariants (spectral projections) -/

/-- The coordinate projection onto the `μ`-eigenspace in the diagonal basis: the diagonal
indicator matrix with a `1` in each position `i` where `d i = μ`. -/
def coordProj (d : n → 𝕜) (μ : 𝕜) : Matrix n n 𝕜 :=
  diagonal (fun i => if d i = μ then 1 else 0)

/-- The **Frobenius covariant** of the diagonalizable matrix `A = U · diagonal d · V`
attached to the eigenvalue `μ`: the spectral projection onto the `μ`-eigenspace, expressed in
the original basis by conjugating the coordinate projection. -/
def frobeniusCovariant (U V : Matrix n n 𝕜) (d : n → 𝕜) (μ : 𝕜) : Matrix n n 𝕜 :=
  U * coordProj d μ * V

/-- The coordinate projections are idempotent in the diagonal basis. -/
theorem coordProj_mul_self (d : n → 𝕜) (μ : 𝕜) :
    coordProj d μ * coordProj d μ = coordProj d μ := by
  unfold coordProj
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : d i = μ <;> simp [h]

/-- The coordinate projections for distinct eigenvalues are orthogonal. -/
theorem coordProj_mul_other (d : n → 𝕜) {μ ν : 𝕜} (hμν : μ ≠ ν) :
    coordProj d μ * coordProj d ν = 0 := by
  unfold coordProj
  rw [diagonal_mul_diagonal]
  rw [show (fun i => (if d i = μ then (1 : 𝕜) else 0) * (if d i = ν then 1 else 0))
        = (fun _ => (0 : 𝕜)) from ?_, diagonal_zero]
  funext i
  by_cases hμ : d i = μ
  · have hν : d i ≠ ν := by rw [hμ]; exact hμν
    rw [if_pos hμ, if_neg hν, mul_zero]
  · rw [if_neg hμ, zero_mul]

/-- Multiplying the diagonal matrix by a coordinate projection scales it by the eigenvalue:
`diagonal d · E_μ = μ • E_μ`. -/
theorem diag_mul_coordProj (d : n → 𝕜) (μ : 𝕜) :
    diagonal d * coordProj d μ = μ • coordProj d μ := by
  unfold coordProj
  rw [diagonal_mul_diagonal, ← diagonal_smul]
  congr 1
  funext i
  by_cases h : d i = μ <;> simp [h, Pi.smul_apply, smul_eq_mul]

/-- **Spectral decomposition of a diagonal matrix.** For any scalar function `g`, the diagonal
matrix `diagonal (i ↦ g (d i))` is the `g`-weighted sum of the coordinate projections over the
distinct eigenvalues. The two instances we need are `g = p.eval` (Sylvester) and `g = 1`
(resolution of the identity). -/
theorem diagonal_eq_sum_coordProj (d : n → 𝕜) (g : 𝕜 → 𝕜) :
    diagonal (fun i => g (d i)) = ∑ μ ∈ Finset.univ.image d, g μ • coordProj d μ := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
    rw [Finset.sum_eq_single (d i)]
    · simp [coordProj, diagonal_apply_eq]
    · intro μ _ hne
      rw [Matrix.smul_apply, coordProj, diagonal_apply_eq, smul_eq_mul,
        if_neg (fun h : d i = μ => hne h.symm), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_image_of_mem d (Finset.mem_univ i)) hmem
  · rw [diagonal_apply_ne _ hij]
    refine (Finset.sum_eq_zero ?_).symm
    intro μ _
    rw [Matrix.smul_apply, coordProj, diagonal_apply_ne _ hij, smul_zero]

/-! ## Sylvester's interpolation formula -/

/-- **Sylvester's interpolation formula.** For a diagonalizable matrix `A = U · diagonal d · V`
(with `U V = V U = 1`) and any polynomial `p`, the matrix `p(A)` is the sum, over the distinct
eigenvalues `μ`, of `p.eval μ` times the Frobenius covariant `Z_μ`:

  `aeval (U · diagonal d · V) p = ∑_μ p.eval μ • frobeniusCovariant U V d μ`.

The covariants `Z_μ` do not depend on `p`: changing the function only re-weights the fixed
spectral projections. -/
theorem sylvester (U V : Matrix n n 𝕜) (hUV : U * V = 1) (hVU : V * U = 1)
    (d : n → 𝕜) (p : 𝕜[X]) :
    aeval (U * diagonal d * V) p
      = ∑ μ ∈ Finset.univ.image d, p.eval μ • frobeniusCovariant U V d μ := by
  rw [aeval_conj U V (diagonal d) hUV hVU, aeval_diagonal,
    diagonal_eq_sum_coordProj d (fun μ => p.eval μ), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc]
  rfl

/-! ## Properties of the Frobenius covariants -/

/-- Each Frobenius covariant is idempotent: `Z_μ² = Z_μ`. -/
theorem frobenius_idem (U V : Matrix n n 𝕜) (hVU : V * U = 1) (d : n → 𝕜) (μ : 𝕜) :
    frobeniusCovariant U V d μ * frobeniusCovariant U V d μ = frobeniusCovariant U V d μ := by
  unfold frobeniusCovariant
  calc U * coordProj d μ * V * (U * coordProj d μ * V)
      = U * coordProj d μ * (V * U) * coordProj d μ * V := by noncomm_ring
    _ = U * coordProj d μ * 1 * coordProj d μ * V := by rw [hVU]
    _ = U * (coordProj d μ * coordProj d μ) * V := by noncomm_ring
    _ = U * coordProj d μ * V := by rw [coordProj_mul_self]

/-- Frobenius covariants for distinct eigenvalues are orthogonal: `Z_μ Z_ν = 0`. -/
theorem frobenius_orthogonal (U V : Matrix n n 𝕜) (hVU : V * U = 1) (d : n → 𝕜)
    {μ ν : 𝕜} (hμν : μ ≠ ν) :
    frobeniusCovariant U V d μ * frobeniusCovariant U V d ν = 0 := by
  unfold frobeniusCovariant
  calc U * coordProj d μ * V * (U * coordProj d ν * V)
      = U * coordProj d μ * (V * U) * coordProj d ν * V := by noncomm_ring
    _ = U * coordProj d μ * 1 * coordProj d ν * V := by rw [hVU]
    _ = U * (coordProj d μ * coordProj d ν) * V := by noncomm_ring
    _ = U * 0 * V := by rw [coordProj_mul_other d hμν]
    _ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]

/-- The Frobenius covariants resolve the identity: `∑_μ Z_μ = 1`. -/
theorem frobenius_complete (U V : Matrix n n 𝕜) (hUV : U * V = 1) (d : n → 𝕜) :
    ∑ μ ∈ Finset.univ.image d, frobeniusCovariant U V d μ = 1 := by
  have hsum : ∑ μ ∈ Finset.univ.image d, coordProj d μ = 1 := by
    have h := diagonal_eq_sum_coordProj d (fun _ => (1 : 𝕜))
    simp only [one_smul] at h
    rw [← h]
    simp [diagonal_one]
  unfold frobeniusCovariant
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, Matrix.mul_one, hUV]

/-- **Eigen-projection.** Each Frobenius covariant projects onto the `μ`-eigenspace:
`A · Z_μ = μ • Z_μ` for `A = U · diagonal d · V`. -/
theorem frobenius_eigen (U V : Matrix n n 𝕜) (hVU : V * U = 1) (d : n → 𝕜) (μ : 𝕜) :
    (U * diagonal d * V) * frobeniusCovariant U V d μ = μ • frobeniusCovariant U V d μ := by
  unfold frobeniusCovariant
  calc U * diagonal d * V * (U * coordProj d μ * V)
      = U * diagonal d * (V * U) * coordProj d μ * V := by noncomm_ring
    _ = U * diagonal d * 1 * coordProj d μ * V := by rw [hVU]
    _ = U * (diagonal d * coordProj d μ) * V := by noncomm_ring
    _ = U * (μ • coordProj d μ) * V := by rw [diag_mul_coordProj]
    _ = μ • (U * coordProj d μ * V) := by rw [mul_smul_comm, smul_mul_assoc]

end CayleyHamiltonOQ02OQ02
