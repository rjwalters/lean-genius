/-
  Cauchy–Schwarz Integral — OQ-04: the Cauchy–Schwarz core of the uncertainty principle

  The gallery entry `CauchySchwarzIntegral` proves the L²/inner-product Cauchy–Schwarz
  inequality `|⟪f,g⟫| ≤ ‖f‖·‖g‖`.  Its OQ-04 asks for the **Heisenberg uncertainty
  principle**.  We formalize both the Cauchy–Schwarz core that drives it *and* the
  full operator-theoretic statement `Var_ψ(A)·Var_ψ(B) ≥ ¼|⟪ψ,[A,B]ψ⟫|²` for
  symmetric (self-adjoint) operators `A, B` over `ℝ` or `ℂ` (`robertson_uncertainty`),
  together with its variance-form specialization at the expectation values
  (`heisenberg_variance_form`).

  Writing `u = (A−⟨A⟩)ψ`, `v = (B−⟨B⟩)ψ`, the uncertainty product is
  `Var(A)·Var(B) = ‖u‖²·‖v‖²`, and the commutator term is `Im⟪u,v⟫`.  The
  inequality `Var(A)·Var(B) ≥ |Im⟪u,v⟫|²` is therefore *exactly*

      `|Im⟪u,v⟫| ≤ ‖u‖·‖v‖`     and its square     `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`,

  the Cauchy–Schwarz step of Heisenberg's proof, valid in any inner product space
  over `ℝ` or `ℂ` (for `ℝ` the imaginary part is `0` and the bound is trivial; the
  content is the `ℂ` case).

  * `abs_im_inner_le_norm_mul_norm` — `|Im⟪u,v⟫| ≤ ‖u‖·‖v‖`.
  * `im_inner_sq_le` — `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`.
  * `abs_re_inner_le_norm_mul_norm` / `re_inner_sq_le` — the real-part
    (anticommutator / Schrödinger) companions.
  * `inner_sq_le_gram` — the sharp Gram form
    `(Re⟪u,v⟫)² + (Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`, combining both parts.
  * `robertson_uncertainty` — `¼‖⟪ψ,[A,B]ψ⟫‖² ≤ ‖(A−a)ψ‖²·‖(B−b)ψ‖²`.
  * `schrodinger_uncertainty` — Schrödinger's sharpening, keeping the covariance term
    `¼‖⟪ψ,[A,B]ψ⟫‖² + (Re⟪u,v⟫)² ≤ ‖(A−a)ψ‖²·‖(B−b)ψ‖²` (via the Gram form).
  * `robertson_of_schrodinger` — Robertson recovered by dropping the covariance term.
  * `heisenberg_variance_form` — the same at `a = ⟨A⟩`, `b = ⟨B⟩` (variance form).

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Heisenberg (1927); Robertson (1929); Schrödinger (1930); the abstract
  uncertainty inequality, e.g. Reed–Simon, *Functional Analysis*, §VIII.
-/

import Mathlib

namespace CauchySchwarzIntegralOQ04

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Uncertainty-principle Cauchy–Schwarz core.**  The imaginary part of the inner
    product is bounded by the product of the norms: `|Im⟪u,v⟫| ≤ ‖u‖·‖v‖`.  With
    `u = (A−⟨A⟩)ψ` and `v = (B−⟨B⟩)ψ`, this is the inequality
    `√(Var A · Var B) ≥ |Im⟪u,v⟫|` underlying Heisenberg's bound. -/
theorem abs_im_inner_le_norm_mul_norm (u v : E) :
    |RCLike.im (inner 𝕜 u v)| ≤ ‖u‖ * ‖v‖ := by
  have h1 : |RCLike.im (inner 𝕜 u v)| ≤ ‖inner 𝕜 u v‖ := RCLike.abs_im_le_norm _
  have h2 : ‖inner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  exact h1.trans h2

/-- **Squared uncertainty inequality.**  `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²` — the product of
    the "variances" `‖u‖²`, `‖v‖²` dominates the squared commutator term. -/
theorem im_inner_sq_le (u v : E) :
    (RCLike.im (inner 𝕜 u v)) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := abs_im_inner_le_norm_mul_norm (𝕜 := 𝕜) u v
  nlinarith [h, abs_nonneg (RCLike.im (inner 𝕜 u v)),
    sq_abs (RCLike.im (inner 𝕜 u v)), norm_nonneg u, norm_nonneg v]

/-- **Real-part (Schrödinger) companion.**  Symmetric to `abs_im_inner_le_norm_mul_norm`:
    the *real* part of the inner product is also bounded by the product of the norms,
    `|Re⟪u,v⟫| ≤ ‖u‖·‖v‖`.  With `u = (A−⟨A⟩)ψ`, `v = (B−⟨B⟩)ψ` the real part is the
    *anticommutator* term `½⟪ψ,{A,B}ψ⟫ − ⟨A⟩⟨B⟩` that appears in the sharper
    Schrödinger uncertainty relation. -/
theorem abs_re_inner_le_norm_mul_norm (u v : E) :
    |RCLike.re (inner 𝕜 u v)| ≤ ‖u‖ * ‖v‖ :=
  (RCLike.abs_re_le_norm _).trans (norm_inner_le_norm u v)

/-- **Squared real-part inequality.**  `(Re⟪u,v⟫)² ≤ ‖u‖²·‖v‖²` — the anticommutator
    counterpart of `im_inner_sq_le`. -/
theorem re_inner_sq_le (u v : E) :
    (RCLike.re (inner 𝕜 u v)) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := abs_re_inner_le_norm_mul_norm (𝕜 := 𝕜) u v
  nlinarith [h, abs_nonneg (RCLike.re (inner 𝕜 u v)),
    sq_abs (RCLike.re (inner 𝕜 u v)), norm_nonneg u, norm_nonneg v]

/-- **Full Gram inequality (the sharp Cauchy–Schwarz).**  Both parts together are
    bounded: `(Re⟪u,v⟫)² + (Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`, i.e. `‖⟪u,v⟫‖² ≤ ‖u‖²·‖v‖²`.
    This is the two-dimensional Gram determinant refinement combining the
    commutator (`Im`, Heisenberg) and anticommutator (`Re`, Schrödinger) terms —
    strictly stronger than either `im_inner_sq_le` or `re_inner_sq_le` alone, and
    the form that yields the *Schrödinger* uncertainty relation. -/
theorem inner_sq_le_gram (u v : E) :
    (RCLike.re (inner 𝕜 u v)) ^ 2 + (RCLike.im (inner 𝕜 u v)) ^ 2
      ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have hnorm : ‖inner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hid : ‖inner 𝕜 u v‖ ^ 2
      = (RCLike.re (inner 𝕜 u v)) ^ 2 + (RCLike.im (inner 𝕜 u v)) ^ 2 := by
    rw [RCLike.norm_sq_eq_def]; ring
  have hsq : ‖inner 𝕜 u v‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    nlinarith [hnorm, norm_nonneg (inner 𝕜 u v),
      mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  rw [hid, mul_pow] at hsq
  exact hsq

/-! ## The full Robertson uncertainty relation

The lemmas above are the Cauchy–Schwarz core.  Here we assemble them into the
genuine operator-theoretic **Robertson uncertainty relation**

  `‖(A−a)ψ‖²·‖(B−b)ψ‖² ≥ ¼·‖⟪ψ, (AB−BA)ψ⟫‖²`,

for symmetric (self-adjoint) operators `A, B` on any inner product space over `ℝ`
or `ℂ`, any state `ψ`, and *any* real shifts `a, b`.  Taking `a = ⟪ψ,Aψ⟫`,
`b = ⟪ψ,Bψ⟫` (the expectation values) makes the left side `Var(A)·Var(B)`, so this
is exactly Heisenberg's `Δx·Δp ≥ ℏ/2` with `[x,p] = iℏ`.

The key algebraic fact is that the commutator expectation equals the antisymmetric
part of `⟪u,v⟫` for the centred vectors `u = (A−a)ψ`, `v = (B−b)ψ` — and, crucially,
is **independent of the shifts** `a, b` (they cancel by symmetry).  Combined with
`⟪v,u⟫ = conj⟪u,v⟫`, this makes `⟪ψ,[A,B]ψ⟫ = ⟪u,v⟫ − conj⟪u,v⟫ = 2·i·Im⟪u,v⟫`,
whose norm is `2·|Im⟪u,v⟫|`, and `im_inner_sq_le` finishes. -/

/-- **Commutator = antisymmetric part of the centred inner product.**  For symmetric
`A, B` and any real shifts `a, b`, with `u = (A−a)ψ`, `v = (B−b)ψ`,
`⟪ψ, (AB−BA)ψ⟫ = ⟪u,v⟫ − ⟪v,u⟫`.  The shifts cancel, so the commutator expectation
does not depend on the centring. -/
theorem inner_commutator_eq_sub {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    inner 𝕜 ψ (A (B ψ) - B (A ψ))
      = inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)
        - inner 𝕜 (B ψ - (b : 𝕜) • ψ) (A ψ - (a : 𝕜) • ψ) := by
  have e1 : inner 𝕜 (A ψ) (B ψ) = inner 𝕜 ψ (A (B ψ)) := hA ψ (B ψ)
  have e2 : inner 𝕜 (B ψ) (A ψ) = inner 𝕜 ψ (B (A ψ)) := hB ψ (A ψ)
  have e3 : inner 𝕜 (A ψ) ψ = inner 𝕜 ψ (A ψ) := hA ψ ψ
  have e4 : inner 𝕜 (B ψ) ψ = inner 𝕜 ψ (B ψ) := hB ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal]
  rw [e1, e2, e3, e4]
  ring

/-- **Robertson uncertainty relation.**  For symmetric operators `A, B`, any state
`ψ` and any real shifts `a, b`,
`¼·‖⟪ψ, (AB−BA)ψ⟫‖² ≤ ‖(A−a)ψ‖²·‖(B−b)ψ‖²`.  With `a = ⟪ψ,Aψ⟫`, `b = ⟪ψ,Bψ⟫` the
right-hand side is the product of variances `Var(A)·Var(B)`, giving the Heisenberg
uncertainty principle `Δx·Δp ≥ ℏ/2`. -/
theorem robertson_uncertainty {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  set u := A ψ - (a : 𝕜) • ψ with hu
  set v := B ψ - (b : 𝕜) • ψ with hv
  have hid : inner 𝕜 ψ (A (B ψ) - B (A ψ)) = inner 𝕜 u v - inner 𝕜 v u :=
    inner_commutator_eq_sub hA hB ψ a b
  have hconj : inner 𝕜 v u = (starRingEnd 𝕜) (inner 𝕜 u v) := (inner_conj_symm v u).symm
  have hInorm : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rcases eq_or_ne (RCLike.I : 𝕜) 0 with h | h
    · rw [h, norm_zero]; norm_num
    · rw [RCLike.norm_I_of_ne_zero h]
  have h2 : ‖(2 : 𝕜)‖ = 2 := RCLike.norm_two
  -- ‖⟪ψ,[A,B]ψ⟫‖ ≤ 2·|Im⟪u,v⟫|
  have hnb : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ≤ 2 * |RCLike.im (inner 𝕜 u v)| := by
    rw [hid, hconj, RCLike.sub_conj, norm_mul, norm_mul, RCLike.norm_ofReal, h2]
    nlinarith [hInorm, abs_nonneg (RCLike.im (inner 𝕜 u v))]
  have him := im_inner_sq_le (𝕜 := 𝕜) u v
  nlinarith [hnb, him, norm_nonneg (inner 𝕜 ψ (A (B ψ) - B (A ψ))),
    abs_nonneg (RCLike.im (inner 𝕜 u v)), sq_abs (RCLike.im (inner 𝕜 u v))]

/-- **Schrödinger uncertainty relation.**  A genuine strengthening of Robertson: the
right-hand side dominates the commutator term *together with* the symmetrized
covariance term `Re⟪(A−a)ψ, (B−b)ψ⟫`,

  `¼·‖⟪ψ,[A,B]ψ⟫‖² + (Re⟪(A−a)ψ,(B−b)ψ⟫)² ≤ ‖(A−a)ψ‖²·‖(B−b)ψ‖²`.

Robertson (`robertson_uncertainty`) is the special case obtained by dropping the
nonnegative `(Re…)²` covariance term.  At `a = ⟨A⟩`, `b = ⟨B⟩` the real part
`Re⟪uₐ,v_b⟫` is the covariance `½⟪ψ,{A,B}ψ⟫ − ⟨A⟩⟨B⟩`, so this is Schrödinger's
sharpening `Var(A)·Var(B) ≥ ¼|⟪[A,B]⟫|² + |Cov(A,B)|²` (Schrödinger 1930).

The proof keeps the *full* Gram bound `(Re⟪u,v⟫)² + (Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`
(`inner_sq_le_gram`) rather than discarding the real part, then bounds
`¼‖[A,B]‖² ≤ (Im⟪u,v⟫)²` exactly as in Robertson. -/
theorem schrodinger_uncertainty {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)) ^ 2
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  set u := A ψ - (a : 𝕜) • ψ with hu
  set v := B ψ - (b : 𝕜) • ψ with hv
  have hid : inner 𝕜 ψ (A (B ψ) - B (A ψ)) = inner 𝕜 u v - inner 𝕜 v u :=
    inner_commutator_eq_sub hA hB ψ a b
  have hconj : inner 𝕜 v u = (starRingEnd 𝕜) (inner 𝕜 u v) := (inner_conj_symm v u).symm
  have hInorm : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rcases eq_or_ne (RCLike.I : 𝕜) 0 with h | h
    · rw [h, norm_zero]; norm_num
    · rw [RCLike.norm_I_of_ne_zero h]
  have h2 : ‖(2 : 𝕜)‖ = 2 := RCLike.norm_two
  have hnb : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ≤ 2 * |RCLike.im (inner 𝕜 u v)| := by
    rw [hid, hconj, RCLike.sub_conj, norm_mul, norm_mul, RCLike.norm_ofReal, h2]
    nlinarith [hInorm, abs_nonneg (RCLike.im (inner 𝕜 u v))]
  have hgram := inner_sq_le_gram (𝕜 := 𝕜) u v
  nlinarith [hnb, hgram, norm_nonneg (inner 𝕜 ψ (A (B ψ) - B (A ψ))),
    abs_nonneg (RCLike.im (inner 𝕜 u v)), sq_abs (RCLike.im (inner 𝕜 u v))]

/-- **Robertson from Schrödinger.**  Dropping the nonnegative covariance term
`(Re⟪(A−a)ψ,(B−b)ψ⟫)²` in `schrodinger_uncertainty` recovers `robertson_uncertainty`,
confirming Schrödinger's relation is at least as strong. -/
theorem robertson_of_schrodinger {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  have h := schrodinger_uncertainty hA hB ψ a b
  nlinarith [h, sq_nonneg (RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)))]

/-- **Heisenberg uncertainty principle (variance form).**  The physically standard
statement: instantiating `robertson_uncertainty` at the expectation values
`⟨A⟩ = Re⟪ψ,Aψ⟫`, `⟨B⟩ = Re⟪ψ,Bψ⟫` makes each factor on the right the variance
`Var_ψ(A) = ‖(A−⟨A⟩)ψ‖²`, `Var_ψ(B) = ‖(B−⟨B⟩)ψ‖²`, so

  `Var_ψ(A)·Var_ψ(B) ≥ ¼·‖⟪ψ, (AB−BA)ψ⟫‖²`.

For a symmetric operator `⟪ψ,Aψ⟫` is real, so `Re⟪ψ,Aψ⟫` is the genuine
expectation value `⟨A⟩` and the centred vector `(A−⟨A⟩)ψ` is the fluctuation. -/
theorem heisenberg_variance_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2 :=
  robertson_uncertainty hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ)))

end CauchySchwarzIntegralOQ04
