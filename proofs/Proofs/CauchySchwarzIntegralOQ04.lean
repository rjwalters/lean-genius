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

/-- **Saturation of the sharp Cauchy–Schwarz (Gram) bound — the minimum-uncertainty
    condition.**  For *nonzero* centred vectors `u, v`, the Gram inequality
    `inner_sq_le_gram` is an **equality**

      `(Re⟪u,v⟫)² + (Im⟪u,v⟫)² = ‖u‖²·‖v‖²`

    if and only if `u` and `v` are parallel, i.e. `v = r • u` for some scalar `r ≠ 0`.

    With `u = (A−⟨A⟩)ψ`, `v = (B−⟨B⟩)ψ` this is precisely the equality case of the
    Schrödinger uncertainty relation `schrodinger_uncertainty`: the states that
    saturate the bound are the **minimum-uncertainty** (generalized coherent /
    squeezed) states, characterized by the eigenvalue-type equation
    `(B−⟨B⟩)ψ = r·(A−⟨A⟩)ψ`.  The Robertson bound `robertson_uncertainty` alone is
    saturated by the further subclass with `r` purely imaginary (vanishing covariance
    `Re⟪u,v⟫ = 0`), the classic `(B−⟨B⟩)ψ = iλ(A−⟨A⟩)ψ` condition.

    This is the equality companion to `inner_sq_le_gram`, obtained from Mathlib's
    Cauchy–Schwarz equality case `norm_inner_eq_norm_iff` after squaring. -/
theorem gram_eq_iff_parallel {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    (RCLike.re (inner 𝕜 u v)) ^ 2 + (RCLike.im (inner 𝕜 u v)) ^ 2
      = ‖u‖ ^ 2 * ‖v‖ ^ 2 ↔ ∃ r : 𝕜, r ≠ 0 ∧ v = r • u := by
  rw [← norm_inner_eq_norm_iff hu hv]
  have hnormsq : (RCLike.re (inner 𝕜 u v)) ^ 2 + (RCLike.im (inner 𝕜 u v)) ^ 2
      = ‖inner 𝕜 u v‖ ^ 2 := by rw [RCLike.norm_sq_eq_def]; ring
  rw [hnormsq, show ‖u‖ ^ 2 * ‖v‖ ^ 2 = (‖u‖ * ‖v‖) ^ 2 from by ring]
  constructor
  · intro h
    have h0 : (‖inner 𝕜 u v‖ - ‖u‖ * ‖v‖) * (‖inner 𝕜 u v‖ + ‖u‖ * ‖v‖) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h0 with h1 | h2
    · linarith
    · have hn1 : 0 ≤ ‖inner 𝕜 u v‖ := norm_nonneg _
      have hn2 : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hz1 : ‖inner 𝕜 u v‖ = 0 := by linarith
      have hz2 : ‖u‖ * ‖v‖ = 0 := by linarith
      linarith
  · intro h; rw [h]

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

/-- **Schrödinger uncertainty principle (variance form).**  The Schrödinger analogue
of `heisenberg_variance_form`: instantiating `schrodinger_uncertainty` at the
expectation values `⟨A⟩ = Re⟪ψ,Aψ⟫`, `⟨B⟩ = Re⟪ψ,Bψ⟫` turns each right-hand factor
into a variance `Var_ψ(A) = ‖(A−⟨A⟩)ψ‖²`, `Var_ψ(B) = ‖(B−⟨B⟩)ψ‖²`, giving the
physically standard Schrödinger relation

  `Var_ψ(A)·Var_ψ(B) ≥ ¼·‖⟪ψ, (AB−BA)ψ⟫‖² + (Re⟪(A−⟨A⟩)ψ,(B−⟨B⟩)ψ⟫)²`,

whose covariance term reads in anticommutator form via
`re_inner_centred_eq_anticommutator` (at `a = ⟨A⟩`, `b = ⟨B⟩`, unit `ψ`) as the
symmetrized covariance `½⟪ψ,{A,B}ψ⟫ − ⟨A⟩⟨B⟩`.  Dropping that nonnegative term
recovers `heisenberg_variance_form`. -/
theorem schrodinger_variance_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + RCLike.re (inner 𝕜 (A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ)
            (B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ)) ^ 2
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2 :=
  schrodinger_uncertainty hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ)))

/-- **Anticommutator = symmetric part of the centred inner product.**  Dual to
`inner_commutator_eq_sub`.  For symmetric `A, B` and real shifts `a, b`, with
`u = (A−a)ψ`, `v = (B−b)ψ`,

  `⟪u,v⟫ + ⟪v,u⟫ = ⟪ψ,(AB+BA)ψ⟫ − 2b·⟪ψ,Aψ⟫ − 2a·⟪ψ,Bψ⟫ + 2ab·⟪ψ,ψ⟫`.

Unlike the commutator, the shifts do **not** cancel: the anticommutator
expectation is genuinely centred.  This is the identity that turns the
covariance term of `schrodinger_uncertainty` into the physical anticommutator
`½⟪ψ,{A,B}ψ⟫`. -/
theorem inner_anticommutator_eq_add {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)
        + inner 𝕜 (B ψ - (b : 𝕜) • ψ) (A ψ - (a : 𝕜) • ψ)
      = inner 𝕜 ψ (A (B ψ) + B (A ψ))
        - (↑(2 * b) : 𝕜) * inner 𝕜 ψ (A ψ)
        - (↑(2 * a) : 𝕜) * inner 𝕜 ψ (B ψ)
        + (↑(2 * a * b) : 𝕜) * inner 𝕜 ψ ψ := by
  have e1 : inner 𝕜 (A ψ) (B ψ) = inner 𝕜 ψ (A (B ψ)) := hA ψ (B ψ)
  have e2 : inner 𝕜 (B ψ) (A ψ) = inner 𝕜 ψ (B (A ψ)) := hB ψ (A ψ)
  have e3 : inner 𝕜 (A ψ) ψ = inner 𝕜 ψ (A ψ) := hA ψ ψ
  have e4 : inner 𝕜 (B ψ) ψ = inner 𝕜 ψ (B ψ) := hB ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_add_right, RCLike.conj_ofReal]
  rw [e1, e2, e3, e4]
  push_cast
  ring

/-- **Covariance in anticommutator form.**  Taking real parts of
`inner_anticommutator_eq_add` and using `⟪v,u⟫ = conj⟪u,v⟫` (so
`Re⟪v,u⟫ = Re⟪u,v⟫`) gives the physical covariance:

  `Re⟪(A−a)ψ,(B−b)ψ⟫ = ½·Re⟪ψ,(AB+BA)ψ⟫ − b·Re⟪ψ,Aψ⟫ − a·Re⟪ψ,Bψ⟫ + ab·Re⟪ψ,ψ⟫`.

At `a = ⟨A⟩ = Re⟪ψ,Aψ⟫`, `b = ⟨B⟩ = Re⟪ψ,Bψ⟫` and a unit state `‖ψ‖ = 1`, the
right-hand side is exactly the symmetrized covariance `½⟪ψ,{A,B}ψ⟫ − ⟨A⟩⟨B⟩`, so
the covariance term appearing in `schrodinger_uncertainty` reads directly in
anticommutator form. -/
theorem re_inner_centred_eq_anticommutator {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ))
      = (1 / 2 : ℝ) * RCLike.re (inner 𝕜 ψ (A (B ψ) + B (A ψ)))
        - b * RCLike.re (inner 𝕜 ψ (A ψ))
        - a * RCLike.re (inner 𝕜 ψ (B ψ))
        + a * b * RCLike.re (inner 𝕜 ψ ψ) := by
  have hAdd := inner_anticommutator_eq_add hA hB ψ a b
  have hre := congrArg RCLike.re hAdd
  rw [map_add, inner_re_symm (B ψ - (b : 𝕜) • ψ) (A ψ - (a : 𝕜) • ψ)] at hre
  simp only [map_add, map_sub, RCLike.re_ofReal_mul] at hre
  linarith [hre]

/-- **Robertson (Heisenberg) saturation — the minimum-uncertainty states.**  For
    *nonzero* centred vectors `u, v`, the Robertson/Heisenberg squared bound
    `im_inner_sq_le`

      `(Im⟪u,v⟫)² = ‖u‖²·‖v‖²`

    is attained **iff** the covariance vanishes (`Re⟪u,v⟫ = 0`) *and* `u, v` are
    parallel (`v = r • u`, `r ≠ 0`).  With `u = (A−⟨A⟩)ψ`, `v = (B−⟨B⟩)ψ` this is the
    exact equality case of the Heisenberg bound `Var(A)·Var(B) ≥ ¼|⟪ψ,[A,B]ψ⟫|²`:
    the saturating states are the parallel (`gram_eq_iff_parallel`) states with the
    additional purely-imaginary-ratio condition `Re⟪u,v⟫ = 0`, i.e. the classic
    `(B−⟨B⟩)ψ = iλ(A−⟨A⟩)ψ`.  This is the strict Robertson subclass of the wider
    Schrödinger minimum-uncertainty family (`gram_eq_iff_parallel`), formalizing the
    "`r` purely imaginary, vanishing covariance" remark there.

    Proof: from the sharp Gram bound `inner_sq_le_gram`, `(Im⟪u,v⟫)² = ‖u‖²‖v‖²`
    forces `(Re⟪u,v⟫)² ≤ 0`, hence `Re⟪u,v⟫ = 0`, and then the Gram bound is itself
    saturated, so `gram_eq_iff_parallel` applies. -/
theorem im_inner_sq_eq_iff_robertson_saturated {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    (RCLike.im (inner 𝕜 u v)) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2
      ↔ RCLike.re (inner 𝕜 u v) = 0 ∧ ∃ r : 𝕜, r ≠ 0 ∧ v = r • u := by
  constructor
  · intro h
    have hgram := inner_sq_le_gram (𝕜 := 𝕜) u v
    have hle : (RCLike.re (inner 𝕜 u v)) ^ 2 ≤ 0 := by nlinarith [hgram, h]
    have hre0 : RCLike.re (inner 𝕜 u v) = 0 := by
      by_contra hne
      have hpos : 0 < (RCLike.re (inner 𝕜 u v)) ^ 2 := by positivity
      linarith
    have hgeq : (RCLike.re (inner 𝕜 u v)) ^ 2 + (RCLike.im (inner 𝕜 u v)) ^ 2
        = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by rw [hre0]; simpa using h
    exact ⟨hre0, (gram_eq_iff_parallel hu hv).mp hgeq⟩
  · rintro ⟨hre0, hpar⟩
    have hgeq := (gram_eq_iff_parallel hu hv).mpr hpar
    rw [hre0] at hgeq
    simpa using hgeq

/-- **Incompatible observables cannot both be sharp.**  If the commutator expectation
`⟪ψ, (AB−BA)ψ⟫` is nonzero, then for *any* real shifts `a, b` both centred vectors are
nonzero: `(A−a)ψ ≠ 0` and `(B−b)ψ ≠ 0`.  Since `Var_ψ(A) = ‖(A−⟨A⟩)ψ‖²`, taking
`a = ⟨A⟩`, `b = ⟨B⟩` says a nonzero commutator forces **strictly positive** variance in
*both* observables — so `ψ` is an eigenvector of neither `A` nor `B` (after any shift),
i.e. observables with nonvanishing commutator expectation admit no common eigenstate.

    This is the qualitative (positivity) consequence of the Robertson bound
    `robertson_uncertainty`, complementary to its quantitative saturation
    characterization `im_inner_sq_eq_iff_robertson_saturated`: whenever the right-hand
    side lower bound `¼‖⟪ψ,[A,B]ψ⟫‖²` is positive, each factor of the variance product
    must be positive. -/
theorem centred_ne_zero_of_commutator_ne_zero {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ)
    (hcomm : inner 𝕜 ψ (A (B ψ) - B (A ψ)) ≠ 0) :
    A ψ - (a : 𝕜) • ψ ≠ 0 ∧ B ψ - (b : 𝕜) • ψ ≠ 0 := by
  have hrob := robertson_uncertainty hA hB ψ a b
  have hcpos : 0 < ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ := norm_pos_iff.mpr hcomm
  have hcsq : 0 < ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2 := pow_pos hcpos 2
  have hprodpos : 0 < ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
    linarith [hrob, hcsq]
  refine ⟨?_, ?_⟩
  · intro hu
    rw [hu, norm_zero, zero_pow (by norm_num), zero_mul] at hprodpos
    exact lt_irrefl 0 hprodpos
  · intro hv
    rw [hv, norm_zero, zero_pow (by norm_num), mul_zero] at hprodpos
    exact lt_irrefl 0 hprodpos

/-- **The Heisenberg bound is attained — explicit minimum-uncertainty witness.**  For
*any* nonzero `u` over a field with a genuine imaginary unit (`RCLike.I ≠ 0`, i.e. `ℂ`,
excluding the degenerate real case), the pair `(u, I • u)` **saturates** the squared
uncertainty inequality `im_inner_sq_le`:

    `(Im⟪u, I•u⟫)² = ‖u‖² · ‖I•u‖²`.

With `u = (A−⟨A⟩)ψ`, this is the canonical minimum-uncertainty (coherent / squeezed)
state condition `(B−⟨B⟩)ψ = i·(A−⟨A⟩)ψ` for which Heisenberg's `Var(A)·Var(B) ≥
¼|⟪ψ,[A,B]ψ⟫|²` holds with **equality**.  It is the constructive companion to the
qualitative characterization `im_inner_sq_eq_iff_robertson_saturated`: that lemma says
*which* states saturate; this exhibits one, proving the saturating set is nonempty and
hence that the bound `im_inner_sq_le` is **sharp** (its constant `1` cannot be lowered).

    Proof: verify the two saturation conditions of
    `im_inner_sq_eq_iff_robertson_saturated`.  Parallelism `I•u = I•u` is `rfl` with the
    nonzero ratio `r = I`; the vanishing covariance `Re⟪u, I•u⟫ = 0` is
    `inner_smul_right` then `RCLike.I_mul_re` (`re (I·z) = −im z`) with `inner_self_im`
    (`im⟪u,u⟫ = 0`). -/
theorem im_inner_I_smul_saturated (hI : (RCLike.I : 𝕜) ≠ 0) {u : E} (hu : u ≠ 0) :
    (RCLike.im (inner 𝕜 u ((RCLike.I : 𝕜) • u))) ^ 2
      = ‖u‖ ^ 2 * ‖(RCLike.I : 𝕜) • u‖ ^ 2 := by
  have hv : (RCLike.I : 𝕜) • u ≠ 0 := smul_ne_zero hI hu
  rw [im_inner_sq_eq_iff_robertson_saturated hu hv]
  refine ⟨?_, RCLike.I, hI, rfl⟩
  rw [inner_smul_right, RCLike.I_mul_re, inner_self_im, neg_zero]

/-- **Sharpness / attainability of the abstract Heisenberg inequality.**  Over a field
with a genuine imaginary unit (`RCLike.I ≠ 0`), for every nonzero `u` there **exists** a
nonzero `v` saturating `im_inner_sq_le`:

    `∃ v ≠ 0, (Im⟪u,v⟫)² = ‖u‖²·‖v‖²`.

Thus the uncertainty inequality `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²` — equivalently Heisenberg's
`Var(A)·Var(B) ≥ ¼|⟪ψ,[A,B]ψ⟫|²` — is **tight**: the bound is achieved, so it cannot be
strengthened.  The explicit witness is `v = I • u` (see `im_inner_I_smul_saturated`). -/
theorem exists_im_inner_sq_saturated (hI : (RCLike.I : 𝕜) ≠ 0) {u : E} (hu : u ≠ 0) :
    ∃ v : E, v ≠ 0 ∧ (RCLike.im (inner 𝕜 u v)) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 :=
  ⟨(RCLike.I : 𝕜) • u, smul_ne_zero hI hu, im_inner_I_smul_saturated hI hu⟩

/-- **Covariance of a parallel pair.**  For a scalar ratio `r` and vector `u`, the real
part of the inner product `⟪u, r•u⟫` (the "covariance" appearing in the Robertson
saturation condition) is exactly `Re(r)·‖u‖²`:

    `Re⟪u, r•u⟫ = Re(r) · ‖u‖²`.

Because `⟪u, r•u⟫ = r·⟪u,u⟫` with `⟪u,u⟫ = ‖u‖²` real, only the real part of `r`
survives.  This is the structural identity behind `im_inner_smul_saturated_iff`: the
covariance of `(u, r•u)` vanishes precisely when the ratio `r` is purely imaginary. -/
theorem re_inner_smul_self (r : 𝕜) (u : E) :
    RCLike.re (inner 𝕜 u (r • u)) = RCLike.re r * ‖u‖ ^ 2 := by
  rw [inner_smul_right, RCLike.mul_re, inner_self_im, mul_zero, sub_zero,
    inner_self_eq_norm_sq]

/-- **The parallel saturating states are exactly the purely-imaginary ratios.**  For
nonzero `u` and nonzero scalar `r`, the parallel pair `(u, r•u)` saturates the squared
uncertainty inequality `im_inner_sq_le`,

    `(Im⟪u, r•u⟫)² = ‖u‖²·‖r•u‖²`,

**iff** the ratio `r` is purely imaginary (`Re r = 0`).  This is the complete
characterization of the Heisenberg-saturating (minimum-uncertainty) states among all
parallel configurations, generalizing the single witness `im_inner_I_smul_saturated`
(the case `r = I`, `Re I = 0`) to the *entire* imaginary axis of ratios: with
`u = (A−⟨A⟩)ψ` these are precisely the states `(B−⟨B⟩)ψ = iλ(A−⟨A⟩)ψ`, `λ ∈ ℝ∖{0}`.

    Proof: through `im_inner_sq_eq_iff_robertson_saturated` the saturation reduces to
    the covariance condition `Re⟪u, r•u⟫ = 0`, and by `re_inner_smul_self` that equals
    `Re(r)·‖u‖²`, which (as `‖u‖² > 0`) vanishes iff `Re r = 0`. -/
theorem im_inner_smul_saturated_iff {u : E} (hu : u ≠ 0) {r : 𝕜} (hr : r ≠ 0) :
    (RCLike.im (inner 𝕜 u (r • u))) ^ 2 = ‖u‖ ^ 2 * ‖r • u‖ ^ 2
      ↔ RCLike.re r = 0 := by
  have hv : r • u ≠ 0 := smul_ne_zero hr hu
  have hupos : (0 : ℝ) < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
  rw [im_inner_sq_eq_iff_robertson_saturated hu hv]
  constructor
  · rintro ⟨hre, -⟩
    rw [re_inner_smul_self] at hre
    rcases mul_eq_zero.mp hre with h | h
    · exact h
    · exact absurd h hupos.ne'
  · intro hre
    exact ⟨by rw [re_inner_smul_self, hre, zero_mul], r, hr, rfl⟩

end CauchySchwarzIntegralOQ04

#print axioms CauchySchwarzIntegralOQ04.gram_eq_iff_parallel
