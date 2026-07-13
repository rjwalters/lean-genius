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
  * `robertson_std_form` / `heisenberg_std_form` / `heisenberg_canonical_std` — the
    literal *standard-deviation* form `Δx·Δp ≥ ½‖⟪[A,B]⟫‖`, i.e. `Δx·Δp ≥ ℏ/2`,
    obtained by taking square roots of the (squared) variance bounds above.
  * `robertson_sum_form` / `heisenberg_sum_form` / `heisenberg_canonical_sum` — the
    additive form `Var(A) + Var(B) ≥ ‖⟪[A,B]⟫‖`, the AM–GM consequence of the
    product bound.
  * `L2_inner_eq_integral` and the `*_integral_inner_*_L2` family — the **L²
    specialization**: with `⟪f,g⟫ = ∫ conj(f)·g` on `α →₂[μ] ℂ`, the abstract core
    becomes the literal integral Cauchy–Schwarz `|⟪f,g⟫|² ≤ ‖f‖²·‖g‖²` named in
    OQ-04's problem statement, split into its Heisenberg (`Im ∫ conj(f)·g`) and
    Schrödinger (`Re ∫ conj(f)·g`) components.

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

/-- **Strict Gram inequality off the minimum-uncertainty locus.**  For nonzero centred
    vectors `u, v` that are *not* parallel (no `r ≠ 0` with `v = r • u`), the sharp
    Cauchy–Schwarz / Gram bound is **strict**:

      `(Re⟪u,v⟫)² + (Im⟪u,v⟫)² < ‖u‖²·‖v‖²`.

    This is the `<`-completion of the `≤` bound `inner_sq_le_gram` and its `=`-case
    `gram_eq_iff_parallel`: equality holds *exactly* on the parallel (minimum-uncertainty)
    states, so anywhere off that locus the inequality is strict.  With
    `u = (A−⟨A⟩)ψ`, `v = (B−⟨B⟩)ψ` it says the Schrödinger uncertainty bound is strictly
    positive unless `ψ` is a generalized coherent/squeezed state
    `(B−⟨B⟩)ψ = r·(A−⟨A⟩)ψ`. -/
theorem inner_sq_lt_gram_of_not_parallel {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hpar : ¬ ∃ r : 𝕜, r ≠ 0 ∧ v = r • u) :
    (RCLike.re (inner 𝕜 u v)) ^ 2 + (RCLike.im (inner 𝕜 u v)) ^ 2
      < ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rcases lt_or_eq_of_le (inner_sq_le_gram (𝕜 := 𝕜) u v) with h | h
  · exact h
  · exact absurd ((gram_eq_iff_parallel hu hv).mp h) hpar

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

/-- **Robertson relation under a canonical commutation relation.**  Suppose the
commutator acts on the state `ψ` as a scalar, `(AB − BA)ψ = c • ψ` for some
`c ∈ 𝕜` — the abstract form of the canonical commutation relation `[x, p] = iℏ`.
Then the commutator expectation is `⟪ψ, (AB−BA)ψ⟫ = c‖ψ‖²`, so `robertson_uncertainty`
becomes the *scalar* lower bound

    `¼‖c‖²·‖ψ‖⁴ ≤ ‖(A−a)ψ‖²·‖(B−b)ψ‖²`,

independent of the operators' finer structure: the product of the (uncentred, then
centred) fluctuations is bounded below purely by the size of the commutator scalar.
This is the step that turns the operator inequality into the physical Heisenberg
bound `Δx·Δp ≥ ℏ/2`. -/
theorem robertson_canonical {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) (c : 𝕜)
    (hc : A (B ψ) - B (A ψ) = c • ψ) :
    ‖c‖ ^ 2 / 4 * ‖ψ‖ ^ 4
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  have hnorm : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ = ‖c‖ * ‖ψ‖ ^ 2 := by
    rw [hc, inner_smul_right, norm_mul, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg ψ)]
  have hrob := robertson_uncertainty hA hB ψ a b
  rw [hnorm] at hrob
  have hgoal : ‖c‖ ^ 2 / 4 * ‖ψ‖ ^ 4 = (1 / 4 : ℝ) * (‖c‖ * ‖ψ‖ ^ 2) ^ 2 := by ring
  rw [hgoal]
  exact hrob

/-- **Heisenberg uncertainty principle for a unit state under a canonical commutation
relation.**  Specializing `robertson_canonical` to a normalized state `‖ψ‖ = 1` and
the expectation-value shifts `a = ⟨A⟩ = Re⟪ψ,Aψ⟫`, `b = ⟨B⟩ = Re⟪ψ,Bψ⟫` makes the
right-hand side the product of variances `Var_ψ(A)·Var_ψ(B)` and collapses the
`‖ψ‖⁴` factor to `1`, giving the sharp scalar bound

    `¼‖c‖² ≤ Var_ψ(A)·Var_ψ(B)`.

For the canonical pair `[A, B]ψ = iℏ ψ` (so `‖c‖ = ℏ`) this is exactly
`Var_ψ(A)·Var_ψ(B) ≥ ℏ²/4`, i.e. `Δx·Δp ≥ ℏ/2`. -/
theorem heisenberg_canonical {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (hψ : ‖ψ‖ = 1) (c : 𝕜)
    (hc : A (B ψ) - B (A ψ) = c • ψ) :
    ‖c‖ ^ 2 / 4
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2 := by
  have h := robertson_canonical hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ))) c hc
  rwa [hψ, one_pow, mul_one] at h

/-! ## The literal `Δx·Δp ≥ ℏ/2` (product-of-standard-deviations form)

All the results above are stated in the **squared / variance** form
`Var(A)·Var(B) ≥ ¼‖⟪ψ,[A,B]ψ⟫‖²`.  The Heisenberg principle is more often written in
its **standard-deviation** form `Δx·Δp ≥ ℏ/2`, i.e. with the square roots taken:

  `‖(A−a)ψ‖·‖(B−b)ψ‖ ≥ ½·‖⟪ψ,[A,B]ψ⟫‖`.

Since both sides are nonnegative, this is *equivalent* to `robertson_uncertainty`,
obtained by taking `Real.sqrt` of both sides (`Real.sqrt_sq` on the nonnegative
squared quantities).  We record it explicitly because it is the form that appears
in physics texts and that the OQ-04 prompt literally asks for. -/

/-- **Robertson uncertainty relation, standard-deviation form.**  The un-squared
`Δx·Δp ≥ ½|⟪[A,B]⟫|`: for symmetric `A, B`, any state `ψ` and any real shifts `a, b`,

  `½·‖⟪ψ, (AB−BA)ψ⟫‖ ≤ ‖(A−a)ψ‖·‖(B−b)ψ‖`.

This is `robertson_uncertainty` with the square roots taken (both sides are
nonnegative), the physically standard `Δx·Δp ≥ ℏ/2` shape. -/
theorem robertson_std_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    (1 / 2 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖ := by
  have hrob := robertson_uncertainty hA hB ψ a b
  have hl : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ := by positivity
  have hr : (0 : ℝ) ≤ ‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have key : ((1 / 2 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖) ^ 2
      ≤ (‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖) ^ 2 := by
    nlinarith [hrob]
  calc (1 / 2 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖
      = Real.sqrt (((1 / 2 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖) ^ 2) :=
        (Real.sqrt_sq hl).symm
    _ ≤ Real.sqrt ((‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = ‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖ := Real.sqrt_sq hr

/-- **Heisenberg uncertainty principle, standard-deviation form.**  Instantiating
`robertson_std_form` at the expectation values `⟨A⟩ = Re⟪ψ,Aψ⟫`, `⟨B⟩ = Re⟪ψ,Bψ⟫`
makes each factor the standard deviation `Δ_ψ A = ‖(A−⟨A⟩)ψ‖`, `Δ_ψ B = ‖(B−⟨B⟩)ψ‖`,
giving the physically standard

  `Δ_ψ(A)·Δ_ψ(B) ≥ ½·‖⟪ψ, (AB−BA)ψ⟫‖`. -/
theorem heisenberg_std_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    (1 / 2 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖
        * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ :=
  robertson_std_form hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ)))

/-- **The literal `Δx·Δp ≥ ℏ/2`.**  For a normalized state `‖ψ‖ = 1` obeying a canonical
commutation relation `(AB − BA)ψ = c • ψ` (abstractly `[x, p] = iℏ`, so `‖c‖ = ℏ`), the
product of standard deviations is bounded below by `½‖c‖`:

  `Δ_ψ(A)·Δ_ψ(B) ≥ ½‖c‖`.

For `‖c‖ = ℏ` this is exactly Heisenberg's `Δx·Δp ≥ ℏ/2` — the un-squared form of
`heisenberg_canonical`, obtained from `robertson_std_form` since the commutator
expectation is `⟪ψ, (AB−BA)ψ⟫ = c‖ψ‖² = c`. -/
theorem heisenberg_canonical_std {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (hψ : ‖ψ‖ = 1) (c : 𝕜)
    (hc : A (B ψ) - B (A ψ) = c • ψ) :
    ‖c‖ / 2
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖
        * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ := by
  have h := heisenberg_std_form hA hB ψ
  have hnorm : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ = ‖c‖ := by
    rw [hc, inner_smul_right, norm_mul, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg ψ), hψ, one_pow, mul_one]
  rw [hnorm] at h
  linarith [h]

/-- **Schrödinger uncertainty principle, standard-deviation form.**  The Schrödinger
analogue of `robertson_std_form`: taking square roots of the (nonnegative) two sides of
`schrodinger_uncertainty` — whose right side `‖(A−a)ψ‖²·‖(B−b)ψ‖²` is the square of the
product of standard deviations — gives the tighter-than-Heisenberg bound

  `√(¼‖⟪ψ,[A,B]ψ⟫‖² + (Re⟪(A−a)ψ,(B−b)ψ⟫)²) ≤ ‖(A−a)ψ‖·‖(B−b)ψ‖`.

Dropping the covariance term under the root recovers `robertson_std_form`. -/
theorem schrodinger_std_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    Real.sqrt ((1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)) ^ 2)
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖ := by
  have hsch := schrodinger_uncertainty hA hB ψ a b
  have hr : (0 : ℝ) ≤ ‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [show ‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖
        = Real.sqrt ((‖A ψ - (a : 𝕜) • ψ‖ * ‖B ψ - (b : 𝕜) • ψ‖) ^ 2) from
      (Real.sqrt_sq hr).symm]
  apply Real.sqrt_le_sqrt
  rw [mul_pow]
  exact hsch

/-- **Schrödinger uncertainty principle, standard-deviation form at the expectation
values.**  Instantiating `schrodinger_std_form` at `⟨A⟩ = Re⟪ψ,Aψ⟫`, `⟨B⟩ = Re⟪ψ,Bψ⟫`
turns each right-hand factor into a standard deviation, giving Schrödinger's sharpening of
`heisenberg_std_form`:

  `√(¼‖⟪ψ,[A,B]ψ⟫‖² + Cov_ψ(A,B)²) ≤ Δ_ψ(A)·Δ_ψ(B)`,

with `Cov_ψ(A,B) = Re⟪(A−⟨A⟩)ψ,(B−⟨B⟩)ψ⟫`.  The square-root companion of
`schrodinger_variance_form`, and the Schrödinger counterpart of `heisenberg_std_form`. -/
theorem schrodinger_std_variance_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    Real.sqrt ((1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + RCLike.re (inner 𝕜 (A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ)
            (B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ)) ^ 2)
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖
        * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ :=
  schrodinger_std_form hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ)))

/-! ## The additive (sum) uncertainty relation `Var(A) + Var(B) ≥ ‖⟪ψ,[A,B]ψ⟫‖`

All the forms above are *multiplicative*: they bound the **product** of the
variances (or of the standard deviations).  A genuinely distinct, weaker-but-often
handier consequence is the **sum** (additive) uncertainty relation

  `‖(A−a)ψ‖² + ‖(B−b)ψ‖² ≥ ‖⟪ψ, (AB−BA)ψ⟫‖`,

i.e. `Var(A) + Var(B) ≥ ‖⟪[A,B]⟫‖` at the expectation values.  It follows from the
product form by AM–GM: `‖u‖² + ‖v‖² ≥ 2‖u‖·‖v‖ ≥ ‖⟪ψ,[A,B]ψ⟫‖`, the last step being
the standard-deviation bound `robertson_std_form`.  Unlike the product relation the
right-hand side is *linear* in the commutator norm (no square root), and the bound is
non-vacuous even when one variance is small provided the other compensates additively;
it underlies sum-form / state-independent uncertainty discussions. -/

/-- **Robertson uncertainty relation, additive (sum) form.**  For symmetric `A, B`,
any state `ψ` and any real shifts `a, b`, the *sum* of the squared centred norms
dominates the commutator norm:

  `‖⟪ψ, (AB−BA)ψ⟫‖ ≤ ‖(A−a)ψ‖² + ‖(B−b)ψ‖²`.

This is the additive counterpart of the multiplicative `robertson_uncertainty`,
obtained from the standard-deviation form `robertson_std_form` by AM–GM
`2‖u‖‖v‖ ≤ ‖u‖² + ‖v‖²`. -/
theorem robertson_sum_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 + ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  have hstd := robertson_std_form hA hB ψ a b
  nlinarith [hstd, sq_nonneg (‖A ψ - (a : 𝕜) • ψ‖ - ‖B ψ - (b : 𝕜) • ψ‖),
    norm_nonneg (inner 𝕜 ψ (A (B ψ) - B (A ψ)))]

/-- **Heisenberg uncertainty principle, additive (sum) form.**  Instantiating
`robertson_sum_form` at the expectation values `⟨A⟩ = Re⟪ψ,Aψ⟫`, `⟨B⟩ = Re⟪ψ,Bψ⟫`
makes each summand a variance, giving

  `Var_ψ(A) + Var_ψ(B) ≥ ‖⟪ψ, (AB−BA)ψ⟫‖`. -/
theorem heisenberg_sum_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        + ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2 :=
  robertson_sum_form hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ)))

/-- **Additive Heisenberg bound under a canonical commutation relation.**  For a
normalized state `‖ψ‖ = 1` obeying `(AB − BA)ψ = c • ψ` (abstractly `[x, p] = iℏ`,
so `‖c‖ = ℏ`), the sum of variances is bounded below by the commutator scalar:

  `Var_ψ(A) + Var_ψ(B) ≥ ‖c‖`.

The additive companion of `heisenberg_canonical`; for `‖c‖ = ℏ` it reads
`Var(A) + Var(B) ≥ ℏ`, the sum-form of `Δx·Δp ≥ ℏ/2` (indeed AM–GM turns one into
the other). -/
theorem heisenberg_canonical_sum {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (hψ : ‖ψ‖ = 1) (c : 𝕜)
    (hc : A (B ψ) - B (A ψ) = c • ψ) :
    ‖c‖
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        + ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2 := by
  have h := heisenberg_sum_form hA hB ψ
  have hnorm : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ = ‖c‖ := by
    rw [hc, inner_smul_right, norm_mul, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg ψ), hψ, one_pow, mul_one]
  rw [hnorm] at h
  exact h

/-! ## The weighted (tunable) sum uncertainty relation

The additive relation `Var(A) + Var(B) ≥ ‖⟪[A,B]⟫‖` (`robertson_sum_form`) uses the
*equal-weight* AM–GM `‖u‖² + ‖v‖² ≥ 2‖u‖‖v‖`.  The weighted AM–GM
`t‖u‖² + t⁻¹‖v‖² ≥ 2‖u‖‖v‖` (any `t > 0`) gives a one-parameter family of sum-form
bounds

  `t·‖(A−a)ψ‖² + t⁻¹·‖(B−b)ψ‖² ≥ ‖⟪ψ, (AB−BA)ψ⟫‖`,

with `robertson_sum_form` the `t = 1` case.  The free scale `t` lets one rebalance the
two variances — choosing `t = ‖v‖/‖u‖` recovers the sharp product bound `2‖u‖‖v‖`,
while any other `t` still yields a valid (looser) additive certificate.  This tunable
form is what underlies scale-optimized / state-independent sum uncertainty estimates. -/

/-- **Robertson uncertainty relation, weighted (tunable) sum form.**  For symmetric
`A, B`, any state `ψ`, real shifts `a, b`, and any weight `t > 0`,

  `‖⟪ψ, (AB−BA)ψ⟫‖ ≤ t·‖(A−a)ψ‖² + t⁻¹·‖(B−b)ψ‖²`.

The one-parameter generalization of `robertson_sum_form` (recovered at `t = 1`),
obtained from the standard-deviation form `robertson_std_form` by the *weighted*
AM–GM `t‖u‖² + t⁻¹‖v‖² ≥ 2‖u‖‖v‖`, itself the identity
`t‖u‖² + t⁻¹‖v‖² − 2‖u‖‖v‖ = t⁻¹(t‖u‖ − ‖v‖)² ≥ 0`. -/
theorem robertson_weighted_sum_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖
      ≤ t * ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 + t⁻¹ * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  have hstd := robertson_std_form hA hB ψ a b
  have htne : t ≠ 0 := ne_of_gt ht
  set u := ‖A ψ - (a : 𝕜) • ψ‖ with hu_def
  set v := ‖B ψ - (b : 𝕜) • ψ‖ with hv_def
  -- weighted AM–GM: `t·u² + t⁻¹·v² − 2uv = t⁻¹·(t·u − v)² ≥ 0`.
  have heq : t * u ^ 2 + t⁻¹ * v ^ 2 - 2 * (u * v) = t⁻¹ * (t * u - v) ^ 2 := by
    field_simp
    ring
  have hamgm : 2 * (u * v) ≤ t * u ^ 2 + t⁻¹ * v ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt (inv_pos.mpr ht)) (sq_nonneg (t * u - v)), heq]
  -- chain with the standard-deviation bound `½‖comm‖ ≤ u·v`.
  linarith [hstd, hamgm]

/-- **Heisenberg uncertainty principle, weighted (tunable) sum form.**  Instantiating
`robertson_weighted_sum_form` at the expectation values `⟨A⟩ = Re⟪ψ,Aψ⟫`,
`⟨B⟩ = Re⟪ψ,Bψ⟫` makes each summand a (scaled) variance:

  `Var_ψ(A)·t + Var_ψ(B)·t⁻¹ ≥ ‖⟪ψ, (AB−BA)ψ⟫‖`   (any `t > 0`).

The tunable companion of `heisenberg_sum_form` (the `t = 1` case). -/
theorem heisenberg_weighted_sum_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) {t : ℝ} (ht : 0 < t) :
    ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖
      ≤ t * ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        + t⁻¹ * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2 :=
  robertson_weighted_sum_form hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ))) ht

/-! ## Structure of the commutator expectation: `⟪ψ,[A,B]ψ⟫` is purely imaginary

Every uncertainty bound above depends on the commutator only through *the imaginary
part* `Im⟪Aψ,Bψ⟫` — the real part never appears.  The reason is a structural identity:
for symmetric `A, B` the commutator expectation `⟪ψ, (AB−BA)ψ⟫` is `i` times a **real**
scalar,

  `⟪ψ, (AB−BA)ψ⟫ = (2·Im⟪Aψ,Bψ⟫)·i`,

so it lies entirely on the imaginary axis (`Re = 0`) and its norm is *exactly*
`2·|Im⟪Aψ,Bψ⟫|`.  Equivalently `−i[A,B]` (equivalently `i[A,B]`) is a symmetric
operator — the hermitian "observable" whose expectation is the real number
`2·Im⟪Aψ,Bψ⟫` that the uncertainty product bounds.  These sharpen the internal
estimate `‖⟪ψ,[A,B]ψ⟫‖ ≤ 2|Im⟪u,v⟫|` used inside `robertson_uncertainty` to the exact
value, and explain why only the imaginary part enters Heisenberg's inequality. -/

/-- **The commutator expectation is `i` times a real number.**  For symmetric `A, B`,
`⟪ψ, (AB−BA)ψ⟫ = ↑(2·Im⟪Aψ,Bψ⟫)·i`.  Since `⟪Aψ,Bψ⟫` and `⟪Bψ,Aψ⟫` are complex
conjugates (both `A, B` symmetric), their difference is `z − z̄ = 2i·Im z`, purely
imaginary.  This is the exact structural identity behind the estimate used inside
`robertson_uncertainty`. -/
theorem inner_commutator_eq_ofReal_mul_I {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    inner 𝕜 ψ (A (B ψ) - B (A ψ))
      = ((2 * RCLike.im (inner 𝕜 (A ψ) (B ψ)) : ℝ) : 𝕜) * RCLike.I := by
  have e1 : inner 𝕜 ψ (A (B ψ)) = inner 𝕜 (A ψ) (B ψ) := (hA ψ (B ψ)).symm
  have e2 : inner 𝕜 ψ (B (A ψ)) = inner 𝕜 (B ψ) (A ψ) := (hB ψ (A ψ)).symm
  have hconj : inner 𝕜 (B ψ) (A ψ) = (starRingEnd 𝕜) (inner 𝕜 (A ψ) (B ψ)) :=
    (inner_conj_symm (B ψ) (A ψ)).symm
  rw [inner_sub_right, e1, e2, hconj, RCLike.sub_conj]
  push_cast
  ring

/-- **The commutator expectation is purely imaginary.**  `Re⟪ψ, (AB−BA)ψ⟫ = 0` for
symmetric `A, B` — the anticommutator/real-part contribution drops out, so the
commutator only feeds the *imaginary* part of the Cauchy–Schwarz core.  Valid over
`ℝ` and `ℂ` alike (over `ℝ` the whole expectation is `0`). -/
theorem re_inner_commutator_eq_zero {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    RCLike.re (inner 𝕜 ψ (A (B ψ) - B (A ψ))) = 0 := by
  have e1 : inner 𝕜 ψ (A (B ψ)) = inner 𝕜 (A ψ) (B ψ) := (hA ψ (B ψ)).symm
  have e2 : inner 𝕜 ψ (B (A ψ)) = inner 𝕜 (B ψ) (A ψ) := (hB ψ (A ψ)).symm
  have hconj : inner 𝕜 (B ψ) (A ψ) = (starRingEnd 𝕜) (inner 𝕜 (A ψ) (B ψ)) :=
    (inner_conj_symm (B ψ) (A ψ)).symm
  rw [inner_sub_right, e1, e2, hconj, map_sub, RCLike.conj_re, sub_self]

/-- **Sharp value of the commutator norm.**  Over a field with a genuine imaginary unit
(`RCLike.I ≠ 0`, i.e. `ℂ`), the internal estimate
`‖⟪ψ,[A,B]ψ⟫‖ ≤ 2|Im⟪u,v⟫|` used in `robertson_uncertainty` is in fact an **equality**:

  `‖⟪ψ, (AB−BA)ψ⟫‖ = 2·|Im⟪Aψ,Bψ⟫|`.

Consequently the Robertson lower bound `¼‖⟪ψ,[A,B]ψ⟫‖²` equals `(Im⟪Aψ,Bψ⟫)²`
exactly, pinning the commutator content of the uncertainty product to the squared
imaginary part of the centred inner product. -/
theorem norm_inner_commutator_eq (hI : (RCLike.I : 𝕜) ≠ 0) {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) :
    ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ = 2 * |RCLike.im (inner 𝕜 (A ψ) (B ψ))| := by
  rw [inner_commutator_eq_ofReal_mul_I hA hB ψ, norm_mul, RCLike.norm_ofReal,
    RCLike.norm_I_of_ne_zero hI, mul_one, abs_mul]
  norm_num

/-! ## The commutator as an operator: `i[A,B]` is Hermitian

The results above describe the commutator only through its *expectation*
`⟪ψ,[A,B]ψ⟫` — that it is purely imaginary (`re_inner_commutator_eq_zero`), equals
`↑(2·Im⟪Aψ,Bψ⟫)·i` (`inner_commutator_eq_ofReal_mul_I`), and has norm `2|Im⟪Aψ,Bψ⟫|`
(`norm_inner_commutator_eq`).  Here we lift this to the **operator** level, which is
the structural reason those expectation facts hold.

For symmetric `A, B` the bare commutator `[A,B] = AB − BA` is **anti-symmetric**
(anti-Hermitian): `⟪[A,B]x, y⟫ = −⟪x, [A,B]y⟫`.  Multiplying by the imaginary unit
therefore produces a **symmetric** (Hermitian) operator `i[A,B]`: a genuine
observable.  This is the operator-theoretic content of "the commutator of two
observables, times `i`, is again an observable" — and it is exactly why the
right-hand side of the uncertainty relation is the expectation of a *real* quantity.
The expectation reality (`re_inner_commutator_eq_zero`, here recovered as the
`im`-vanishing of `⟪ψ, (i[A,B])ψ⟫`) is then an immediate corollary of operator
symmetry, rather than a separate computation. -/

/-- **The commutator of two symmetric operators is anti-Hermitian.**  For symmetric
`A, B`, the bare commutator `[A,B] = A∘B − B∘A` satisfies

  `⟪[A,B]x, y⟫ = −⟪x, [A,B]y⟫`

for all `x, y`.  Moving each operator across the inner product with `hA`, `hB`
introduces two transpositions whose composite flips the sign: `⟪ABx,y⟫ = ⟪x,BAy⟫`
and `⟪BAx,y⟫ = ⟪x,ABy⟫`, so the difference negates.  This anti-symmetry is the
operator-level source of the purely-imaginary commutator expectation
`re_inner_commutator_eq_zero`. -/
theorem commutator_isAntisymmetric {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (x y : E) :
    inner 𝕜 ((A.comp B - B.comp A) x) y
      = - inner 𝕜 x ((A.comp B - B.comp A) y) := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, inner_sub_right]
  rw [hA (B x) y, hB x (A y), hB (A x) y, hA x (B y)]
  ring

/-- **`i[A,B]` is a symmetric (Hermitian) operator.**  For symmetric `A, B`, the
operator `i·(A∘B − B∘A)` is symmetric:

  `⟪(i[A,B])x, y⟫ = ⟪x, (i[A,B])y⟫`.

This is the operator-theoretic heart of the uncertainty principle: while `A` and `B`
need not commute, the scaled commutator `i[A,B]` is a bona fide observable, and it is
*its* expectation (a real number) that lower-bounds the variance product.  The proof
combines the anti-Hermiticity of the bare commutator
(`commutator_isAntisymmetric`) with `conj i = −i` (`RCLike.conj_I`): the conjugate
from `inner_smul_left` and the sign flip from anti-symmetry cancel to give symmetry.
Over `ℝ` (`i = 0`) the operator is `0`, trivially symmetric. -/
theorem commutator_smul_I_isSymmetric {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) :
    ((RCLike.I : 𝕜) • (A.comp B - B.comp A)).IsSymmetric := by
  intro x y
  have hanti := commutator_isAntisymmetric hA hB x y
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right]
  rw [hanti, RCLike.conj_I]
  ring

/-- **The `i[A,B]` expectation is real — operator-symmetry proof.**  Because
`i[A,B]` is a symmetric operator (`commutator_smul_I_isSymmetric`), its expectation
at any state is real: `Im⟪ψ, (i[A,B])ψ⟫ = 0`.  This recovers the expectation-level
fact `re_inner_commutator_eq_zero` (purely-imaginary bare commutator) as a one-line
corollary of operator Hermiticity — a symmetric operator has real diagonal
expectations because `⟪Cψ,ψ⟫ = ⟪ψ,Cψ⟫` while `⟪Cψ,ψ⟫ = conj⟪ψ,Cψ⟫`, forcing
`conj z = z`. -/
theorem inner_commutator_smul_I_isReal {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    RCLike.im (inner 𝕜 ψ (((RCLike.I : 𝕜) • (A.comp B - B.comp A)) ψ)) = 0 := by
  set C := (RCLike.I : 𝕜) • (A.comp B - B.comp A) with hC
  have hsym := commutator_smul_I_isSymmetric hA hB
  have heq : inner 𝕜 (C ψ) ψ = inner 𝕜 ψ (C ψ) := hsym ψ ψ
  have hconj : inner 𝕜 (C ψ) ψ = (starRingEnd 𝕜) (inner 𝕜 ψ (C ψ)) :=
    (inner_conj_symm (C ψ) ψ).symm
  have hz : (starRingEnd 𝕜) (inner 𝕜 ψ (C ψ)) = inner 𝕜 ψ (C ψ) := by rw [← hconj, heq]
  exact RCLike.conj_eq_iff_im.mp hz

/-- **The anticommutator `{A,B} = A∘B + B∘A` is symmetric.**  For symmetric `A, B` the
anticommutator is a genuine symmetric (Hermitian) operator: `⟪{A,B}x, y⟫ = ⟪x, {A,B}y⟫`.
Unlike the commutator (which is *anti*-symmetric, `commutator_isAntisymmetric`, and needs
the `i` twist to become Hermitian), the anticommutator is Hermitian on the nose.  Its
expectation is the symmetrized covariance `Re⟪(A−a)ψ,(B−b)ψ⟫` that appears as the extra
non-negative term in the Schrödinger refinement of the Robertson bound.  Proof is the
sign-flipped twin of `commutator_isAntisymmetric`, moving each factor across the inner
product by `IsSymmetric`. -/
theorem anticommutator_isSymmetric {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) : (A.comp B + B.comp A).IsSymmetric := by
  intro x y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_left, inner_add_right]
  rw [hA (B x) y, hB x (A y), hB (A x) y, hA x (B y)]
  ring

/-- **The anticommutator expectation is real.**  Because `{A,B}` is a symmetric operator
(`anticommutator_isSymmetric`), its diagonal expectation is real: `Im⟪ψ, {A,B}ψ⟫ = 0`.
The Hermitian counterpart of `inner_commutator_smul_I_isReal` — the symmetrized covariance
`Re⟪ψ,{A,B}ψ⟫` carries the entire expectation, with no imaginary part.  Same one-line
argument: a symmetric operator satisfies `⟪Cψ,ψ⟫ = ⟪ψ,Cψ⟫ = conj⟪ψ,Cψ⟫`, forcing the
expectation to equal its own conjugate. -/
theorem inner_anticommutator_isReal {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    RCLike.im (inner 𝕜 ψ ((A.comp B + B.comp A) ψ)) = 0 := by
  set C := A.comp B + B.comp A with hC
  have hsym := anticommutator_isSymmetric hA hB
  have heq : inner 𝕜 (C ψ) ψ = inner 𝕜 ψ (C ψ) := hsym ψ ψ
  have hconj : inner 𝕜 (C ψ) ψ = (starRingEnd 𝕜) (inner 𝕜 ψ (C ψ)) :=
    (inner_conj_symm (C ψ) ψ).symm
  have hz : (starRingEnd 𝕜) (inner 𝕜 ψ (C ψ)) = inner 𝕜 ψ (C ψ) := by rw [← hconj, heq]
  exact RCLike.conj_eq_iff_im.mp hz

/-! ## Saturation of the operator-level Robertson inequality

    The file characterizes saturation of the *abstract* Cauchy–Schwarz step
    (`im_inner_sq_eq_iff_robertson_saturated`, in terms of `Im⟪u,v⟫`) and exhibits a
    minimum-uncertainty *witness* (`exists_im_inner_sq_saturated`).  What was missing is
    the saturation condition for the *operator* statement `robertson_uncertainty` itself,
    whose right-hand side is the physical commutator expectation `¼‖⟪ψ,[A,B]ψ⟫‖²`.

    Over a field with a genuine imaginary unit (`RCLike.I ≠ 0`, i.e. `ℂ`) the bridge
    `⟪ψ,[A,B]ψ⟫ = ⟪u,v⟫ − ⟪v,u⟫ = 2i·Im⟪u,v⟫` gives the *exact* identity
    `¼‖⟪ψ,[A,B]ψ⟫‖² = (Im⟪u,v⟫)²`, so operator-level saturation is equivalent to abstract
    saturation, and the state-space characterization transfers verbatim. -/

/-- **When the Robertson inequality is saturated (minimum-uncertainty states).**  Over a
    field with a genuine imaginary unit (`RCLike.I ≠ 0`, i.e. `ℂ`), and for symmetric
    `A, B` with both centred vectors `u = (A−a)ψ`, `v = (B−b)ψ` nonzero, the operator
    Robertson bound `robertson_uncertainty` holds with **equality**

      `¼‖⟪ψ,[A,B]ψ⟫‖² = ‖(A−a)ψ‖²·‖(B−b)ψ‖²`

    if and only if the symmetrized covariance vanishes and `v` is a (nonzero) scalar
    multiple of `u`:  `Re⟪u,v⟫ = 0 ∧ ∃ r ≠ 0, v = r • u`.  At `a = ⟨A⟩`, `b = ⟨B⟩` these
    are exactly the *minimum-uncertainty* (coherent / squeezed) states.  This lifts the
    abstract Cauchy–Schwarz saturation `im_inner_sq_eq_iff_robertson_saturated` to the
    physical commutator-expectation form of the inequality, via the exact norm identity
    `¼‖⟪ψ,[A,B]ψ⟫‖² = (Im⟪u,v⟫)²` (valid over `ℂ` where `‖I‖ = 1`). -/
theorem robertson_saturated_iff (hI : (RCLike.I : 𝕜) ≠ 0) {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (a b : ℝ)
    (hu : A ψ - (a : 𝕜) • ψ ≠ 0) (hv : B ψ - (b : 𝕜) • ψ ≠ 0) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        = ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2
      ↔ RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)) = 0
        ∧ ∃ r : 𝕜, r ≠ 0 ∧ B ψ - (b : 𝕜) • ψ = r • (A ψ - (a : 𝕜) • ψ) := by
  set u := A ψ - (a : 𝕜) • ψ with hudef
  set v := B ψ - (b : 𝕜) • ψ with hvdef
  have hid : inner 𝕜 ψ (A (B ψ) - B (A ψ)) = inner 𝕜 u v - inner 𝕜 v u :=
    inner_commutator_eq_sub hA hB ψ a b
  have hconj : inner 𝕜 v u = (starRingEnd 𝕜) (inner 𝕜 u v) := (inner_conj_symm v u).symm
  have hInorm : ‖(RCLike.I : 𝕜)‖ = 1 := RCLike.norm_I_of_ne_zero hI
  have h2 : ‖(2 : 𝕜)‖ = 2 := RCLike.norm_two
  -- exact norm identity over ℂ:  ‖⟪ψ,[A,B]ψ⟫‖ = 2·|Im⟪u,v⟫|
  have hnorm : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ = 2 * |RCLike.im (inner 𝕜 u v)| := by
    rw [hid, hconj, RCLike.sub_conj, norm_mul, norm_mul, RCLike.norm_ofReal, h2, hInorm]
    ring
  -- hence  ¼‖⟪ψ,[A,B]ψ⟫‖² = (Im⟪u,v⟫)²
  have hsq : (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      = (RCLike.im (inner 𝕜 u v)) ^ 2 := by
    rw [hnorm, mul_pow, sq_abs]; ring
  rw [hsq]
  exact im_inner_sq_eq_iff_robertson_saturated hu hv

/-- **Strict Robertson inequality away from minimum-uncertainty states.**  Over `ℂ`
    (`RCLike.I ≠ 0`), whenever the saturation condition of `robertson_saturated_iff`
    fails — i.e. `ψ` is *not* a minimum-uncertainty state for `(A, B)` after the shifts
    `a, b` — the Robertson bound is **strict**:

      `¼‖⟪ψ,[A,B]ψ⟫‖² < ‖(A−a)ψ‖²·‖(B−b)ψ‖²`.

    Combines the non-strict bound `robertson_uncertainty` with the equality
    characterization `robertson_saturated_iff` (a `≤` that is not an `=` is a `<`). -/
theorem robertson_uncertainty_strict (hI : (RCLike.I : 𝕜) ≠ 0) {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (a b : ℝ)
    (hu : A ψ - (a : 𝕜) • ψ ≠ 0) (hv : B ψ - (b : 𝕜) • ψ ≠ 0)
    (hns : ¬ (RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)) = 0
        ∧ ∃ r : 𝕜, r ≠ 0 ∧ B ψ - (b : 𝕜) • ψ = r • (A ψ - (a : 𝕜) • ψ))) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      < ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  refine lt_of_le_of_ne (robertson_uncertainty hA hB ψ a b) ?_
  intro heq
  exact hns ((robertson_saturated_iff hI hA hB ψ a b hu hv).mp heq)

/-- **Schrödinger uncertainty relation, additive (sum) form.**  The covariance-refined
additive bound: for symmetric `A, B`, any state `ψ` and real shifts `a, b`, with
`u = (A−a)ψ`, `v = (B−b)ψ`,

  `‖⟪ψ, (AB−BA)ψ⟫‖² + 4·(Re⟪u,v⟫)² ≤ (‖u‖² + ‖v‖²)²`.

This is the additive counterpart of the multiplicative `schrodinger_uncertainty`, and a
genuine strengthening of the (squared) `robertson_sum_form`: it carries the extra
nonnegative covariance term `4·(Re⟪u,v⟫)²` on the left, which `robertson_sum_form`
discards.  Proof: multiply `schrodinger_uncertainty`
(`¼‖[A,B]‖² + (Re⟪u,v⟫)² ≤ ‖u‖²‖v‖²`) by `4` and combine with the AM–GM identity
`4‖u‖²‖v‖² ≤ (‖u‖² + ‖v‖²)²` (i.e. `(‖u‖² − ‖v‖²)² ≥ 0`).  Dropping the covariance term
recovers the squared `robertson_sum_form`. -/
theorem schrodinger_sum_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + 4 * RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)) ^ 2
      ≤ (‖A ψ - (a : 𝕜) • ψ‖ ^ 2 + ‖B ψ - (b : 𝕜) • ψ‖ ^ 2) ^ 2 := by
  have hsch := schrodinger_uncertainty hA hB ψ a b
  nlinarith [hsch, sq_nonneg (‖A ψ - (a : 𝕜) • ψ‖ ^ 2 - ‖B ψ - (b : 𝕜) • ψ‖ ^ 2),
    norm_nonneg (inner 𝕜 ψ (A (B ψ) - B (A ψ)))]

/-- **Schrödinger uncertainty principle, additive variance form.**  Instantiating
`schrodinger_sum_form` at the expectation values `⟨A⟩ = Re⟪ψ,Aψ⟫`, `⟨B⟩ = Re⟪ψ,Bψ⟫`
turns each squared centred norm into a variance, giving the covariance-refined additive
Heisenberg relation

  `‖⟪ψ,(AB−BA)ψ⟫‖² + 4·(Re⟪(A−⟨A⟩)ψ,(B−⟨B⟩)ψ⟫)² ≤ (Var_ψ(A) + Var_ψ(B))²`,

whose covariance term is the symmetrized `½⟪ψ,{A,B}ψ⟫ − ⟨A⟩⟨B⟩` (via
`re_inner_centred_eq_anticommutator`).  The Schrödinger member of the sum-form family,
strengthening `heisenberg_sum_form`. -/
theorem schrodinger_variance_sum_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) :
    ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + 4 * RCLike.re (inner 𝕜 (A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ)
            (B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ)) ^ 2
      ≤ (‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
          + ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2) ^ 2 :=
  schrodinger_sum_form hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ)))

/-! ## The Maccone–Pati *stronger* sum uncertainty relation

The additive relations above (`robertson_sum_form`, `heisenberg_sum_form`,
`robertson_weighted_sum_form`) all bound `Var(A) + Var(B)` from below by a quantity
proportional to the commutator norm `‖⟪ψ,[A,B]ψ⟫‖`.  Such bounds share a defect noted
by Maccone and Pati (*Phys. Rev. Lett.* **113**, 260401, 2014): the lower bound
**vanishes** whenever the commutator expectation does — even for genuinely incompatible
observables in a state where `⟪ψ,[A,B]ψ⟫ = 0`, so they can be trivially uninformative.

Maccone and Pati's *stronger* uncertainty relation removes this defect by adding a
state-dependent, manifestly nonnegative term built from **any** state `ψ⊥` orthogonal
to `ψ`.  Writing `u = (A−a)ψ`, `v = (B−b)ψ`, the mechanism is one line of Hilbert-space
geometry: the vector `Γ = u + i·v` satisfies the polarization identity

  `‖Γ‖² = ‖u + i·v‖² = ‖u‖² + ‖v‖² − 2·Im⟪u,v⟫`   (`normSq_add_I_smul`),

and Cauchy–Schwarz against a *unit* vector `w` gives `‖⟪w,Γ⟫‖² ≤ ‖Γ‖²`.  Rearranging,

  `Var(A) + Var(B) ≥ 2·Im⟪(A−a)ψ,(B−b)ψ⟫ + ‖⟪w, (A + i·B)ψ⟫‖²`,

where the projection term uses only `w ⊥ ψ` (the real shifts `a, b` drop out).  The
imaginary part `Im⟪u,v⟫` is shift-independent and equals `½` the "signed commutator"
`−i⟪ψ,[A,B]ψ⟫`; the extra `‖⟪w,(A ± iB)ψ⟫‖²` term is the genuine strengthening over
`robertson_sum_form` — it can be positive even when the commutator term vanishes.  The
two sign choices (`Γ± = u ± i·v`, theorems `maccone_pati_uncertainty` and
`maccone_pati_uncertainty_neg`) let one pick the orientation making the commutator term
`+‖⟪ψ,[A,B]ψ⟫‖` (see `maccone_pati_stronger_than_robertson_sum`). -/

/-- **Polarization identity for `u + i·v`.**  Over a field with a genuine imaginary
unit (`RCLike.I ≠ 0`, i.e. `ℂ`), for any vectors `u, v`,

  `‖u + i·v‖² = ‖u‖² + ‖v‖² − 2·Im⟪u,v⟫`.

The cross term `2·Re⟪u, i·v⟫ = −2·Im⟪u,v⟫` is the only place the imaginary part enters;
this is the algebraic engine of the Maccone–Pati stronger uncertainty relation. -/
theorem normSq_add_I_smul (hI : (RCLike.I : 𝕜) ≠ 0) (u v : E) :
    ‖u + (RCLike.I : 𝕜) • v‖ ^ 2
      = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * RCLike.im (inner 𝕜 u v) := by
  rw [norm_add_sq (𝕜 := 𝕜) u ((RCLike.I : 𝕜) • v), inner_smul_right, RCLike.I_mul_re,
    norm_smul, RCLike.norm_I_of_ne_zero hI, one_mul]
  ring

/-- **Maccone–Pati stronger sum uncertainty relation** (the `+i` orientation).  For
symmetric operators `A, B`, a state `ψ`, real shifts `a, b`, and **any** vector `w`
that is a *unit* vector orthogonal to `ψ` (`⟪w,ψ⟫ = 0`, `‖w‖ = 1` — abstractly a
`ψ⊥`), the sum of the squared centred norms is bounded below by the commutator term
*plus* a nonnegative projection term:

  `2·Im⟪(A−a)ψ,(B−b)ψ⟫ + ‖⟪w, Aψ + i·Bψ⟫‖² ≤ ‖(A−a)ψ‖² + ‖(B−b)ψ‖²`.

At `a = ⟨A⟩`, `b = ⟨B⟩` the right side is `Var(A) + Var(B)` (see
`maccone_pati_variance_form`).  The extra term `‖⟪ψ⊥, (A+iB)ψ⟫‖²` is what makes this
*strictly stronger* than `robertson_sum_form`: it can be positive even when the
commutator term vanishes, so the bound is informative for incompatible observables in
states with `⟪ψ,[A,B]ψ⟫ = 0`.  (Maccone–Pati, PRL 113, 260401, 2014.)

Proof: the vector `Γ = u + i·v` has `‖⟪w,Γ⟫‖² ≤ ‖w‖²·‖Γ‖² = ‖Γ‖²` (Cauchy–Schwarz,
`‖w‖ = 1`); rewrite `‖Γ‖²` by `normSq_add_I_smul`; and `⟪w,Γ⟫ = ⟪w, Aψ + i·Bψ⟫`
because the shift contributions `⟪w, a·ψ⟫`, `⟪w, i·(b·ψ)⟫` vanish by `⟪w,ψ⟫ = 0`. -/
theorem maccone_pati_uncertainty {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) (hI : (RCLike.I : 𝕜) ≠ 0)
    {w : E} (hw : inner 𝕜 w ψ = 0) (hwn : ‖w‖ = 1) :
    2 * RCLike.im (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ))
        + ‖inner 𝕜 w (A ψ + (RCLike.I : 𝕜) • B ψ)‖ ^ 2
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 + ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  set u := A ψ - (a : 𝕜) • ψ with hu
  set v := B ψ - (b : 𝕜) • ψ with hv
  -- The projection onto `w` sees only the uncentred part, since `w ⊥ ψ`.
  have hΓ : inner 𝕜 w (u + (RCLike.I : 𝕜) • v)
      = inner 𝕜 w (A ψ + (RCLike.I : 𝕜) • B ψ) := by
    simp only [hu, hv, inner_add_right, inner_sub_right, inner_smul_right, hw,
      mul_zero, sub_zero]
  -- Cauchy–Schwarz against the unit vector `w`.
  have hcs : ‖inner 𝕜 w (u + (RCLike.I : 𝕜) • v)‖ ≤ ‖u + (RCLike.I : 𝕜) • v‖ := by
    have h := norm_inner_le_norm (𝕜 := 𝕜) w (u + (RCLike.I : 𝕜) • v)
    rwa [hwn, one_mul] at h
  have hsq : ‖inner 𝕜 w (u + (RCLike.I : 𝕜) • v)‖ ^ 2
      ≤ ‖u + (RCLike.I : 𝕜) • v‖ ^ 2 := by
    nlinarith [hcs, norm_nonneg (inner 𝕜 w (u + (RCLike.I : 𝕜) • v)),
      norm_nonneg (u + (RCLike.I : 𝕜) • v)]
  rw [hΓ] at hsq
  have hid := normSq_add_I_smul (𝕜 := 𝕜) hI u v
  linarith [hsq, hid]

/-- **Polarization identity for `u − i·v`.**  The `−i` companion of `normSq_add_I_smul`:

  `‖u − i·v‖² = ‖u‖² + ‖v‖² + 2·Im⟪u,v⟫`.

Immediate from `normSq_add_I_smul` at `(u, −v)`, since `u − i·v = u + i·(−v)`. -/
theorem normSq_sub_I_smul (hI : (RCLike.I : 𝕜) ≠ 0) (u v : E) :
    ‖u - (RCLike.I : 𝕜) • v‖ ^ 2
      = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * RCLike.im (inner 𝕜 u v) := by
  have hrw : u - (RCLike.I : 𝕜) • v = u + (RCLike.I : 𝕜) • (-v) := by
    rw [smul_neg]; abel
  rw [hrw, normSq_add_I_smul hI u (-v), norm_neg, inner_neg_right, map_neg]
  ring

/-- **Maccone–Pati stronger sum uncertainty relation** (the `−i` orientation).  The
companion of `maccone_pati_uncertainty` using `Γ = u − i·v`; it flips the sign of the
commutator term and conjugates the operator combination to `A − i·B`:

  `−2·Im⟪(A−a)ψ,(B−b)ψ⟫ + ‖⟪w, Aψ − i·Bψ⟫‖² ≤ ‖(A−a)ψ‖² + ‖(B−b)ψ‖²`.

Proof mirrors `maccone_pati_uncertainty` with `Γ = u − i·v` (whose squared norm is
`normSq_sub_I_smul`).  The two orientations together give the full Maccone–Pati bound
(`±`); selecting the one whose commutator term is nonnegative yields
`maccone_pati_stronger_than_robertson_sum`. -/
theorem maccone_pati_uncertainty_neg {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) (hI : (RCLike.I : 𝕜) ≠ 0)
    {w : E} (hw : inner 𝕜 w ψ = 0) (hwn : ‖w‖ = 1) :
    -(2 * RCLike.im (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)))
        + ‖inner 𝕜 w (A ψ - (RCLike.I : 𝕜) • B ψ)‖ ^ 2
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 + ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  set u := A ψ - (a : 𝕜) • ψ with hu
  set v := B ψ - (b : 𝕜) • ψ with hv
  have hΓ : inner 𝕜 w (u - (RCLike.I : 𝕜) • v)
      = inner 𝕜 w (A ψ - (RCLike.I : 𝕜) • B ψ) := by
    simp only [hu, hv, inner_sub_right, inner_smul_right, hw, mul_zero, sub_zero]
  have hcs : ‖inner 𝕜 w (u - (RCLike.I : 𝕜) • v)‖ ≤ ‖u - (RCLike.I : 𝕜) • v‖ := by
    have h := norm_inner_le_norm (𝕜 := 𝕜) w (u - (RCLike.I : 𝕜) • v)
    rwa [hwn, one_mul] at h
  have hsq : ‖inner 𝕜 w (u - (RCLike.I : 𝕜) • v)‖ ^ 2
      ≤ ‖u - (RCLike.I : 𝕜) • v‖ ^ 2 := by
    nlinarith [hcs, norm_nonneg (inner 𝕜 w (u - (RCLike.I : 𝕜) • v)),
      norm_nonneg (u - (RCLike.I : 𝕜) • v)]
  rw [hΓ] at hsq
  have hid := normSq_sub_I_smul (𝕜 := 𝕜) hI u v
  linarith [hsq, hid]

/-- **Maccone–Pati bound, variance form.**  Instantiating `maccone_pati_uncertainty` at
the expectation values `⟨A⟩ = Re⟪ψ,Aψ⟫`, `⟨B⟩ = Re⟪ψ,Bψ⟫` makes each right-hand summand
a variance, giving the physical stronger uncertainty relation

  `Var_ψ(A) + Var_ψ(B) ≥ 2·Im⟪(A−⟨A⟩)ψ,(B−⟨B⟩)ψ⟫ + ‖⟪ψ⊥, (A + i·B)ψ⟫‖²`

for any unit `ψ⊥ ⊥ ψ`.  Dropping the (nonnegative) projection term and taking
`|·|` of the commutator term recovers `heisenberg_sum_form`; the projection term is
the Maccone–Pati improvement. -/
theorem maccone_pati_variance_form {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (hI : (RCLike.I : 𝕜) ≠ 0)
    {w : E} (hw : inner 𝕜 w ψ = 0) (hwn : ‖w‖ = 1) :
    2 * RCLike.im (inner 𝕜 (A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ)
          (B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ))
        + ‖inner 𝕜 w (A ψ + (RCLike.I : 𝕜) • B ψ)‖ ^ 2
      ≤ ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        + ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2 :=
  maccone_pati_uncertainty hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ))) hI hw hwn

/-- **The Maccone–Pati bound dominates the Robertson sum bound.**  Combining both
orientations (`maccone_pati_uncertainty` and its `_neg` companion) and selecting the
one whose commutator term is `+‖⟪ψ,[A,B]ψ⟫‖ = 2|Im⟪u,v⟫|` shows that, for a unit
`ψ⊥ ⊥ ψ`, the sum of centred norms exceeds the Robertson-sum lower bound `‖⟪ψ,[A,B]ψ⟫‖`
*by at least* a nonnegative projection term — one of `‖⟪w,(A+iB)ψ⟫‖²`, `‖⟪w,(A−iB)ψ⟫‖²`:

  `‖⟪ψ,[A,B]ψ⟫‖ + min(‖⟪w,(A+iB)ψ⟫‖², ‖⟪w,(A−iB)ψ⟫‖²) ≤ ‖(A−a)ψ‖² + ‖(B−b)ψ‖²`.

Since `‖⟪ψ,[A,B]ψ⟫‖ = 2|Im⟪u,v⟫|` (the file's `norm_inner_commutator...` structure),
this is exactly `robertson_sum_form` augmented by a nonnegative Maccone–Pati term,
making the strengthening explicit. -/
theorem maccone_pati_stronger_than_robertson_sum {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) (hI : (RCLike.I : 𝕜) ≠ 0)
    {w : E} (hw : inner 𝕜 w ψ = 0) (hwn : ‖w‖ = 1) :
    2 * |RCLike.im (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ))|
        + min (‖inner 𝕜 w (A ψ + (RCLike.I : 𝕜) • B ψ)‖ ^ 2)
              (‖inner 𝕜 w (A ψ - (RCLike.I : 𝕜) • B ψ)‖ ^ 2)
      ≤ ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 + ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 := by
  have hpos := maccone_pati_uncertainty hA hB ψ a b hI hw hwn
  have hneg := maccone_pati_uncertainty_neg hA hB ψ a b hI hw hwn
  set m := RCLike.im (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)) with hm
  have hmin_pos := min_le_left (‖inner 𝕜 w (A ψ + (RCLike.I : 𝕜) • B ψ)‖ ^ 2)
    (‖inner 𝕜 w (A ψ - (RCLike.I : 𝕜) • B ψ)‖ ^ 2)
  have hmin_neg := min_le_right (‖inner 𝕜 w (A ψ + (RCLike.I : 𝕜) • B ψ)‖ ^ 2)
    (‖inner 𝕜 w (A ψ - (RCLike.I : 𝕜) • B ψ)‖ ^ 2)
  rcases abs_cases m with ⟨habs, _⟩ | ⟨habs, _⟩
  · rw [habs]; linarith [hpos, hmin_pos]
  · rw [habs]; linarith [hneg, hmin_neg]

/-- **Schrödinger saturation — the full minimum-uncertainty family.**  Over a field with
a genuine imaginary unit (`RCLike.I ≠ 0`, i.e. `ℂ`), for symmetric `A, B`, a state `ψ`
and real shifts `a, b` with both centred vectors `u = (A−a)ψ`, `v = (B−b)ψ` nonzero, the
**Schrödinger** bound `schrodinger_uncertainty` holds with **equality**

    `¼‖⟪ψ,[A,B]ψ⟫‖² + (Re⟪u,v⟫)² = ‖u‖²·‖v‖²`

**iff** `u` and `v` are parallel, `v = r • u` for some `r ≠ 0`.

Unlike the Robertson saturation `im_inner_sq_eq_iff_robertson_saturated` — which demands
the *extra* purely-imaginary-ratio (vanishing-covariance) condition `Re⟪u,v⟫ = 0` — the
Schrödinger bound is saturated by the **entire** proportional family.  With
`u = (A−⟨A⟩)ψ`, `v = (B−⟨B⟩)ψ` these are *all* the minimum-uncertainty states — coherent
**and** squeezed — `(B−⟨B⟩)ψ = r·(A−⟨A⟩)ψ`, `r ∈ ℂ∖{0}`; Robertson's subclass is the
purely-imaginary slice `Re r = 0` (cf. `im_inner_smul_saturated_iff`).  This is the
operator-level (physical, commutator-expectation) dressing of the inner-product
equality `gram_eq_iff_parallel`.

Proof: over `ℂ` the commutator norm is *exactly* `‖⟪ψ,[A,B]ψ⟫‖ = 2·|Im⟪u,v⟫|` — here
`‖I‖ = 1`, so the Robertson estimate `hnb` of `robertson_uncertainty` is tight — whence
`¼‖⟪ψ,[A,B]ψ⟫‖² = (Im⟪u,v⟫)²` and the Schrödinger equation collapses to the Gram
equality `(Re⟪u,v⟫)² + (Im⟪u,v⟫)² = ‖u‖²‖v‖²`, characterized by `gram_eq_iff_parallel`. -/
theorem schrodinger_saturated_iff {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) (hI : (RCLike.I : 𝕜) ≠ 0)
    (hu : A ψ - (a : 𝕜) • ψ ≠ 0) (hv : B ψ - (b : 𝕜) • ψ ≠ 0) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + RCLike.re (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ)) ^ 2
      = ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2
      ↔ ∃ r : 𝕜, r ≠ 0 ∧ B ψ - (b : 𝕜) • ψ = r • (A ψ - (a : 𝕜) • ψ) := by
  set u := A ψ - (a : 𝕜) • ψ with hudef
  set v := B ψ - (b : 𝕜) • ψ with hvdef
  have hid : inner 𝕜 ψ (A (B ψ) - B (A ψ)) = inner 𝕜 u v - inner 𝕜 v u :=
    inner_commutator_eq_sub hA hB ψ a b
  have hconj : inner 𝕜 v u = (starRingEnd 𝕜) (inner 𝕜 u v) := (inner_conj_symm v u).symm
  have hIeq : ‖(RCLike.I : 𝕜)‖ = 1 := RCLike.norm_I_of_ne_zero hI
  have h2 : ‖(2 : 𝕜)‖ = 2 := RCLike.norm_two
  -- Over ℂ the commutator norm is *exactly* `2·|Im⟪u,v⟫|` (Robertson's estimate is tight).
  have hnb : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ = 2 * |RCLike.im (inner 𝕜 u v)| := by
    rw [hid, hconj, RCLike.sub_conj, norm_mul, norm_mul, RCLike.norm_ofReal, h2, hIeq]
    ring
  have hcomm : (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      = (RCLike.im (inner 𝕜 u v)) ^ 2 := by
    rw [hnb, mul_pow, sq_abs]; ring
  rw [hcomm, add_comm]
  exact gram_eq_iff_parallel hu hv

/-- **Schrödinger saturation, variance form — the minimum-uncertainty capstone.**  For
observables with **nonzero commutator expectation** `⟪ψ, (AB−BA)ψ⟫ ≠ 0` over `ℂ`
(`RCLike.I ≠ 0`), the Schrödinger relation *at the expectation-value shifts*
`a = ⟨A⟩ = Re⟪ψ,Aψ⟫`, `b = ⟨B⟩ = Re⟪ψ,Bψ⟫` (the physically standard variance form
`schrodinger_variance_form`) is saturated

    `Var_ψ(A)·Var_ψ(B) = ¼‖⟪ψ,[A,B]ψ⟫‖² + (Re⟪(A−⟨A⟩)ψ,(B−⟨B⟩)ψ⟫)²`

**iff** the fluctuation vectors are proportional,
`(B−⟨B⟩)ψ = r·(A−⟨A⟩)ψ` for some `r ≠ 0`.

This is the clean physical statement: a state achieves the (covariance-corrected)
minimum uncertainty **exactly** when its `B`-fluctuation is a scalar multiple of its
`A`-fluctuation.  The nonvanishing-fluctuation side conditions of
`schrodinger_saturated_iff` are *free* here — a nonzero commutator forces both variances
strictly positive (`centred_ne_zero_of_commutator_ne_zero`), so no separate hypothesis
`(A−⟨A⟩)ψ ≠ 0`, `(B−⟨B⟩)ψ ≠ 0` is needed. -/
theorem schrodinger_variance_saturated_iff {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : E) (hI : (RCLike.I : 𝕜) ≠ 0)
    (hcomm : inner 𝕜 ψ (A (B ψ) - B (A ψ)) ≠ 0) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
        + RCLike.re (inner 𝕜 (A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ)
            (B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ)) ^ 2
      = ‖A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
        * ‖B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ‖ ^ 2
      ↔ ∃ r : 𝕜, r ≠ 0 ∧ B ψ - ((RCLike.re (inner 𝕜 ψ (B ψ)) : ℝ) : 𝕜) • ψ
          = r • (A ψ - ((RCLike.re (inner 𝕜 ψ (A ψ)) : ℝ) : 𝕜) • ψ) := by
  obtain ⟨hu, hv⟩ := centred_ne_zero_of_commutator_ne_zero hA hB ψ
    (RCLike.re (inner 𝕜 ψ (A ψ))) (RCLike.re (inner 𝕜 ψ (B ψ))) hcomm
  exact schrodinger_saturated_iff hA hB ψ (RCLike.re (inner 𝕜 ψ (A ψ)))
    (RCLike.re (inner 𝕜 ψ (B ψ))) hI hu hv

/-! ### L² specialization — the integral Cauchy–Schwarz core

  OQ-04's problem statement names the *integral* Cauchy–Schwarz inequality in `L²`,
  `|⟪f,g⟫|² ≤ ‖f‖²·‖g‖²` with `⟪f,g⟫ = ∫ conj(f)·g`, as the source of Heisenberg's
  bound.  Instantiating the abstract inner-product-space core on the concrete space
  `α →₂[μ] ℂ` recovers exactly this integral form.  The L² inner product *is* the
  integral of the pointwise inner product (`MeasureTheory.L2.inner_def`, which is
  definitional), and pointwise `⟪z,w⟫_ℂ = conj z · w` (`RCLike.inner_apply'`), so the
  abstract bounds become bounds on the real / imaginary parts (and the modulus) of
  `∫ conj(f)·g` by `‖f‖·‖g‖`.  The imaginary part is the Heisenberg (commutator) term,
  the real part the Schrödinger (anticommutator) term.  All are axiom-free, obtained by
  one rewrite through the bridge `L2_inner_eq_integral`. -/

section L2Specialization

open MeasureTheory
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The L² inner product as an integral.**  `⟪f, g⟫ = ∫ conj(f)·g`.  This is the
    bridge identifying the abstract Cauchy–Schwarz core with the integral form named
    in OQ-04's problem statement. -/
theorem L2_inner_eq_integral (f g : α →₂[μ] ℂ) :
    inner ℂ f g = ∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  simp_rw [RCLike.inner_apply']

/-- **L² integral Cauchy–Schwarz — imaginary (Heisenberg) part.**
    `|Im ∫ conj(f)·g| ≤ ‖f‖·‖g‖`.  With `f = (X−⟨X⟩)ψ`, `g = (P−⟨P⟩)ψ` the imaginary
    part is the commutator term `Im⟪f,g⟫` underlying `Δx·Δp ≥ ℏ/2`. -/
theorem abs_im_integral_inner_le_L2 (f g : α →₂[μ] ℂ) :
    |RCLike.im (∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ)| ≤ ‖f‖ * ‖g‖ := by
  rw [← L2_inner_eq_integral]
  exact abs_im_inner_le_norm_mul_norm (𝕜 := ℂ) f g

/-- **Squared L² integral Cauchy–Schwarz — imaginary part.**
    `(Im ∫ conj(f)·g)² ≤ ‖f‖²·‖g‖²`. -/
theorem im_integral_inner_sq_le_L2 (f g : α →₂[μ] ℂ) :
    (RCLike.im (∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ)) ^ 2
      ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  rw [← L2_inner_eq_integral]
  exact im_inner_sq_le (𝕜 := ℂ) f g

/-- **L² integral Cauchy–Schwarz — real (Schrödinger) part.**
    `|Re ∫ conj(f)·g| ≤ ‖f‖·‖g‖`, the anticommutator/covariance companion. -/
theorem abs_re_integral_inner_le_L2 (f g : α →₂[μ] ℂ) :
    |RCLike.re (∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ)| ≤ ‖f‖ * ‖g‖ := by
  rw [← L2_inner_eq_integral]
  exact abs_re_inner_le_norm_mul_norm (𝕜 := ℂ) f g

/-- **Squared L² integral Cauchy–Schwarz — real part.**
    `(Re ∫ conj(f)·g)² ≤ ‖f‖²·‖g‖²`. -/
theorem re_integral_inner_sq_le_L2 (f g : α →₂[μ] ℂ) :
    (RCLike.re (∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ)) ^ 2
      ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  rw [← L2_inner_eq_integral]
  exact re_inner_sq_le (𝕜 := ℂ) f g

/-- **Sharp L² integral Cauchy–Schwarz (Gram form).**
    `(Re ∫ conj(f)·g)² + (Im ∫ conj(f)·g)² ≤ ‖f‖²·‖g‖²` — the literal
    `|⟪f,g⟫|² ≤ ‖f‖²·‖g‖²` of OQ-04, split into its Heisenberg (Im) and
    Schrödinger (Re) components. -/
theorem integral_inner_sq_le_gram_L2 (f g : α →₂[μ] ℂ) :
    (RCLike.re (∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ)) ^ 2
      + (RCLike.im (∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ)) ^ 2
      ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  rw [← L2_inner_eq_integral]
  exact inner_sq_le_gram (𝕜 := ℂ) f g

/-- **L² integral Cauchy–Schwarz — modulus form.**  `‖∫ conj(f)·g‖² ≤ ‖f‖²·‖g‖²`,
    the classical squared Cauchy–Schwarz `|⟪f,g⟫|² ≤ ‖f‖²·‖g‖²` on `L²(μ)`. -/
theorem norm_integral_inner_sq_le_L2 (f g : α →₂[μ] ℂ) :
    ‖∫ a, conj ((f : α → ℂ) a) * (g : α → ℂ) a ∂μ‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  rw [← L2_inner_eq_integral]
  have h : ‖inner ℂ f g‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm f g
  nlinarith [h, norm_nonneg (inner ℂ f g),
    mul_nonneg (norm_nonneg f) (norm_nonneg g)]

end L2Specialization

end CauchySchwarzIntegralOQ04

#print axioms CauchySchwarzIntegralOQ04.gram_eq_iff_parallel
#print axioms CauchySchwarzIntegralOQ04.inner_commutator_eq_ofReal_mul_I
#print axioms CauchySchwarzIntegralOQ04.norm_inner_commutator_eq
#print axioms CauchySchwarzIntegralOQ04.commutator_smul_I_isSymmetric
#print axioms CauchySchwarzIntegralOQ04.inner_commutator_smul_I_isReal
#print axioms CauchySchwarzIntegralOQ04.robertson_saturated_iff
#print axioms CauchySchwarzIntegralOQ04.L2_inner_eq_integral
#print axioms CauchySchwarzIntegralOQ04.integral_inner_sq_le_gram_L2
#print axioms CauchySchwarzIntegralOQ04.norm_integral_inner_sq_le_L2
#print axioms CauchySchwarzIntegralOQ04.robertson_uncertainty_strict
#print axioms CauchySchwarzIntegralOQ04.normSq_add_I_smul
#print axioms CauchySchwarzIntegralOQ04.maccone_pati_uncertainty
#print axioms CauchySchwarzIntegralOQ04.maccone_pati_uncertainty_neg
#print axioms CauchySchwarzIntegralOQ04.maccone_pati_variance_form
#print axioms CauchySchwarzIntegralOQ04.maccone_pati_stronger_than_robertson_sum
#print axioms CauchySchwarzIntegralOQ04.schrodinger_saturated_iff
#print axioms CauchySchwarzIntegralOQ04.schrodinger_variance_saturated_iff
#print axioms CauchySchwarzIntegralOQ04.schrodinger_sum_form
#print axioms CauchySchwarzIntegralOQ04.schrodinger_variance_sum_form
