/-
  Cauchy–Schwarz Integral — OQ-04, variational companion:
  the uncertainty principle as a *squared-distance* minimization.

  The main file `CauchySchwarzIntegralOQ04` derives the Robertson/Heisenberg
  uncertainty relations **directly** from the Cauchy–Schwarz inequality
  `|⟪u,v⟫| ≤ ‖u‖·‖v‖`.  This companion records the *other* classical route — the
  original physicist's derivation (Weyl, Pauli, Kennard): for real mixing
  parameter `t`, the vector `u + t·(i·v)` has nonnegative squared norm, giving a
  nonnegative quadratic in `t`,

      `q(t) = ‖u‖² + t²‖v‖² − 2t·Im⟪u,v⟫ ≥ 0`   (`variational_quadratic_nonneg`),

  and the uncertainty inequality is exactly the *discriminant condition* for this
  quadratic to have no real root.  The novelty over the Cauchy–Schwarz route is
  that it exhibits the **exact minimizer** — the optimal "squeezing" parameter
  `t⋆ = Im⟪u,v⟫ / ‖v‖²` — at which the residual is smallest, and shows the
  uncertainty *gap* is a genuine squared distance:

      `‖v‖²·q(t) − (‖u‖²‖v‖² − (Im⟪u,v⟫)²) = (‖v‖²·t − Im⟪u,v⟫)² ≥ 0`,

  so `min_t ‖v‖²·q(t) = ‖u‖²‖v‖² − (Im⟪u,v⟫)²`, attained at `t⋆`
  (`variational_min`, `variational_min_attained`).  With `u = (A−a)ψ`, `v = (B−b)ψ`
  and the main file's identity `¼‖⟪ψ,[A,B]ψ⟫‖² = (Im⟪u,v⟫)²` (over ℂ), the
  Robertson gap `Var(A)·Var(B) − ¼‖⟪ψ,[A,B]ψ⟫‖²` is *equal* to the minimal squared
  norm `min_t ‖v‖²·‖(A−a)ψ + t·i·(B−b)ψ‖²` — a squared distance, manifestly
  nonnegative (`robertson_gap_eq_variational_min`, `robertson_variational_min`).
  The optimal `t⋆` is the physical *conditional / squeezed* combination.

  Everything is over a field with a genuine imaginary unit (`RCLike.I ≠ 0`, i.e.
  `ℂ`); over `ℝ` the imaginary part is `0` and the content is vacuous.  All results
  are fully machine-checked (0 axioms, 0 sorries).

  Reference: Kennard (1927); Weyl, *Gruppentheorie und Quantenmechanik* (1928);
  the variational (Gram-determinant) derivation, e.g. Reed–Simon, *Functional
  Analysis*, §VIII.
-/

import Proofs.CauchySchwarzIntegralOQ04

namespace CauchySchwarzIntegralOQ04Variational

open CauchySchwarzIntegralOQ04

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Real-parameter polarization identity.**  Over a field with a genuine imaginary
    unit (`RCLike.I ≠ 0`, i.e. `ℂ`), for any vectors `u, v` and real parameter `t`,

      `‖u + t·(i·v)‖² = ‖u‖² + t²·‖v‖² − 2t·Im⟪u,v⟫`.

    The one-parameter family generalizing the main file's `normSq_add_I_smul`
    (the `t = 1` case): it is the quadratic in the real mixing parameter `t` whose
    nonnegativity drives the variational derivation of the uncertainty principle. -/
theorem normSq_add_real_smul_I_smul (hI : (RCLike.I : 𝕜) ≠ 0) (u v : E) (t : ℝ) :
    ‖u + (t : 𝕜) • ((RCLike.I : 𝕜) • v)‖ ^ 2
      = ‖u‖ ^ 2 + t ^ 2 * ‖v‖ ^ 2 - 2 * t * RCLike.im (inner 𝕜 u v) := by
  have hcomm : (t : 𝕜) • ((RCLike.I : 𝕜) • v) = (RCLike.I : 𝕜) • ((t : 𝕜) • v) :=
    smul_comm _ _ _
  rw [hcomm, normSq_add_I_smul hI u ((t : 𝕜) • v)]
  have hn : ‖(t : 𝕜) • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
  have him : RCLike.im (inner 𝕜 u ((t : 𝕜) • v)) = t * RCLike.im (inner 𝕜 u v) := by
    rw [inner_smul_right]
    simp [RCLike.mul_im]
  rw [hn, him]; ring

/-- **The variational quadratic is nonnegative** (the uncertainty principle's engine).
    Over `ℂ` (`RCLike.I ≠ 0`), for all vectors `u, v` and every real `t`,

      `0 ≤ ‖u‖² + t²·‖v‖² − 2t·Im⟪u,v⟫`.

    This is just the nonnegativity of the squared norm `‖u + t·(i·v)‖²`
    (`normSq_add_real_smul_I_smul`) read as a quadratic in `t`.  With
    `u = (A−a)ψ`, `v = (B−b)ψ` this is the statement that
    `Var(A) + t²·Var(B) ≥ 2t·Im⟪(A−a)ψ,(B−b)ψ⟫` for all `t` — the physicist's
    starting point (Kennard/Weyl), whose discriminant condition *is* the
    uncertainty inequality. -/
theorem variational_quadratic_nonneg (hI : (RCLike.I : 𝕜) ≠ 0) (u v : E) (t : ℝ) :
    0 ≤ ‖u‖ ^ 2 + t ^ 2 * ‖v‖ ^ 2 - 2 * t * RCLike.im (inner 𝕜 u v) := by
  rw [← normSq_add_real_smul_I_smul hI u v t]; positivity

/-- **The uncertainty gap is a squared distance** (nonnegative form).  Over `ℂ`
    (`RCLike.I ≠ 0`), for all `u, v` and every real `t`,

      `‖u‖²·‖v‖² − (Im⟪u,v⟫)² ≤ ‖v‖²·‖u + t·(i·v)‖²`.

    The right-hand side is the (scaled) squared norm of the mixed vector; the
    left-hand side is the fixed uncertainty gap.  So the gap is a lower bound for
    the squared distance at *every* mixing `t`, and (by `variational_min_attained`)
    is exactly the minimum.  Proof: the difference is the perfect square
    `(‖v‖²·t − Im⟪u,v⟫)² ≥ 0`. -/
theorem variational_min (hI : (RCLike.I : 𝕜) ≠ 0) (u v : E) (t : ℝ) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 - (RCLike.im (inner 𝕜 u v)) ^ 2
      ≤ ‖v‖ ^ 2 * ‖u + (t : 𝕜) • ((RCLike.I : 𝕜) • v)‖ ^ 2 := by
  rw [normSq_add_real_smul_I_smul hI u v t]
  nlinarith [sq_nonneg (‖v‖ ^ 2 * t - RCLike.im (inner 𝕜 u v))]

/-- **The optimal mixing parameter attains the uncertainty gap.**  Over `ℂ`
    (`RCLike.I ≠ 0`), for nonzero `v`, at the optimal ("squeezing") parameter
    `t⋆ = Im⟪u,v⟫ / ‖v‖²`,

      `‖v‖²·‖u + t⋆·(i·v)‖² = ‖u‖²·‖v‖² − (Im⟪u,v⟫)²`.

    Together with `variational_min` this shows the minimum over all real `t` of
    `‖v‖²·‖u + t·(i·v)‖²` is exactly the uncertainty gap `‖u‖²‖v‖² − (Im⟪u,v⟫)²`,
    attained at `t⋆`.  With `u = (A−a)ψ`, `v = (B−b)ψ`, `t⋆` is the physical optimal
    conditional/squeezed combination realizing minimum uncertainty. -/
theorem variational_min_attained (hI : (RCLike.I : 𝕜) ≠ 0) (u : E) {v : E}
    (hv : v ≠ 0) :
    ‖v‖ ^ 2 * ‖u + ((RCLike.im (inner 𝕜 u v) / ‖v‖ ^ 2 : ℝ) : 𝕜)
          • ((RCLike.I : 𝕜) • v)‖ ^ 2
      = ‖u‖ ^ 2 * ‖v‖ ^ 2 - (RCLike.im (inner 𝕜 u v)) ^ 2 := by
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  rw [normSq_add_real_smul_I_smul hI u v]
  field_simp
  ring

/-- **Variational derivation of the squared uncertainty inequality.**  Over `ℂ`
    (`RCLike.I ≠ 0`), the discriminant condition for the nonnegative quadratic
    `variational_quadratic_nonneg` yields

      `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`.

    This re-proves the main file's `im_inner_sq_le` by the variational route
    (no real root ⟹ discriminant ≤ 0): for `v ≠ 0` evaluate the gap identity
    `variational_min_attained` (whose right side must be `≥ 0` since the left is a
    squared norm); for `v = 0` both sides vanish.  It closes the loop, showing the
    physicist's derivation lands the same Heisenberg bound as Cauchy–Schwarz. -/
theorem im_inner_sq_le_variational (hI : (RCLike.I : 𝕜) ≠ 0) (u v : E) :
    (RCLike.im (inner 𝕜 u v)) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · have hle := variational_min hI u v (RCLike.im (inner 𝕜 u v) / ‖v‖ ^ 2)
    have heq := variational_min_attained hI u hv
    have hnn : (0 : ℝ) ≤ ‖v‖ ^ 2 * ‖u + ((RCLike.im (inner 𝕜 u v) / ‖v‖ ^ 2 : ℝ) : 𝕜)
        • ((RCLike.I : 𝕜) • v)‖ ^ 2 := by positivity
    rw [heq] at hnn
    linarith

/-! ## Operator level: the Robertson gap is a squared distance

With `u = (A−a)ψ`, `v = (B−b)ψ`, the imaginary part `Im⟪u,v⟫` is `½` the signed
commutator, and over `ℂ` the main file's identity gives
`(Im⟪u,v⟫)² = ¼‖⟪ψ,[A,B]ψ⟫‖²`.  Substituting into the variational identities turns
the abstract gap `‖u‖²‖v‖² − (Im⟪u,v⟫)²` into the physical **Robertson gap**
`Var(A)·Var(B) − ¼‖⟪ψ,[A,B]ψ⟫‖²`, exhibiting it as the minimal squared norm of the
mixed fluctuation vector — hence manifestly nonnegative, an independent proof of
`robertson_uncertainty`. -/

/-- **The commutator term equals the squared imaginary part** (over `ℂ`).  For
    symmetric `A, B` and real shifts `a, b`, with `u = (A−a)ψ`, `v = (B−b)ψ`,

      `¼‖⟪ψ, (AB−BA)ψ⟫‖² = (Im⟪u,v⟫)²`.

    This is the bridge (extracted from the main file's `robertson_saturated_iff`)
    turning the abstract variational gap into the physical Robertson gap. -/
theorem quarter_commutator_norm_sq_eq (hI : (RCLike.I : 𝕜) ≠ 0) {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      = (RCLike.im (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ))) ^ 2 := by
  set u := A ψ - (a : 𝕜) • ψ with hudef
  set v := B ψ - (b : 𝕜) • ψ with hvdef
  have hid : inner 𝕜 ψ (A (B ψ) - B (A ψ)) = inner 𝕜 u v - inner 𝕜 v u :=
    inner_commutator_eq_sub hA hB ψ a b
  have hconj : inner 𝕜 v u = (starRingEnd 𝕜) (inner 𝕜 u v) := (inner_conj_symm v u).symm
  have hIeq : ‖(RCLike.I : 𝕜)‖ = 1 := RCLike.norm_I_of_ne_zero hI
  have h2 : ‖(2 : 𝕜)‖ = 2 := RCLike.norm_two
  have hnorm : ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ = 2 * |RCLike.im (inner 𝕜 u v)| := by
    rw [hid, hconj, RCLike.sub_conj, norm_mul, norm_mul, RCLike.norm_ofReal, h2, hIeq]
    ring
  rw [hnorm, mul_pow, sq_abs]; ring

/-- **The Robertson gap is the minimal squared norm of the mixed fluctuation vector.**
    Over `ℂ` (`RCLike.I ≠ 0`), for symmetric `A, B`, a state `ψ` and real shifts
    `a, b`, with `u = (A−a)ψ`, `v = (B−b)ψ` and **any** real mixing `t`,

      `‖u‖²·‖v‖² − ¼‖⟪ψ,[A,B]ψ⟫‖² ≤ ‖v‖²·‖u + t·(i·v)‖²`.

    The left side is the Robertson gap `Var(A)·Var(B) − ¼‖⟪ψ,[A,B]ψ⟫‖²` (at the
    expectation-value shifts); the right side is a scaled squared norm.  So the
    Robertson gap is a lower bound for a squared distance — an independent proof
    that it is nonnegative, i.e. of `robertson_uncertainty` — and, by
    `robertson_gap_eq_variational_min`, is exactly the minimum. -/
theorem robertson_variational_min (hI : (RCLike.I : 𝕜) ≠ 0) {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) (t : ℝ) :
    ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2
        - (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2
      ≤ ‖B ψ - (b : 𝕜) • ψ‖ ^ 2
        * ‖(A ψ - (a : 𝕜) • ψ) + (t : 𝕜)
            • ((RCLike.I : 𝕜) • (B ψ - (b : 𝕜) • ψ))‖ ^ 2 := by
  rw [quarter_commutator_norm_sq_eq hI hA hB ψ a b]
  exact variational_min hI (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ) t

/-- **The Robertson gap equals the minimal squared distance** (attained at the optimal
    squeezing parameter).  Over `ℂ` (`RCLike.I ≠ 0`), for symmetric `A, B` with the
    `B`-fluctuation `v = (B−b)ψ ≠ 0`, at the optimal parameter
    `t⋆ = Im⟪(A−a)ψ,(B−b)ψ⟫ / ‖(B−b)ψ‖²`,

      `‖v‖²·‖(A−a)ψ + t⋆·(i·v)‖²
         = ‖(A−a)ψ‖²·‖v‖² − ¼‖⟪ψ,[A,B]ψ⟫‖²`.

    Together with `robertson_variational_min` this identifies the Robertson gap
    `Var(A)·Var(B) − ¼‖⟪ψ,[A,B]ψ⟫‖²` with the *minimum* over all real `t` of the
    scaled squared norm of the mixed fluctuation vector, attained at `t⋆`.  The
    optimal `t⋆` is the physical squeezing that realizes minimum uncertainty; the
    gap vanishes precisely when this minimal residual does, recovering the
    minimum-uncertainty (coherent/squeezed) states of the main file's
    `robertson_saturated_iff`. -/
theorem robertson_gap_eq_variational_min (hI : (RCLike.I : 𝕜) ≠ 0) {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (a b : ℝ)
    (hv : B ψ - (b : 𝕜) • ψ ≠ 0) :
    ‖B ψ - (b : 𝕜) • ψ‖ ^ 2
        * ‖(A ψ - (a : 𝕜) • ψ) + ((RCLike.im
              (inner 𝕜 (A ψ - (a : 𝕜) • ψ) (B ψ - (b : 𝕜) • ψ))
              / ‖B ψ - (b : 𝕜) • ψ‖ ^ 2 : ℝ) : 𝕜)
            • ((RCLike.I : 𝕜) • (B ψ - (b : 𝕜) • ψ))‖ ^ 2
      = ‖A ψ - (a : 𝕜) • ψ‖ ^ 2 * ‖B ψ - (b : 𝕜) • ψ‖ ^ 2
        - (1 / 4 : ℝ) * ‖inner 𝕜 ψ (A (B ψ) - B (A ψ))‖ ^ 2 := by
  rw [quarter_commutator_norm_sq_eq hI hA hB ψ a b]
  exact variational_min_attained hI (A ψ - (a : 𝕜) • ψ) hv

end CauchySchwarzIntegralOQ04Variational

#print axioms CauchySchwarzIntegralOQ04Variational.normSq_add_real_smul_I_smul
#print axioms CauchySchwarzIntegralOQ04Variational.variational_quadratic_nonneg
#print axioms CauchySchwarzIntegralOQ04Variational.variational_min
#print axioms CauchySchwarzIntegralOQ04Variational.variational_min_attained
#print axioms CauchySchwarzIntegralOQ04Variational.im_inner_sq_le_variational
#print axioms CauchySchwarzIntegralOQ04Variational.quarter_commutator_norm_sq_eq
#print axioms CauchySchwarzIntegralOQ04Variational.robertson_variational_min
#print axioms CauchySchwarzIntegralOQ04Variational.robertson_gap_eq_variational_min
