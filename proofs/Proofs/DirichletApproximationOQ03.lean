/-
  Dirichlet's Approximation Theorem via Minkowski's Convex-Body Theorem
  (research problem: dirichlet-approximation-theorem-oq-03)

  The gallery entry `dirichlet-approximation-theorem` proves, for every real `α` and
  integer `N ≥ 1`, the bound `|qα - p| < 1/N` for some `1 ≤ q ≤ N` via the pigeonhole
  principle on fractional parts.

  This file develops the **geometry-of-numbers** (Minkowski) re-derivation requested by
  the open problem.  The classical one-line proof applies Minkowski's convex-body theorem
  to the symmetric convex body

      K(α, N) = { v ∈ ℝ²  :  |v₀| ≤ N  and  |α·v₀ - v₁| ≤ 1/N },

  a parallelogram of area exactly `4 = 2² · (covolume of ℤ²)`.  Minkowski's theorem (the
  closed/compact, area-`= 2ⁿ` variant) yields a nonzero integer point `(q, p) ∈ ℤ²` of `K`,
  which is exactly a Dirichlet approximation `|qα - p| ≤ 1/N` with `1 ≤ q ≤ N`.

  What is established here, sorry-free and axiom-free:

  * `body`             — the convex body `K(α, N)`.
  * `body_symm`        — `K` is symmetric about the origin (`v ∈ K → -v ∈ K`).
  * `body_convex`      — `K` is convex (intersection of two linear slabs).
  * `body_isClosed`    — `K` is closed (intersection of two closed linear slabs).
                         Together with boundedness (a one-line norm estimate) this gives the
                         compactness Minkowski's closed-body variant needs.
  * `dirichlet_of_lattice_point`
                       — **the arithmetic bridge**: a nonzero integer point of `K`
                         (for `N ≥ 2`) is a Dirichlet approximation.  This is the shared
                         final step that turns Minkowski's lattice point into the theorem,
                         handling the sign normalisation `q ≥ 1` and the degenerate
                         `q = 0` boundary case.
  * `dirichlet_via_convex_body`
                       — Dirichlet's bound, conditional on the Minkowski conclusion
                         (existence of a nonzero **integer** point of `K`).

  The remaining open step is purely the **volume computation** `volume (body α N) = 4`,
  feeding Mathlib's `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`
  with the standard lattice `ℤ² = Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))`
  (covolume `1` by `ZSpan.volume_fundamentalDomain`).  That volume equals `4` because `K`
  is the image of the box `[-N, N] × [-1/N, 1/N]` (Lebesgue volume `4`) under the shear
  `(x, y) ↦ (x, αx - y)`, a linear map of determinant `-1`
  (`MeasureTheory.Measure.addHaar_image_linearMap`).  The geometric inputs that Minkowski
  consumes are all discharged above; only the measure bookkeeping remains.
-/
import Mathlib

namespace DirichletMinkowski

open Set MeasureTheory

variable (α : ℝ) (N : ℕ)

/-- The symmetric convex body whose lattice points are Dirichlet approximations:
    `K(α, N) = {v : ℝ² | |v 0| ≤ N ∧ |α·v 0 - v 1| ≤ 1/N}`. -/
def body : Set (Fin 2 → ℝ) :=
  {v | |v 0| ≤ (N : ℝ) ∧ |α * v 0 - v 1| ≤ 1 / (N : ℝ)}

variable {α N}

/-- `K(α, N)` is symmetric about the origin. -/
theorem body_symm {v : Fin 2 → ℝ} (hv : v ∈ body α N) : -v ∈ body α N := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · show |(-v) 0| ≤ (N : ℝ)
    rw [Pi.neg_apply, abs_neg]; exact h1
  · show |α * (-v) 0 - (-v) 1| ≤ 1 / (N : ℝ)
    rw [Pi.neg_apply, Pi.neg_apply,
      show α * -(v 0) - -(v 1) = -(α * v 0 - v 1) from by ring, abs_neg]
    exact h2

variable (α N)

/-- `K(α, N)` is convex: it is the intersection of two slabs, each the preimage of a
    closed interval under a linear functional. -/
theorem body_convex : Convex ℝ (body α N) := by
  have e : body α N =
      (⇑(LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)) ⁻¹' Icc (-(N : ℝ)) (N : ℝ) ∩
      (⇑(α • (LinearMap.proj 0) - (LinearMap.proj 1) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)) ⁻¹'
        Icc (-(1 / (N : ℝ))) (1 / (N : ℝ)) := by
    ext v
    simp only [body, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Icc, abs_le,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

/-- `K(α, N)` is closed: it is the intersection of two slabs, each the preimage of a
    closed interval under a continuous linear functional. -/
theorem body_isClosed : IsClosed (body α N) := by
  have e : body α N =
      (⇑(LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)) ⁻¹' Icc (-(N : ℝ)) (N : ℝ) ∩
      (⇑(α • (LinearMap.proj 0) - (LinearMap.proj 1) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)) ⁻¹'
        Icc (-(1 / (N : ℝ))) (1 / (N : ℝ)) := by
    ext v
    simp only [body, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Icc, abs_le,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [e]
  exact (isClosed_Icc.preimage (LinearMap.continuous_of_finiteDimensional _)).inter
    (isClosed_Icc.preimage (LinearMap.continuous_of_finiteDimensional _))

/-- **Arithmetic bridge.**  For `N ≥ 2`, a nonzero integer point `(q₀, p₀)` of the body
    `K(α, N)` is a Dirichlet approximation: after a sign normalisation it yields
    `1 ≤ q ≤ N` with `|qα - p| ≤ 1/N`.

    The hypothesis `N ≥ 2` rules out the degenerate boundary point `(0, ±1)`: this is the
    only way a nonzero integer point could have first coordinate `0`, and it lies in `K`
    exactly when `N = 1`. -/
theorem dirichlet_of_lattice_point (hN : 2 ≤ N) {q₀ p₀ : ℤ}
    (hne : ¬ (q₀ = 0 ∧ p₀ = 0))
    (hx : |(q₀ : ℝ)| ≤ (N : ℝ))
    (hy : |α * (q₀ : ℝ) - (p₀ : ℝ)| ≤ 1 / (N : ℝ)) :
    ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ N ∧ |(q : ℝ) * α - (p : ℝ)| ≤ 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- Step 1: the first coordinate cannot vanish.
  have hq0 : q₀ ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_zero, zero_sub, abs_neg] at hy
    have h1N : 1 / (N : ℝ) < 1 := by rw [div_lt_one hNR]; exact hN1
    have hlt : |(p₀ : ℝ)| < 1 := lt_of_le_of_lt hy h1N
    obtain ⟨hl, hr⟩ := abs_lt.mp hlt
    have : p₀ = 0 := by
      have hl' : (-1 : ℤ) < p₀ := by exact_mod_cast hl
      have hr' : p₀ < 1 := by exact_mod_cast hr
      omega
    exact hne ⟨rfl, this⟩
  -- Step 2: sign-normalise so that `q = |q₀| ≥ 1`.
  have hqpos : 1 ≤ q₀.natAbs := by omega
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · -- q₀ < 0: take q = |q₀|, p = -p₀.
    have hqR : (q₀ : ℝ) < 0 := by exact_mod_cast hneg
    have hnat : (q₀.natAbs : ℝ) = -(q₀ : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_neg hneg]; push_cast; ring
    refine ⟨-p₀, q₀.natAbs, hqpos, ?_, ?_⟩
    · have h := hx; rw [abs_of_neg hqR] at h
      have : (q₀.natAbs : ℝ) ≤ (N : ℝ) := by rw [hnat]; exact h
      exact_mod_cast this
    · rw [hnat]
      push_cast
      rw [show -(q₀ : ℝ) * α - -(p₀ : ℝ) = -(α * (q₀ : ℝ) - (p₀ : ℝ)) from by ring, abs_neg]
      exact hy
  · -- q₀ > 0: take q = |q₀|, p = p₀.
    have hqR : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast hpos
    have hnat : (q₀.natAbs : ℝ) = (q₀ : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_pos hpos]
    refine ⟨p₀, q₀.natAbs, hqpos, ?_, ?_⟩
    · have h := hx; rw [abs_of_pos hqR] at h
      have : (q₀.natAbs : ℝ) ≤ (N : ℝ) := by rw [hnat]; exact h
      exact_mod_cast this
    · rw [hnat, mul_comm (q₀ : ℝ) α]; exact hy

/-- **Dirichlet's approximation theorem, conditional on Minkowski.**  Given a nonzero
    point of the body `K(α, N)` with integer coordinates — exactly what Minkowski's
    convex-body theorem produces once `volume (body α N) = 4` is supplied — Dirichlet's
    bound `|qα - p| ≤ 1/N` (with `1 ≤ q ≤ N`) follows.  The geometric hypotheses Minkowski
    needs (`body_symm`, `body_convex`, `body_isClosed`) are discharged above. -/
theorem dirichlet_via_convex_body (hN : 2 ≤ N)
    (hMink : ∃ v : Fin 2 → ℝ, v ∈ body α N ∧ v ≠ 0 ∧ ∀ i, ∃ m : ℤ, v i = (m : ℝ)) :
    ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ N ∧ |(q : ℝ) * α - (p : ℝ)| ≤ 1 / (N : ℝ) := by
  obtain ⟨v, ⟨hv0, hv1⟩, hvne, hint⟩ := hMink
  obtain ⟨q₀, hq₀⟩ := hint 0
  obtain ⟨p₀, hp₀⟩ := hint 1
  refine dirichlet_of_lattice_point α N hN (q₀ := q₀) (p₀ := p₀) ?_ ?_ ?_
  · rintro ⟨rfl, rfl⟩
    apply hvne
    funext i
    fin_cases i
    · simpa using hq₀
    · simpa using hp₀
  · rw [← hq₀]; exact hv0
  · rw [← hq₀, ← hp₀]; exact hv1

/-! ### The volume computation and the unconditional Minkowski derivation

The remaining content of the open problem is the measure computation `volume (K) = 4`.  We discharge
it via the **shear** `T : (x, y) ↦ (x, α·x − y)`, a linear map of determinant `−1` whose image of
the axis-aligned box `[−N, N] × [−1/N, 1/N]` (Lebesgue volume `4`) is exactly `K`.  Feeding the
resulting `volume (K) = 4 = 1 · 2² = covol(ℤ²) · 2^(dim)` into Mathlib's compact Minkowski theorem
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` produces the nonzero integer point,
discharging the `hMink` hypothesis of `dirichlet_via_convex_body`.  The result `dirichlet_via_minkowski`
is therefore an **unconditional, sorry-free, axiom-free** geometry-of-numbers proof of Dirichlet's
bound. -/

/-- The shear `(x, y) ↦ (x, α·x − y)` as a linear endomorphism of `ℝ²`.  Its matrix
    `!![1, 0; α, -1]` has determinant `−1`, so the map is volume-preserving and `K(α, N)` is its
    image of the axis-aligned box `[−N, N] × [−1/N, 1/N]`. -/
def shear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![1, 0; α, -1]

/-- The axis-aligned box `[−N, N] × [−1/N, 1/N]`, whose shear image is `K(α, N)`. -/
def box : Set (Fin 2 → ℝ) := {v | |v 0| ≤ (N : ℝ) ∧ |v 1| ≤ 1 / (N : ℝ)}

theorem shear_apply_zero (v : Fin 2 → ℝ) : shear α v 0 = v 0 := by
  show (Matrix.toLin' !![1, 0; α, -1]) v 0 = v 0
  rw [Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem shear_apply_one (v : Fin 2 → ℝ) : shear α v 1 = α * v 0 - v 1 := by
  show (Matrix.toLin' !![1, 0; α, -1]) v 1 = α * v 0 - v 1
  rw [Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The shear is an involution: `T ∘ T = id`. -/
theorem shear_involutive (w : Fin 2 → ℝ) : shear α (shear α w) = w := by
  funext i
  fin_cases i
  · show shear α (shear α w) 0 = w 0
    rw [shear_apply_zero, shear_apply_zero]
  · show shear α (shear α w) 1 = w 1
    rw [shear_apply_one, shear_apply_one, shear_apply_zero]; ring

/-- The body `K(α, N)` is the shear image of the axis-aligned box. -/
theorem body_eq_image : body α N = ⇑(shear α) '' box N := by
  ext w
  simp only [body, box, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨shear α w, ⟨by rw [shear_apply_zero]; exact h0, by rw [shear_apply_one]; exact h1⟩,
      shear_involutive α w⟩
  · rintro ⟨v, ⟨hv0, hv1⟩, rfl⟩
    refine ⟨by rw [shear_apply_zero]; exact hv0, ?_⟩
    rw [shear_apply_one, shear_apply_zero, show α * v 0 - (α * v 0 - v 1) = v 1 from by ring]
    exact hv1

/-- `box N` is the closed rectangle `Icc (-N, -1/N) (N, 1/N)`. -/
theorem box_eq_Icc :
    box N = Set.Icc (![-(N : ℝ), -(1 / (N : ℝ))] : Fin 2 → ℝ) ![(N : ℝ), 1 / (N : ℝ)] := by
  ext v
  simp only [box, Set.mem_setOf_eq, Set.mem_Icc, abs_le, Pi.le_def, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

theorem box_isCompact : IsCompact (box N) := by
  rw [box_eq_Icc]; exact isCompact_Icc

theorem body_isCompact : IsCompact (body α N) := by
  rw [body_eq_image]
  exact (box_isCompact N).image (shear α).continuous_of_finiteDimensional

/-- **The volume computation.**  `volume (box N) = 4`. -/
theorem box_volume (hN : 1 ≤ N) : volume (box N) = 4 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [box_eq_Icc, ← pi_univ_Icc, volume_pi_pi, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith)]
  rw [show ((N : ℝ) - -(N : ℝ)) * (1 / (N : ℝ) - -(1 / (N : ℝ))) = 4 from by field_simp; ring]
  norm_num

/-- **The volume computation for the body.**  `volume (K(α, N)) = 4`, the area input Minkowski
    needs.  Proved from `box_volume` via the determinant-`(−1)` shear and `addHaar_image_linearMap`. -/
theorem body_volume (hN : 1 ≤ N) : volume (body α N) = 4 := by
  have hdet : LinearMap.det (shear α) = -1 := by
    show LinearMap.det (Matrix.toLin' !![1, 0; α, -1]) = -1
    rw [LinearMap.det_toLin', Matrix.det_fin_two_of]; ring
  rw [body_eq_image, Measure.addHaar_image_linearMap, hdet, box_volume N hN, abs_neg, abs_one,
    ENNReal.ofReal_one, one_mul]

/-- **Dirichlet's approximation theorem via Minkowski's convex-body theorem — unconditional.**
    For every real `α` and every `N ≥ 2`, there are integers `p` and `1 ≤ q ≤ N` with
    `|qα − p| ≤ 1/N`.  This discharges the `hMink` hypothesis of `dirichlet_via_convex_body` by
    feeding `volume (K) = 4 = covol(ℤ²) · 2^(dim)` into Mathlib's compact Minkowski theorem and
    reading off integer coordinates from the resulting lattice point. -/
theorem dirichlet_via_minkowski (hN : 2 ≤ N) :
    ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ N ∧ |(q : ℝ) * α - (p : ℝ)| ≤ 1 / (N : ℝ) := by
  classical
  apply dirichlet_via_convex_body α N hN
  -- The standard lattice `ℤ² = span ℤ (range (Pi.basisFun ℝ (Fin 2)))` and its unit-covolume
  -- fundamental domain.
  have h_fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 2)) volume
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))); infer_instance
  have hcov : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi_pi]; simp [Real.volume_Ico]
  have hrank : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by
    simp [Module.finrank_fintype_fun_eq_card]
  -- The Minkowski volume hypothesis `covol · 2^dim ≤ volume K`, here `1 · 2² = 4 ≤ 4`.
  have hvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2)))
      * 2 ^ Module.finrank ℝ (Fin 2 → ℝ) ≤ volume (body α N) := by
    rw [hcov, hrank, body_volume α N (by omega), one_mul]; norm_num
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund (fun y hy => body_symm hy) (body_convex α N) (body_isCompact α N) hvol
  rw [Submodule.mem_toAddSubgroup] at hx
  refine ⟨x, ?_, ?_, ?_⟩
  · exact h_mem
  · intro hx0; exact h_nz (Subtype.ext hx0)
  · intro i
    obtain ⟨z, hz⟩ := ((Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ x).mp hx i
    refine ⟨z, ?_⟩
    have hb : (Pi.basisFun ℝ (Fin 2)).repr x i = x i := by simp
    rw [hb] at hz
    simpa using hz.symm

end DirichletMinkowski
