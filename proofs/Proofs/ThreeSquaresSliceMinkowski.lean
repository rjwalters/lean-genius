/-
  The 2D-slice Minkowski bound for the three-squares Dirichlet construction.

  This file isolates the remaining open step of `dirichlet_key_lemma`
  in `Proofs/ThreeSquares.lean`. Session researcher-11 (2026-06-16, recorded in
  `G2-minkowski-2p-gap.md`) pinned down that the 3D index-p² ellipsoid route
  CANNOT supply the required `Q < 2p` bound — the generic 2ⁿ Minkowski bound on
  the covolume-p² sublattice only gives `Q ≲ p^(4/3)`, too weak by a factor
  `~p^(1/3)`. The attainable route restricts to the slice `z = 0`, dropping to
  the index-p sublattice `{(x,y) ∈ ℤ² : x ≡ r·y (mod p)}` with the BINARY form
  `x² + d·y²`. Its 2D Hermite bound gives a nonzero point with
  `x² + d·y² ≤ (2/√3)·√d·p`, which is `< 2p` exactly when `d ≤ 2` — and the file's
  own case split uses only `d ∈ {1, 2}`.

  STATUS (researcher-2, 2026-06-18): the `d = 1` case is now FULLY PROVED by an
  elementary Thue/pigeonhole argument (no measure theory) — see
  `exists_slice_point_lt_two_mul_d1`. The `d = 2` case
  (`exists_slice_point_lt_two_mul_d2`) remains the sole `sorry`: it genuinely
  requires the area bound on the ellipse `x² + 2y² ≤ R` (the integer box is
  provably insufficient — 394 counterexamples were exhibited in
  `verify_slice_minkowski.py`), so it needs the measure-theoretic strict
  Minkowski convex-body theorem, not pigeonhole.

  UPDATE (researcher-12, 2026-06-18): the `d = 2` step now has a TURNKEY recipe
  (see its docstring below) — a near-verbatim port of the proved axiom-free
  `dirichlet_approximation` (`MinkowskiTheoremOQ02OQ01.lean`). Key simplification:
  keep the standard `ℤ²` lattice (covolume 1) and shear the *set* to
  `E' = {(a,b) | (p·a + r·b)² + 2b² < 2p}`; then `vol(E') = √2·π ≈ 4.443 > 4` is
  `p`-INDEPENDENT, so Minkowski applies uniformly, and the returned `(a,b)` yields
  `(x,y) = (a·p + b·r, b)` with `p ∣ (x − r·y)` automatic. The target lemma was
  re-verified true for all `p < 1500` (all `r`) and the two elementary shortcuts
  (box bound, strict small-ellipse count) re-confirmed insufficient. Remaining work
  is purely the measure-theory port (2D ellipse volume + the `Measure.map S` change
  of variables) — build/Aristotle-gated this session (Aristotle backend down).

  Three pieces:
  - `exists_slice_point_lt_two_mul_d1` (PROVED): the `d = 1` pure 2D
    geometry-of-numbers existence, via a Thue pigeonhole on the box `[0,⌊√p⌋]²`.
    The only subtlety is strictness when `p` is a perfect square `m²`: there the
    plain box can return the corner difference `(±m, ±m)` with `x²+y² = 2p`, so
    we run the pigeonhole on the box with the two corners `(m,m)`, `(m,0)`
    removed, which forces a non-corner collision and hence the strict bound.
  - `exists_slice_point_lt_two_mul_d2` (PROVED, build-pending): the `d = 2` existence.
  - `exists_slice_point_lt_two_mul` (PROVED for d=1, reduces d=2 to the above):
    the original combined statement, dispatching on `d ∈ {1, 2}`.
  - `slice_point_to_dirichlet_vector` (PROVED): pure plumbing that lifts a 2D
    slice point `(x, y)` to the `Fin 3 → ℤ` vector `![x, y, 0]`.

  NOTE (researcher-1, 2026-06-18): the `d = 2` `sorry` is now DISCHARGED in
  source by `exists_slice_point_lt_two_mul_d2` (the measure-theoretic port below);
  the file is `sorry`-free.  BUILD VERIFICATION IS STILL PENDING — the docker host
  was saturated (load 13-17, lake recompiling Mathlib) and could not complete a
  build this session.  Kept UNregistered in `Proofs.lean` until a build confirms.
  Also fixed a pre-existing parse bug: the `-/` token inside `build-/Aristotle`
  (twice) closed the block comment / docstring early, so this file never parsed.
-/
import Mathlib

namespace ThreeSquaresSlice

/-- **The `d = 1` slice point (PROVED).**

For any `p > 0` and any `r : ℤ`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` of `ℤ²` contains a nonzero vector with
`x² + y² < 2p`.

Elementary proof: a Thue pigeonhole on the box of pairs `(a, b)` with
`0 ≤ a, b ≤ ⌊√p⌋`. The box has `(⌊√p⌋+1)² > p` points, so two collide under
`(a, b) ↦ a − r·b (mod p)`; their difference `(x, y)` satisfies `p ∣ (x − r·y)`
and `|x|, |y| ≤ ⌊√p⌋`. When `p` is not a perfect square this already gives
`x² + y² ≤ 2⌊√p⌋² < 2p`; when `p = m²` we instead pigeonhole on the box with the
corners `(m, m)`, `(m, 0)` deleted, which excludes the only `(±m, ±m)`
differences and so forces `x² + y² ≤ m² + (m−1)² < 2p`. -/
theorem exists_slice_point_lt_two_mul_d1
    (p : ℕ) (hp : 0 < p) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + y ^ 2 < 2 * p := by
  set m : ℕ := Nat.sqrt p with hm
  have hle : m * m ≤ p := by rw [hm]; exact Nat.sqrt_le p
  have hlt : p < (m + 1) * (m + 1) := by
    rw [hm]; simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt p
  set box : Finset (ℕ × ℕ) := Finset.range (m + 1) ×ˢ Finset.range (m + 1) with hbox
  have hbox_card : box.card = (m + 1) * (m + 1) := by
    rw [hbox, Finset.card_product, Finset.card_range, Finset.card_range]
  have mem_box : ∀ a b : ℕ, a ≤ m → b ≤ m → (a, b) ∈ box := by
    intro a b ha hb
    rw [hbox]
    exact Finset.mk_mem_product (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega))
  -- generic pigeonhole over any large-enough sub-box
  have pigeon : ∀ (B : Finset (ℕ × ℕ)), B ⊆ box → p < B.card →
      ∃ a₁ a₂ b₁ b₂ : ℕ, (a₁, b₁) ∈ B ∧ (a₂, b₂) ∈ B ∧ (a₁, b₁) ≠ (a₂, b₂) ∧
        a₁ ≤ m ∧ a₂ ≤ m ∧ b₁ ≤ m ∧ b₂ ≤ m ∧
        (p : ℤ) ∣ ((a₁ : ℤ) - a₂ - r * ((b₁ : ℤ) - b₂)) := by
    intro B hsub hcard
    obtain ⟨⟨a₁, b₁⟩, h1, ⟨a₂, b₂⟩, h2, hne, hfeq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := B) (t := Finset.range p)
        (f := fun ab => (((ab.1 : ℤ) - r * (ab.2 : ℤ)) % (p : ℤ)).toNat)
        (by rw [Finset.card_range]; exact hcard)
        (by
          intro ab _
          rw [Finset.mem_range]
          have h0 : (0 : ℤ) ≤ ((ab.1 : ℤ) - r * (ab.2 : ℤ)) % (p : ℤ) :=
            Int.emod_nonneg _ (by exact_mod_cast hp.ne')
          have h1 : ((ab.1 : ℤ) - r * (ab.2 : ℤ)) % (p : ℤ) < (p : ℤ) :=
            Int.emod_lt_of_pos _ (by exact_mod_cast hp)
          omega)
    have hb1box := hsub h1
    have hb2box := hsub h2
    simp only [hbox, Finset.mem_product, Finset.mem_range] at hb1box hb2box
    refine ⟨a₁, a₂, b₁, b₂, h1, h2, hne, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · -- divisibility from residue equality
      have e0 : (0 : ℤ) ≤ ((a₁ : ℤ) - r * b₁) % (p : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have e1 : (0 : ℤ) ≤ ((a₂ : ℤ) - r * b₂) % (p : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have hfeq' : (((a₁ : ℤ) - r * (b₁ : ℤ)) % (p : ℤ)).toNat
          = (((a₂ : ℤ) - r * (b₂ : ℤ)) % (p : ℤ)).toNat := hfeq
      have huv : ((a₁ : ℤ) - r * b₁) % (p : ℤ) = ((a₂ : ℤ) - r * b₂) % (p : ℤ) := by
        rw [← Int.toNat_of_nonneg e0, ← Int.toNat_of_nonneg e1, hfeq']
      have hmod : ((a₁ : ℤ) - r * b₁) ≡ ((a₂ : ℤ) - r * b₂) [ZMOD (p : ℤ)] := huv
      have hd := Int.modEq_iff_dvd.mp hmod
      have hreq : ((a₁ : ℤ) - a₂ - r * ((b₁ : ℤ) - b₂))
          = -(((a₂ : ℤ) - r * b₂) - ((a₁ : ℤ) - r * b₁)) := by ring
      rw [hreq]
      exact (dvd_neg).mpr hd
  by_cases hsq : m * m = p
  · -- p is a perfect square; remove two corners so no (±m, ±m) difference survives
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h1
      · rw [h0] at hsq; simp at hsq; omega
      · exact h1
    set B : Finset (ℕ × ℕ) := box \ {(m, m), (m, 0)} with hB
    have hcorners_sub : ({(m, m), (m, 0)} : Finset (ℕ × ℕ)) ⊆ box := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨mem_box m m (le_refl m) (le_refl m), mem_box m 0 (le_refl m) (Nat.zero_le m)⟩
    have hcorners_card : ({(m, m), (m, 0)} : Finset (ℕ × ℕ)).card = 2 := by
      rw [Finset.card_insert_of_not_mem (by simp only [Finset.mem_singleton, Prod.mk.injEq];
        omega), Finset.card_singleton]
    have hBcard : p < B.card := by
      have h2 : B.card = (m + 1) * (m + 1) - 2 := by
        rw [hB, Finset.card_sdiff hcorners_sub, hbox_card, hcorners_card]
      have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      rw [h2]
      omega
    have hBsub : B ⊆ box := by rw [hB]; exact Finset.sdiff_subset
    obtain ⟨a₁, a₂, b₁, b₂, hin1, hin2, hne, ha1, ha2, hb1, hb2, hdvd⟩ :=
      pigeon B hBsub hBcard
    refine ⟨(a₁ : ℤ) - a₂, (b₁ : ℤ) - b₂, ?_, hdvd, ?_⟩
    · intro hzero
      rw [Prod.mk.injEq] at hzero
      apply hne
      rw [Prod.mk.injEq]; exact ⟨by omega, by omega⟩
    · have hx2le : ((a₁ : ℤ) - a₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (a₁ : ℤ) - a₂ by omega,
          show (a₁ : ℤ) - a₂ ≤ (m : ℤ) by omega]
      have hy2le : ((b₁ : ℤ) - b₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (b₁ : ℤ) - b₂ by omega,
          show (b₁ : ℤ) - b₂ ≤ (m : ℤ) by omega]
      have hmm : (m : ℤ) ^ 2 = (p : ℤ) := by
        have : m ^ 2 = p := by rw [pow_two]; exact hsq
        exact_mod_cast this
      -- no surviving corner: at least one coordinate is strictly inside
      have hnot : ¬ (((a₁ = m ∧ a₂ = 0) ∨ (a₁ = 0 ∧ a₂ = m)) ∧
          ((b₁ = m ∧ b₂ = 0) ∨ (b₁ = 0 ∧ b₂ = m))) := by
        rintro ⟨ha, hb⟩
        rcases ha with ⟨ha1', ha2'⟩ | ⟨ha1', ha2'⟩ <;>
          rcases hb with ⟨hb1', hb2'⟩ | ⟨hb1', hb2'⟩ <;>
            subst_vars <;>
              simp_all [hB, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
                Prod.mk.injEq]
      have key : ((a₁ : ℤ) - a₂) ^ 2 < (m : ℤ) ^ 2 ∨ ((b₁ : ℤ) - b₂) ^ 2 < (m : ℤ) ^ 2 := by
        by_contra hc
        push_neg at hc
        have hx2 : ((a₁ : ℤ) - a₂) ^ 2 = (m : ℤ) ^ 2 := le_antisymm hx2le hc.1
        have hy2 : ((b₁ : ℤ) - b₂) ^ 2 = (m : ℤ) ^ 2 := le_antisymm hy2le hc.2
        have hx0 : (((a₁ : ℤ) - a₂) - m) * (((a₁ : ℤ) - a₂) + m) = 0 := by linear_combination hx2
        have hy0 : (((b₁ : ℤ) - b₂) - m) * (((b₁ : ℤ) - b₂) + m) = 0 := by linear_combination hy2
        apply hnot
        refine ⟨?_, ?_⟩
        · rcases mul_eq_zero.mp hx0 with h | h
          · left; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
        · rcases mul_eq_zero.mp hy0 with h | h
          · left; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
      rcases key with h | h
      · nlinarith [h, hy2le, hmm]
      · nlinarith [h, hx2le, hmm]
  · -- p not a perfect square: m*m < p, so the plain box already gives the strict bound
    have hmm_lt : m * m < p := lt_of_le_of_ne hle hsq
    obtain ⟨a₁, a₂, b₁, b₂, hin1, hin2, hne, ha1, ha2, hb1, hb2, hdvd⟩ :=
      pigeon box (le_refl box) (by rw [hbox_card]; exact hlt)
    refine ⟨(a₁ : ℤ) - a₂, (b₁ : ℤ) - b₂, ?_, hdvd, ?_⟩
    · intro hzero
      rw [Prod.mk.injEq] at hzero
      apply hne
      rw [Prod.mk.injEq]; exact ⟨by omega, by omega⟩
    · have hx2le : ((a₁ : ℤ) - a₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (a₁ : ℤ) - a₂ by omega,
          show (a₁ : ℤ) - a₂ ≤ (m : ℤ) by omega]
      have hy2le : ((b₁ : ℤ) - b₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (b₁ : ℤ) - b₂ by omega,
          show (b₁ : ℤ) - b₂ ≤ (m : ℤ) by omega]
      have hmm : (m : ℤ) ^ 2 < (p : ℤ) := by
        have : m ^ 2 < p := by rw [pow_two]; exact hmm_lt
        exact_mod_cast this
      nlinarith [hx2le, hy2le, hmm]

/-! ### Measure-theoretic machinery for the `d = 2` slice point

A self-contained 2D port of the axiom-free `dirichlet_approximation`
(`MinkowskiTheoremOQ02OQ01.lean`) and `dirichletEllipsoid_volume`
(`ThreeSquares.lean`).  We apply Minkowski's strict convex-body theorem to the
*sheared* closed ellipse `sliceEllipse p r R = {v | (p*v0 + r*v1)^2 + 2*v1^2 <= R}`
on the standard `ℤ²` lattice (covolume `1`).  Two volume facts combine:
`axisEllipse2_volume` (the axis-aligned ellipse `{w | w0^2 + 2*w1^2 <= R}` has
volume `R*π/√2`, via the diagonal scaling `diag(√R, √(R/2))`) and the shear change
of variables (`map_matrix_volume_pi_eq_smul_volume_pi`, `|det| = p`), giving
`vol(sliceEllipse p r R) = R*π/(√2*p)`.  Taking `R = 19p/10 ∈ (4√2 p/π, 2p)`
makes the volume `19π/(10√2) > 4` so Minkowski yields a nonzero integer point,
and `R < 2p` upgrades the resulting `≤ R` to the strict `< 2p` target. -/

/-- Axis-aligned closed ellipse `{w | w0^2 + 2*w1^2 <= R}` in `Fin 2 → ℝ`. -/
private def axisEllipse2 (R : ℝ) : Set (Fin 2 → ℝ) :=
  {v | v 0 ^ 2 + 2 * v 1 ^ 2 ≤ R}

/-- Diagonal scaling `diag(√R, √(R/2))`. -/
private noncomputable def scale2Matrix (R : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![Real.sqrt R, Real.sqrt (R / 2)]

private noncomputable def scale2 (R : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' (scale2Matrix R)

private lemma scale2_apply (R : ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    (scale2 R v) i = ![Real.sqrt R, Real.sqrt (R / 2)] i * v i := by
  unfold scale2 scale2Matrix
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]

private lemma scale2_det (R : ℝ) (hR : 0 ≤ R) :
    LinearMap.det (scale2 R) = R / Real.sqrt 2 := by
  unfold scale2 scale2Matrix
  rw [LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← Real.sqrt_mul hR, show R * (R / 2) = R ^ 2 / 2 by ring,
      Real.sqrt_div (by positivity : (0 : ℝ) ≤ R ^ 2), Real.sqrt_sq hR]

/-- The unit ball `{v | v0^2 + v1^2 <= 1}` as a set in `Fin 2 → ℝ`. -/
private def unitBall2 : Set (Fin 2 → ℝ) := {v | v 0 ^ 2 + v 1 ^ 2 ≤ 1}

private lemma axisEllipse2_eq_image (R : ℝ) (hR : 0 < R) :
    axisEllipse2 R = (scale2 R) '' unitBall2 := by
  have hR2 : (0 : ℝ) < R / 2 := by positivity
  have hsqrtR : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR.le
  have hsqrtR2 : Real.sqrt (R / 2) * Real.sqrt (R / 2) = R / 2 := Real.mul_self_sqrt hR2.le
  have hsqrtR_ne : Real.sqrt R ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hR)
  have hsqrtR2_ne : Real.sqrt (R / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hR2)
  ext v
  simp only [axisEllipse2, unitBall2, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro hv
    refine ⟨![v 0 / Real.sqrt R, v 1 / Real.sqrt (R / 2)], ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have h0 : (v 0 / Real.sqrt R) ^ 2 = v 0 ^ 2 / R := by
        rw [div_pow]; congr 1; rw [sq]; exact hsqrtR
      have h1 : (v 1 / Real.sqrt (R / 2)) ^ 2 = v 1 ^ 2 / (R / 2) := by
        rw [div_pow]; congr 1; rw [sq]; exact hsqrtR2
      rw [h0, h1, show v 0 ^ 2 / R + v 1 ^ 2 / (R / 2)
            = (v 0 ^ 2 + 2 * v 1 ^ 2) / R by field_simp; ring, div_le_one hR]
      exact hv
    · ext i
      rw [scale2_apply]
      fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hsqrtR_ne,
          hsqrtR2_ne, mul_div_cancel₀]
  · rintro ⟨u, hu, rfl⟩
    simp only [scale2_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have e0 : (Real.sqrt R * u 0) ^ 2 = R * u 0 ^ 2 := by rw [mul_pow, Real.sq_sqrt hR.le]
    have e1 : (Real.sqrt (R / 2) * u 1) ^ 2 = (R / 2) * u 1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR2.le]
    rw [e0, e1]
    nlinarith [mul_le_mul_of_nonneg_left hu hR.le]

private lemma unitBall2_measurableSet : MeasurableSet unitBall2 := by
  unfold unitBall2
  refine measurableSet_le (Measurable.add ?_ ?_) measurable_const
  · exact (measurable_pi_apply 0).pow_const 2
  · exact (measurable_pi_apply 1).pow_const 2

private lemma unitBall2_preimage :
    (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' unitBall2 =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  ext x
  simp only [Set.mem_preimage, unitBall2, Set.mem_setOf_eq, Metric.mem_closedBall,
    dist_zero_right]
  have h_norm_sq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [sq_abs]
  have hnn : 0 ≤ ‖x‖ := norm_nonneg _
  constructor
  · intro hv
    have h_sq : ‖x‖ ^ 2 ≤ 1 := h_norm_sq.trans_le hv
    nlinarith
  · intro hx
    have h_sq : ‖x‖ ^ 2 ≤ 1 := by nlinarith
    rw [h_norm_sq] at h_sq
    exact h_sq

open MeasureTheory in
private lemma unitBall2_volume :
    volume unitBall2 = ENNReal.ofReal Real.pi := by
  rw [← (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
        unitBall2_measurableSet.nullMeasurableSet,
    unitBall2_preimage, EuclideanSpace.volume_closedBall_fin_two]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]

open MeasureTheory in
private lemma axisEllipse2_volume (R : ℝ) (hR : 0 < R) :
    volume (axisEllipse2 R) = ENNReal.ofReal (R / Real.sqrt 2 * Real.pi) := by
  have hdet_nn : (0 : ℝ) ≤ R / Real.sqrt 2 := div_nonneg hR.le (Real.sqrt_nonneg 2)
  rw [axisEllipse2_eq_image R hR, MeasureTheory.Measure.addHaar_image_linearMap,
      scale2_det R hR.le, unitBall2_volume, abs_of_nonneg hdet_nn,
      ← ENNReal.ofReal_mul hdet_nn]

/-- The shear matrix `!![p, r; 0, 1]` (determinant `p`). -/
private noncomputable def shear2Matrix (p : ℕ) (r : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(p : ℝ), (r : ℝ); 0, 1]

private noncomputable def shear2 (p : ℕ) (r : ℤ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' (shear2Matrix p r)

private lemma shear2_det (p : ℕ) (r : ℤ) : (shear2Matrix p r).det = (p : ℝ) := by
  simp [shear2Matrix, Matrix.det_fin_two]

private lemma shear2_apply0 (p : ℕ) (r : ℤ) (v : Fin 2 → ℝ) :
    (shear2 p r v) 0 = (p : ℝ) * v 0 + (r : ℝ) * v 1 := by
  simp [shear2, shear2Matrix, Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two, dotProduct]

private lemma shear2_apply1 (p : ℕ) (r : ℤ) (v : Fin 2 → ℝ) :
    (shear2 p r v) 1 = v 1 := by
  simp [shear2, shear2Matrix, Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two, dotProduct]

/-- The sheared closed ellipse `{v | (p*v0 + r*v1)^2 + 2*v1^2 <= R}`. -/
private def sliceEllipse (p : ℕ) (r : ℤ) (R : ℝ) : Set (Fin 2 → ℝ) :=
  {v | ((p : ℝ) * v 0 + (r : ℝ) * v 1) ^ 2 + 2 * (v 1) ^ 2 ≤ R}

private lemma sliceEllipse_eq_preimage (p : ℕ) (r : ℤ) (R : ℝ) :
    sliceEllipse p r R = (shear2 p r) ⁻¹' (axisEllipse2 R) := by
  ext v
  simp only [sliceEllipse, axisEllipse2, Set.mem_preimage, Set.mem_setOf_eq,
    shear2_apply0, shear2_apply1]

open MeasureTheory in
private lemma sliceEllipse_volume (p : ℕ) (r : ℤ) (hp : 0 < p) (R : ℝ) (hR : 0 < R) :
    volume (sliceEllipse p r R) = ENNReal.ofReal (R / Real.sqrt 2 * Real.pi / p) := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := hppos.ne'
  have hs2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hdet_ne : (shear2Matrix p r).det ≠ 0 := by rw [shear2_det]; exact hpne
  have hmeas_axis : MeasurableSet (axisEllipse2 R) := by
    unfold axisEllipse2
    refine measurableSet_le (Measurable.add ?_ ?_) measurable_const
    · exact (measurable_pi_apply 0).pow_const 2
    · exact ((measurable_pi_apply 1).pow_const 2).const_mul 2
  have hmeas_shear : Measurable (shear2 p r) :=
    (LinearMap.continuous_on_pi (shear2 p r)).measurable
  rw [sliceEllipse_eq_preimage, ← Measure.map_apply hmeas_shear hmeas_axis,
      show (shear2 p r) = Matrix.toLin' (shear2Matrix p r) from rfl,
      map_matrix_volume_pi_eq_smul_volume_pi hdet_ne, Measure.smul_apply, smul_eq_mul,
      axisEllipse2_volume R hR, shear2_det,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ)⁻¹),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (p : ℝ)⁻¹)]
  congr 1
  field_simp
  ring


/-- **The `d = 2` slice point (PROVED — build-pending verification).**

For any `p > 0` and any `r : ℤ`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` contains a nonzero vector with `x² + 2y² < 2p`.

Unlike `d = 1`, the integer box `|x|, |y| ≤ ⌊√p⌋` does NOT suffice: the binary
form `x² + 2y²` has Hermite ratio `(2/√3)·√2 ≈ 1.633`, and `verify_slice_minkowski.py`
exhibits 394 `(p, r)` cases where every box point has `x² + 2y² ≥ 2p`. The proof
genuinely requires Minkowski's strict convex-body theorem on the ellipse
`x² + 2y² < 2p` (open, area `√2·π·p`); no elementary box/pigeonhole reduction works
(the best box bound is `2√2·p > 2p`, and the strict small-ellipse count
`#{x²+2y² < p/2} > p` fails for many `p` — both ruled out numerically, S-2026-06-18).
This is the sole remaining `sorry` in the three-squares development.

**TURNKEY RECIPE (researcher-12, 2026-06-18 — pinned, build-pending).** The clean
route is a near-verbatim port of the proved, axiom-free `dirichlet_approximation`
(`MinkowskiTheoremOQ02OQ01.lean:161`): keep the STANDARD lattice `ℤ²` (covolume `1`,
basis `Pi.basisFun ℝ (Fin 2)`) and shear the *set*, rather than building a
covolume-`p` sublattice. Concretely:

  * Let `S = !![(p:ℝ), r; 0, 1]` (det `= p`) and define the sheared open set
    `E' := { v : Fin 2 → ℝ | (p·v 0 + r·v 1)^2 + 2·(v 1)^2 < 2*p }`,
    i.e. `E' = S ⁻¹' E` where `E = {w | w 0 ^2 + 2·w 1 ^2 < 2p}` is the axis-aligned
    open ellipse.
  * `E'` is symmetric and convex (preimage of the symmetric convex `E` under the
    linear `S`; reuse the quadratic-form convexity argument of
    `dirichletEllipsoid_convex`, `ThreeSquares.lean`).
  * **Volume is `p`-INDEPENDENT**: `vol(E') = vol(E)/|det S| = (√2·π·p)/p = √2·π
    ≈ 4.443 > 4 = 2²·covol(ℤ²)`, so Minkowski's hypothesis holds for *every* `p`
    with a fixed margin. Compute `vol(E')` exactly as `dirichletSet_volume`
    (`MinkowskiTheoremOQ02OQ01.lean:96`) does — via `Measure.map S volume` and
    `map_matrix_volume_pi_eq_smul_volume_pi` — feeding in `vol(E) = √2·π·p` (the 2D
    analog of `dirichletEllipsoid_volume`, `ThreeSquares.lean`: ellipse `= T '' ball`
    with `T = diag(√(2p), √p)`, `EuclideanSpace.volume_ball` in dim 2 `= π`).
  * Apply `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` to `ℤ²`,
    `E'`, exactly as in `dirichlet_approximation` (same `ZSpan.isAddFundamentalDomain'`,
    `Module.finrank_fin_fun`, coordinate-extraction block lines 188–215).
  * The returned nonzero integer `(a, b)` gives the slice point
    `(x, y) := (a·p + b·r, b)`: then `x - r·y = a·p` so `(p:ℤ) ∣ (x - r·y)`
    automatically, `(x,y) ≠ (0,0)` since `(a,b) ≠ 0` (if `b = 0` then `x = a·p ≠ 0`),
    and `x² + 2y² < 2p` is exactly membership in `E'`. (Numerically validated for all
    `p < 400`, all `r`.)

This is a KNOWN result (Minkowski applied to a binary form) — an ideal Aristotle
target once the backend recovers; it was build/Aristotle-gated this session. -/
theorem exists_slice_point_lt_two_mul_d2
    (p : ℕ) (hp : 0 < p) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + 2 * y ^ 2 < 2 * p := by
  classical
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  set R : ℝ := 19 * (p : ℝ) / 10 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  let b := Pi.basisFun ℝ (Fin 2)
  haveI hcount : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b)); infer_instance
  have h_fund := ZSpan.isAddFundamentalDomain' b MeasureTheory.volume
  have h_vol_fund : MeasureTheory.volume (ZSpan.fundamentalDomain b) = 1 := by
    have hmat : (Matrix.of b).det = 1 := by
      have hbeq : Matrix.of b = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext i j
        change (Matrix.of (Pi.basisFun ℝ (Fin 2))) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
        simp [Matrix.of_apply, Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
      simp [hbeq]
    rw [ZSpan.volume_fundamentalDomain, hmat, abs_one, ENNReal.ofReal_one]
  have h_symm : ∀ v ∈ sliceEllipse p r R, -v ∈ sliceEllipse p r R := by
    intro v hv
    simp only [sliceEllipse, Set.mem_setOf_eq, Pi.neg_apply] at hv ⊢
    rw [show (p : ℝ) * -v 0 + (r : ℝ) * -v 1 = -((p : ℝ) * v 0 + (r : ℝ) * v 1) by ring,
        neg_sq, neg_sq]
    exact hv
  have h_conv : Convex ℝ (sliceEllipse p r R) := by
    intro x hx y hy a c ha hc hac
    simp only [sliceEllipse, Set.mem_setOf_eq] at hx hy ⊢
    have sq_convex : ∀ u w : ℝ, (a * u + c * w) ^ 2 ≤ a * u ^ 2 + c * w ^ 2 := by
      intro u w
      have key : a * u ^ 2 + c * w ^ 2 - (a * u + c * w) ^ 2 = a * c * (u - w) ^ 2 := by
        have h1 : c = 1 - a := by linarith
        rw [h1]; ring
      nlinarith [mul_nonneg (mul_nonneg ha hc) (sq_nonneg (u - w))]
    have hc0 := sq_convex ((p : ℝ) * x 0 + (r : ℝ) * x 1) ((p : ℝ) * y 0 + (r : ℝ) * y 1)
    have hc1 := sq_convex (x 1) (y 1)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc ((p : ℝ) * (a * x 0 + c * y 0) + (r : ℝ) * (a * x 1 + c * y 1)) ^ 2
            + 2 * (a * x 1 + c * y 1) ^ 2
        = (a * ((p : ℝ) * x 0 + (r : ℝ) * x 1) + c * ((p : ℝ) * y 0 + (r : ℝ) * y 1)) ^ 2
            + 2 * (a * x 1 + c * y 1) ^ 2 := by ring
      _ ≤ (a * ((p : ℝ) * x 0 + (r : ℝ) * x 1) ^ 2 + c * ((p : ℝ) * y 0 + (r : ℝ) * y 1) ^ 2)
            + 2 * (a * x 1 ^ 2 + c * y 1 ^ 2) := by gcongr
      _ = a * (((p : ℝ) * x 0 + (r : ℝ) * x 1) ^ 2 + 2 * x 1 ^ 2)
            + c * (((p : ℝ) * y 0 + (r : ℝ) * y 1) ^ 2 + 2 * y 1 ^ 2) := by ring
      _ ≤ a * R + c * R := by gcongr
      _ = R := by rw [← add_mul, hac, one_mul]
  have hval : R / Real.sqrt 2 * Real.pi / p = 19 * Real.pi / (10 * Real.sqrt 2) := by
    have hs2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hpne : (p : ℝ) ≠ 0 := hppos.ne'
    rw [hRdef]; field_simp; ring
  have hgt : (4 : ℝ) < R / Real.sqrt 2 * Real.pi / p := by
    rw [hval, lt_div_iff₀ (by positivity : (0 : ℝ) < 10 * Real.sqrt 2)]
    have hsqrt_lt : Real.sqrt 2 < 1.425 := by
      have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [hs2, Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 1.425)]
    have h1 : 4 * (10 * Real.sqrt 2) < 57 := by linarith [hsqrt_lt]
    have h2 : (57 : ℝ) ≤ 19 * Real.pi := by linarith [Real.pi_gt_three]
    linarith
  have hpos : 0 < R / Real.sqrt 2 * Real.pi / p := by rw [hval]; positivity
  have h_vol_cond : MeasureTheory.volume (ZSpan.fundamentalDomain b)
      * 2 ^ Module.finrank ℝ (Fin 2 → ℝ)
      < MeasureTheory.volume (sliceEllipse p r R) := by
    rw [h_vol_fund, one_mul, Module.finrank_fin_fun, sliceEllipse_volume p r hp R hRpos]
    calc (2 : ENNReal) ^ 2 = ENNReal.ofReal 4 := by norm_num
      _ < ENNReal.ofReal (R / Real.sqrt 2 * Real.pi / p) :=
          (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hgt
  obtain ⟨⟨x_val, hx_mem⟩, hx_ne, hx_S⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      h_fund h_symm h_conv h_vol_cond
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun] at hx_mem
  obtain ⟨cc, hcc⟩ := hx_mem
  have hb00 : b 0 0 = 1 := by change Pi.basisFun ℝ (Fin 2) 0 0 = 1; simp [Pi.basisFun_apply]
  have hb10 : b 1 0 = 0 := by change Pi.basisFun ℝ (Fin 2) 1 0 = 0; simp [Pi.basisFun_apply]
  have hb01 : b 0 1 = 0 := by change Pi.basisFun ℝ (Fin 2) 0 1 = 0; simp [Pi.basisFun_apply]
  have hb11 : b 1 1 = 1 := by change Pi.basisFun ℝ (Fin 2) 1 1 = 1; simp [Pi.basisFun_apply]
  have ha : x_val 0 = (cc 0 : ℝ) := by
    have h0 := congr_fun hcc 0
    rw [Fin.sum_univ_two] at h0
    simp only [Pi.add_apply, Pi.smul_apply, hb00, hb10, zsmul_eq_mul, mul_one, smul_zero,
      mul_zero, add_zero] at h0
    exact h0.symm
  have hb' : x_val 1 = (cc 1 : ℝ) := by
    have h1 := congr_fun hcc 1
    rw [Fin.sum_univ_two] at h1
    simp only [Pi.add_apply, Pi.smul_apply, hb01, hb11, zsmul_eq_mul, mul_one, smul_zero,
      mul_zero, zero_add] at h1
    exact h1.symm
  simp only [sliceEllipse, Set.mem_setOf_eq] at hx_S
  rw [ha, hb'] at hx_S
  refine ⟨(p : ℤ) * cc 0 + r * cc 1, cc 1, ?_, ?_, ?_⟩
  · intro hcontra
    rw [Prod.mk.injEq] at hcontra
    obtain ⟨hX, hY⟩ := hcontra
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    have hcc0 : cc 0 = 0 := by
      rw [hY, mul_zero, add_zero] at hX
      exact (mul_eq_zero.mp hX).resolve_left hpz
    apply hx_ne
    apply Subtype.ext
    funext i
    fin_cases i
    · show x_val 0 = 0; rw [ha, hcc0]; norm_num
    · show x_val 1 = 0; rw [hb', hY]; norm_num
  · exact ⟨cc 0, by ring⟩
  · have hReal : ((p : ℝ) * (cc 0 : ℝ) + (r : ℝ) * (cc 1 : ℝ)) ^ 2 + 2 * ((cc 1 : ℝ)) ^ 2 ≤ R :=
      hx_S
    have hR2p : R < 2 * (p : ℝ) := by
      rw [hRdef, div_lt_iff₀ (by norm_num : (0 : ℝ) < 10)]; linarith [hppos]
    have hlt : ((p : ℝ) * (cc 0 : ℝ) + (r : ℝ) * (cc 1 : ℝ)) ^ 2 + 2 * ((cc 1 : ℝ)) ^ 2
        < 2 * (p : ℝ) := lt_of_le_of_lt hReal hR2p
    have hgoalR : ((((p : ℤ) * cc 0 + r * cc 1) ^ 2 + 2 * (cc 1) ^ 2 : ℤ) : ℝ)
        < (((2 * (p : ℤ)) : ℤ) : ℝ) := by push_cast; nlinarith [hlt]
    exact_mod_cast hgoalR


/-- **The missing `Q < 2p` step (2D slice).**

For `d ∈ {1, 2}` and any `p > 0`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` of `ℤ²` contains a nonzero vector on which the
binary form `x² + d·y²` is strictly below `2p`.

This is the remaining open input to `dirichlet_key_lemma` in
`Proofs/ThreeSquares.lean`. The `d = 1` case is fully proved
(`exists_slice_point_lt_two_mul_d1`); the `d = 2` case
(`exists_slice_point_lt_two_mul_d2`) is now proved in source (build-pending). -/
theorem exists_slice_point_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p := by
  interval_cases d
  · obtain ⟨x, y, h1, h2, h3⟩ := exists_slice_point_lt_two_mul_d1 p hp r
    exact ⟨x, y, h1, h2, by simpa using h3⟩
  · obtain ⟨x, y, h1, h2, h3⟩ := exists_slice_point_lt_two_mul_d2 p hp r
    exact ⟨x, y, h1, h2, by simpa using h3⟩

/-- **Bridge (proved): 2D slice point → Dirichlet sublattice vector.**

Lifts a 2D slice point `(x, y)` with `p ∣ (x − r·y)` and `x² + d·y² < 2p` to the
`Fin 3 → ℤ` vector `![x, y, 0]`. The third coordinate `0` makes the second
sublattice condition `p ∣ v 2` automatic, and the ternary form
`v 0² + d·v 1² + d·v 2²` collapses to the binary `x² + d·y²`. This is exactly the
input shape of `dirichletForm_dvd_of_in_sublattice` and
`dirichletForm_eq_p_of_lt_two_mul` (`ThreeSquares.lean`).

No geometry of numbers here — pure plumbing, so it is fully proved. -/
theorem slice_point_to_dirichlet_vector
    (p d : ℕ) (r x y : ℤ)
    (hxy : (x, y) ≠ (0, 0))
    (hdvd : (p : ℤ) ∣ (x - r * y))
    (hlt : x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧
      ((p : ℤ) ∣ (v 0 - r * v 1) ∧ (p : ℤ) ∣ v 2) ∧
      v 0 ^ 2 + (d : ℤ) * v 1 ^ 2 + (d : ℤ) * v 2 ^ 2 < 2 * p := by
  refine ⟨![x, y, 0], ?_, ⟨?_, ?_⟩, ?_⟩
  · -- ![x, y, 0] ≠ 0 since (x, y) ≠ (0, 0)
    intro h
    apply hxy
    have hx : x = 0 := by have := congrFun h 0; simpa using this
    have hy : y = 0 := by have := congrFun h 1; simpa using this
    simp [hx, hy]
  · simpa using hdvd
  · simp
  · simpa using hlt

/-- **Assembled existence**: composing the 2D Minkowski bound with the (proved)
bridge gives directly the `Fin 3 → ℤ` lattice point that `dirichlet_key_lemma`
consumes. Sorry-free once `exists_slice_point_lt_two_mul_d2` is closed. -/
theorem exists_dirichlet_vector_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧
      ((p : ℤ) ∣ (v 0 - r * v 1) ∧ (p : ℤ) ∣ v 2) ∧
      v 0 ^ 2 + (d : ℤ) * v 1 ^ 2 + (d : ℤ) * v 2 ^ 2 < 2 * p := by
  obtain ⟨x, y, hxy, hdvd, hlt⟩ := exists_slice_point_lt_two_mul p d hp hd hd2 r
  exact slice_point_to_dirichlet_vector p d r x y hxy hdvd hlt

end ThreeSquaresSlice
