/-
Aristotle target for `feuerbachs-theorem-oq-02-murakami` (step S10).

DISCHARGE TARGET for the lone axiom of the parent file
`proofs/Proofs/FeuerbachsTheoremOQ02.lean`:

    axiom feuerbach_3d_fails_general :
        ∃ T : Tetrahedron,
          (dot3 (vec3 T.A T.B) (vec3 T.C T.D) ≠ 0) ∧            -- non-orthocentric
          ¬ spheresInternallyTangent T.twentyFourPointCenter T.incenter
              T.twentyFourPointRadius T.inradius                -- 24-pt sphere NOT
                                                                -- tangent to insphere

The axiom asserts that the 3D "Feuerbach" tangency (twenty-four-point sphere
internally tangent to the insphere) can FAIL for a non-orthocentric
tetrahedron — i.e. orthocentricity is genuinely necessary. Prior slug
refutations (the trirectangular T0 and the regular tetrahedron) are ALL
orthocentric (dot3(AB,CD) = 0), so none of them witness this axiom; a
non-orthocentric witness is required.

EXPLICIT WITNESS (this file): T1 with
    A = (0,0,0),  B = (1,0,0),  C = (0,1,0),  D = (1,1,1).

Exact quantities (sympy-certified, see
`proofs/scripts/verify_feuerbach3d_fails_witness_exact.py`):
  • signedVolume6 = 1               (nondegenerate)
  • dot3(AB,CD) = 1 ≠ 0             (non-orthocentric: AB=(1,0,0), CD=(1,0,1))
  • circumcenter O = (1/2,1/2,1/2),  R = √3/2,  twentyFourPointRadius = √3/6
  • centroid G = (1/2,1/2,1/4),  mongePoint M = 4G−3O = (1/2,1/2,−1/2)
  • twentyFourPointCenter N₂₄ = midpoint(O,M) = (1/2,1/2,0)   ← RATIONAL
  • faceAreas = (√3/2, √2/2, √2/2, 1/2),  surfaceArea S = (1+√3+2√2)/2
  • inradius r = 3V/S = 1/(1+√3+2√2),  incenter
        I = ((1+√2)/Δ, (1+√2)/Δ, 1/Δ),   Δ = 1+√3+2√2
  • dist(N₂₄,I)² = (3−√3)/Δ²,   (R/3 − r)² = (−3+√3+2√6)²/(36 Δ²)

NON-TANGENCY ⇔ dist(N₂₄,I) ≠ |R/3 − r|.  Both sides are ≥ 0, so it suffices
to separate the squares.  Clearing the common factor 36 Δ² > 0:

    36 Δ² · dist(N₂₄,I)²  −  36 Δ² · (R/3 − r)²
      = 36(3−√3) − (−3+√3+2√6)²
      = 72 − 30√3 − 12√2 + 12√6                       (≈ 32.4618 ≠ 0).

So the WHOLE discharge reduces to the three-surd inequality

    72 − 30√3 − 12√2 + 12√6 ≠ 0       (in fact > 0).

This is the sharp, sqrt-free-after-squaring target.  It is now CLOSED below
(`witnessT1_surd_separation`) by the rational separating bounds
√3 < 1.7321, √2 < 1.41422, √6 > 2.4494, each obtained from the squared
identity `Real.sq_sqrt` plus `Real.sqrt_nonneg` via `nlinarith` (the negated
goal multiplied by `0 ≤ √·` yields the matching one-sided bound), then
`linarith` for positivity.  No `Real.sqrt_lt'`/`Real.lt_sqrt` iff-lemma is
needed.

SORRY-FREE (S11): `witnessT1_fails` is now fully discharged.  The non-tangency
is reduced to the proven surd kernel by transcribing the closed forms of all
four invariants at T1 as separate lemmas:
  • `witnessT1_faceArea_{A,B,C,D}`  = (√3/2, √2/2, √2/2, 1/2)
  • `witnessT1_volume`              = 1/6
  • `witnessT1_surfaceArea`         = (1+√3+2√2)/2
  • `witnessT1_inradius`            = 1/(1+√3+2√2)
  • `witnessT1_circumcenter`        = (1/2,1/2,1/2)   (rational, via Cramer)
  • `witnessT1_circumradius`        = √3/2
  • `witnessT1_twentyFourPointRadius` = √3/6
  • `witnessT1_twentyFourPointCenter` = (1/2,1/2,0)   (rational)
  • `witnessT1_incenter`            = ((1+√2)/Δ, (1+√2)/Δ, 1/Δ)
The non-tangency `dist(N₂₄,I) = |R/3 − r|` is squared (`dist3_sq_eq`, `sq_abs`),
both sides put over the common denominator `36 Δ²` as pure RATIONAL identities
(no surd-square needed: `field_simp; ring`), and the strict separation
`(bΔ−6)² < 18((1−b)²+2)` is the exact polynomial identity `hid` modulo
`a²=2, b²=3` (a=√2, b=√3) plus the numeric bounds √2<1.41422, √3<1.7321,
√6>2.4494 — i.e. the same `72−30√3−12√2+12√6 > 0` kernel as
`witnessT1_surd_separation`.  `feuerbach_3d_fails_general_proved` then discharges
the parent existence axiom outright.

BUILD-PENDING — authored under a Docker + Aristotle blackout, so NOT yet
compiler-checked; every algebraic identity is sympy-certified in
`proofs/scripts/verify_feuerbach3d_fails_witness_exact.py` (ALL CHECKS PASS,
including the S11 Lean-shaped intermediate identities `hd`, `he`, `hid`).  This
file does NOT touch the registered parent file and is NOT itself registered in
`Proofs.lean`, so it cannot affect the gallery build.  Once green, the parent
axiom `feuerbach_3d_fails_general` can be replaced by
`feuerbach_3d_fails_general_proved` (axiom elimination).
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ02

set_option maxHeartbeats 1000000

open scoped Real

namespace FeuerbachsTheoremOQ02

/-- The explicit non-orthocentric witness tetrahedron T1. -/
def witnessT1 : Tetrahedron where
  A := (0, 0, 0)
  B := (1, 0, 0)
  C := (0, 1, 0)
  D := (1, 1, 1)
  nondegenerate := by norm_num [vec3, dot3, cross3]

/-- The squared-separation core: the genuinely hard content of the discharge,
isolated as a self-contained three-surd inequality (see the file header for
the reduction).  `Δ = 1+√3+2√2 > 0`, so this is equivalent to
`dist(N₂₄,I)² ≠ (R/3 − r)²`. -/
theorem witnessT1_surd_separation :
    (72 : ℝ) - 30 * Real.sqrt 3 - 12 * Real.sqrt 2 + 12 * Real.sqrt 6 ≠ 0 := by
  -- The expression is in fact strictly positive (≈ 32.4618), so it is ≠ 0.
  -- Rational separating bounds (each verified by the squared identity + nonneg):
  --   √3 < 1.7321   (1.7321² = 3.00017… > 3)
  --   √2 < 1.41422  (1.41422² = 2.00002… > 2)
  --   √6 > 2.4494   (2.4494² = 5.99956… < 6)
  -- giving 72 − 30√3 − 12√2 + 12√6 > 72 − 51.963 − 16.97064 + 29.3928 ≈ 32.459 > 0.
  have h3 : Real.sqrt 3 < 1.7321 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h2 : Real.sqrt 2 < 1.41422 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h6 : (2.4494 : ℝ) < Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6), Real.sqrt_nonneg 6]
  have hpos : (0 : ℝ) < 72 - 30 * Real.sqrt 3 - 12 * Real.sqrt 2 + 12 * Real.sqrt 6 := by
    linarith
  exact ne_of_gt hpos

/-- The non-orthocentric conjunct of the witness, discharged outright.
`vec3 A B = (1,0,0)`, `vec3 C D = (1,0,1)`, so `dot3 = 1 ≠ 0` — a pure rational
computation (same `norm_num [vec3, dot3, …]` pattern as `witnessT1.nondegenerate`),
needing none of the surd-laden tangency definitions. This is the easy half of
`witnessT1_fails`; the non-tangency half is now also discharged (S11), so the
whole file is sorry-free. -/
theorem witnessT1_nonorthocentric :
    dot3 (vec3 witnessT1.A witnessT1.B) (vec3 witnessT1.C witnessT1.D) ≠ 0 := by
  norm_num [witnessT1, vec3, dot3]

-- ============================================================
-- Closed forms of the surd-laden invariants at T1 (S11).
-- Each is sympy-certified in verify_feuerbach3d_fails_witness_exact.py.
-- ============================================================

/-- Face areas of T1: (√3/2, √2/2, √2/2, 1/2). -/
theorem witnessT1_faceArea_A : witnessT1.faceArea_A = Real.sqrt 3 / 2 := by
  norm_num [Tetrahedron.faceArea_A, witnessT1, vec3, cross3, dot3]

theorem witnessT1_faceArea_B : witnessT1.faceArea_B = Real.sqrt 2 / 2 := by
  norm_num [Tetrahedron.faceArea_B, witnessT1, vec3, cross3, dot3]

theorem witnessT1_faceArea_C : witnessT1.faceArea_C = Real.sqrt 2 / 2 := by
  norm_num [Tetrahedron.faceArea_C, witnessT1, vec3, cross3, dot3]

theorem witnessT1_faceArea_D : witnessT1.faceArea_D = 1 / 2 := by
  norm_num [Tetrahedron.faceArea_D, witnessT1, vec3, cross3, dot3]

/-- Volume of T1 is 1/6 (signed volume 6 = 1). -/
theorem witnessT1_volume : witnessT1.volume = 1 / 6 := by
  norm_num [Tetrahedron.volume, Tetrahedron.signedVolume6, witnessT1, vec3, dot3, cross3]

/-- Surface area S = (1 + √3 + 2√2)/2. -/
theorem witnessT1_surfaceArea :
    witnessT1.surfaceArea = (1 + Real.sqrt 3 + 2 * Real.sqrt 2) / 2 := by
  rw [Tetrahedron.surfaceArea, witnessT1_faceArea_A, witnessT1_faceArea_B,
    witnessT1_faceArea_C, witnessT1_faceArea_D]
  ring

/-- Inradius r = 3V/S = 1/(1+√3+2√2). -/
theorem witnessT1_inradius :
    witnessT1.inradius = 1 / (1 + Real.sqrt 3 + 2 * Real.sqrt 2) := by
  have hpos : (0 : ℝ) < 1 + Real.sqrt 3 + 2 * Real.sqrt 2 := by positivity
  rw [Tetrahedron.inradius, witnessT1_volume, witnessT1_surfaceArea]
  field_simp
  ring

/-- Circumcenter O = (1/2, 1/2, 1/2) (rational; via Cramer with det = 1). -/
theorem witnessT1_circumcenter : witnessT1.circumcenter = (1 / 2, 1 / 2, 1 / 2) := by
  simp only [Tetrahedron.circumcenter, witnessT1, vec3, dot3, cross3, Prod.mk.injEq]
  norm_num

/-- Circumradius R = √3/2 = dist(O, A). -/
theorem witnessT1_circumradius : witnessT1.circumradius = Real.sqrt 3 / 2 := by
  rw [Tetrahedron.circumradius, witnessT1_circumcenter]
  simp only [dist3, witnessT1]
  rw [show ((0 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - 1 / 2) ^ 2
        = 3 * (1 / 2) ^ 2 by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

/-- twentyFourPointRadius R/3 = √3/6. -/
theorem witnessT1_twentyFourPointRadius :
    witnessT1.twentyFourPointRadius = Real.sqrt 3 / 6 := by
  rw [Tetrahedron.twentyFourPointRadius, witnessT1_circumradius]
  ring

/-- twentyFourPointCenter N₂₄ = (1/2, 1/2, 0) (rational; = midpoint(O, 4G−3O)). -/
theorem witnessT1_twentyFourPointCenter :
    witnessT1.twentyFourPointCenter = (1 / 2, 1 / 2, 0) := by
  rw [Tetrahedron.twentyFourPointCenter, Tetrahedron.mongePoint, witnessT1_circumcenter]
  simp only [midpoint3, Tetrahedron.centroid, witnessT1, Prod.mk.injEq]
  norm_num

/-- Incenter I = ((1+√2)/Δ, (1+√2)/Δ, 1/Δ), Δ = 1+√3+2√2. -/
theorem witnessT1_incenter :
    witnessT1.incenter =
      ((1 + Real.sqrt 2) / (1 + Real.sqrt 3 + 2 * Real.sqrt 2),
       (1 + Real.sqrt 2) / (1 + Real.sqrt 3 + 2 * Real.sqrt 2),
       1 / (1 + Real.sqrt 3 + 2 * Real.sqrt 2)) := by
  have hpos : (0 : ℝ) < 1 + Real.sqrt 3 + 2 * Real.sqrt 2 := by positivity
  have htot : (Real.sqrt 3 / 2 + Real.sqrt 2 / 2 + Real.sqrt 2 / 2 + 1 / 2) ≠ 0 := by positivity
  simp only [Tetrahedron.incenter]
  rw [witnessT1_faceArea_A, witnessT1_faceArea_B, witnessT1_faceArea_C, witnessT1_faceArea_D]
  simp only [witnessT1, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [div_eq_div_iff htot hpos.ne']
      ring

/-- The witness T1 is non-orthocentric AND its twenty-four-point sphere is NOT
internally tangent to its insphere.  This is exactly the body of the parent
axiom `feuerbach_3d_fails_general`, specialised to T1.

Both conjuncts are proved (S11): the non-orthocentric conjunct is
`witnessT1_nonorthocentric`, and the non-tangency follows by substituting the
closed forms of `twentyFourPointCenter`/`incenter`/`inradius`/
`twentyFourPointRadius` at T1, squaring, and invoking the surd separation kernel
(all sympy-certified in `verify_feuerbach3d_fails_witness_exact.py`). -/
theorem witnessT1_fails :
    (dot3 (vec3 witnessT1.A witnessT1.B) (vec3 witnessT1.C witnessT1.D) ≠ 0) ∧
    ¬ spheresInternallyTangent
        witnessT1.twentyFourPointCenter witnessT1.incenter
        witnessT1.twentyFourPointRadius witnessT1.inradius := by
  refine ⟨witnessT1_nonorthocentric, ?_⟩
  -- Unfold tangency and substitute the closed forms of all four invariants at T1.
  simp only [spheresInternallyTangent, witnessT1_twentyFourPointCenter, witnessT1_incenter,
    witnessT1_twentyFourPointRadius, witnessT1_inradius]
  -- Goal: ¬ (dist3 N₂₄ I = |√3/6 − 1/Δ|), with N₂₄, I, R/3, r all explicit.
  intro h
  -- Square the tangency equation: dist3_sq N₂₄ I = (√3/6 − 1/Δ)².
  have h2 :
      dist3_sq (1 / 2, 1 / 2, 0)
        ((1 + Real.sqrt 2) / (1 + Real.sqrt 3 + 2 * Real.sqrt 2),
         (1 + Real.sqrt 2) / (1 + Real.sqrt 3 + 2 * Real.sqrt 2),
         1 / (1 + Real.sqrt 3 + 2 * Real.sqrt 2))
        = (Real.sqrt 3 / 6 - 1 / (1 + Real.sqrt 3 + 2 * Real.sqrt 2)) ^ 2 := by
    have hsq := congrArg (· ^ 2) h
    rwa [dist3_sq_eq, sq_abs] at hsq
  -- The strict separation dist3_sq N₂₄ I > (√3/6 − 1/Δ)², contradicting h2.
  have hgt :
      (Real.sqrt 3 / 6 - 1 / (1 + Real.sqrt 3 + 2 * Real.sqrt 2)) ^ 2 <
        dist3_sq (1 / 2, 1 / 2, 0)
          ((1 + Real.sqrt 2) / (1 + Real.sqrt 3 + 2 * Real.sqrt 2),
           (1 + Real.sqrt 2) / (1 + Real.sqrt 3 + 2 * Real.sqrt 2),
           1 / (1 + Real.sqrt 3 + 2 * Real.sqrt 2)) := by
    set a : ℝ := Real.sqrt 2 with ha
    set b : ℝ := Real.sqrt 3 with hb
    have ha0 : 0 ≤ a := by rw [ha]; exact Real.sqrt_nonneg 2
    have hb0 : 0 ≤ b := by rw [hb]; exact Real.sqrt_nonneg 3
    have ha2 : a ^ 2 = 2 := by rw [ha]; exact Real.sq_sqrt (by norm_num)
    have hb2 : b ^ 2 = 3 := by rw [hb]; exact Real.sq_sqrt (by norm_num)
    have hΔpos : (0 : ℝ) < 1 + b + 2 * a := by positivity
    -- rational closed forms of both sides (no surd-square needed)
    have hd :
        dist3_sq (1 / 2, 1 / 2, 0)
          ((1 + a) / (1 + b + 2 * a), (1 + a) / (1 + b + 2 * a), 1 / (1 + b + 2 * a))
          = ((1 - b) ^ 2 + 2) / (2 * (1 + b + 2 * a) ^ 2) := by
      simp only [dist3_sq]
      field_simp [hΔpos.ne']
      ring
    have he :
        (b / 6 - 1 / (1 + b + 2 * a)) ^ 2
          = (b * (1 + b + 2 * a) - 6) ^ 2 / (36 * (1 + b + 2 * a) ^ 2) := by
      field_simp [hΔpos.ne']
      ring
    rw [hd, he]
    -- numeric separating bounds on the surds
    have ha_ub : a < 1.41422 := by nlinarith [ha2, ha0]
    have hb_ub : b < 1.7321 := by nlinarith [hb2, hb0]
    have hab_lb : (2.4494 : ℝ) < a * b := by
      have hab : a * b = Real.sqrt 6 := by
        rw [ha, hb, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      rw [hab]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
    -- the sharp three-surd kernel, as an exact polynomial identity mod a²=2, b²=3
    have hid :
        18 * ((1 - b) ^ 2 + 2) - (b * (1 + b + 2 * a) - 6) ^ 2
          = 72 - 30 * b - 12 * a + 12 * (a * b) := by
      linear_combination (-4 * b ^ 2) * ha2
        + (-4 * a * b - 4 * a - b ^ 2 - 2 * b + 18) * hb2
    have hpos : (0 : ℝ) < 72 - 30 * b - 12 * a + 12 * (a * b) := by
      linarith [ha_ub, hb_ub, hab_lb]
    have hkey : (b * (1 + b + 2 * a) - 6) ^ 2 < 18 * ((1 - b) ^ 2 + 2) := by
      linarith [hid, hpos]
    -- transport across the common positive denominator
    have hD2 : (0 : ℝ) < 2 * (1 + b + 2 * a) ^ 2 := by positivity
    rw [div_lt_div_iff (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hkey hD2]
  linarith [h2, hgt]

/-- Discharge of the parent existence axiom from the explicit witness. -/
theorem feuerbach_3d_fails_general_proved :
    ∃ T : Tetrahedron,
      (dot3 (vec3 T.A T.B) (vec3 T.C T.D) ≠ 0) ∧
      ¬ spheresInternallyTangent
          T.twentyFourPointCenter T.incenter
          T.twentyFourPointRadius T.inradius :=
  ⟨witnessT1, witnessT1_fails⟩

end FeuerbachsTheoremOQ02
