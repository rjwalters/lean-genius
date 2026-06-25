import Proofs.MenelausTheorem
import Mathlib.Tactic

/-
# Menelaus follow-up: the cevian triangle and Routh's theorem

Open question: `menelaus-theorem-oq-01-oq-03`
Parent: `Proofs/MenelausTheorem.lean` (`menelaus-theorem-oq-01`).

## What this adds

The parent characterises when a *transversal* meets the three sides of a triangle
collinearly (signed-ratio product `= -1`). Its Ceva companion characterises when the
three *cevians* `AX, BY, CZ` are concurrent (signed-ratio product `= +1`, equivalently
`t·u·v = (1-t)(1-u)(1-v)`).

This file studies the **cevian triangle** `P Q R` cut out by the three cevians:

  `P = AX ∩ BY`,  `Q = BY ∩ CZ`,  `R = CZ ∩ AX`.

Two results, both built on the parent's `collinearDet` machinery:

1. **Concurrency criterion (general triangle).** For an arbitrary non-degenerate
   triangle, the intersection `P = AX ∩ BY` lies on the third cevian `CZ` — i.e. the
   three cevians are concurrent and the cevian triangle collapses to a point — **iff**
   `t·u·v = (1-t)(1-u)(1-v)`. The driving identity

     `collinearDet C Z P · detP
        = ((1-t)(1-u)(1-v) - t·u·v) · (collinearDet A B C)²`

   is a pure polynomial identity in the six triangle coordinates and `t, u, v`.

2. **Routh's theorem (signed-area formula).** For the canonical reference triangle
   `A=(0,0), B=(1,0), C=(0,1)` (where `collinearDet A B C = 1`), the signed area of the
   cevian triangle is

     `collinearDet P Q R
        = (t·u·v - (1-t)(1-u)(1-v))²
          / ((1-u+t·u)·(1-v+u·v)·(1-t+v·t))`.

   The vertices `P, Q, R` are *certified* to lie on the correct pairs of cevians, so this
   really is the cevian triangle. The numerator is the *square* of the concurrency
   defect, so the cevian triangle collapses to a point exactly when the cevians concur —
   recovering result (1). Because the area ratio `area(PQR)/area(ABC)` is an affine
   invariant and every triangle is the affine image of the reference triangle, this
   closed form is the general Routh ratio. The classical "one-seventh area" triangle
   (`t=u=v=1/3`, trisection cevians) drops out with value `1/7`.

Routh's theorem is **not** in Mathlib.

## Status
- [x] Cevian line intersection point, explicit closed form
- [x] Concurrency criterion (general triangle, polynomial identity)
- [x] Cevians-concurrent ↔ `t·u·v = (1-t)(1-u)(1-v)`
- [x] Cevian-triangle vertices certified on their cevians
- [x] Routh signed-area formula (reference triangle)
- [x] Cevian triangle degenerate ↔ concurrent (corollary of Routh)
- [x] One-seventh area triangle as a concrete instance
- [x] 0 sorries, 0 axioms
-/

namespace MenelausTheoremOQ01OQ03

open MenelausTheorem

set_option linter.unusedVariables false

/-! ### Cevian line intersection (general triangle) -/

/-- The cross product of the direction vectors of the line `P→Q` and the line `R→S`.
    It vanishes exactly when the two lines are parallel, and is the denominator that
    appears when solving for their intersection. -/
def detLines (P Q R S : Pt) : ℝ :=
  (Q.1 - P.1) * (S.2 - R.2) - (Q.2 - P.2) * (S.1 - R.1)

/-- The intersection point of the line through `P, Q` and the line through `R, S`,
    via Cramer's rule on the two line equations. Valid when `detLines P Q R S ≠ 0`. -/
noncomputable def interPt (P Q R S : Pt) : Pt :=
  let c1 := (Q.1 - P.1) * P.2 - (Q.2 - P.2) * P.1
  let c2 := (S.1 - R.1) * R.2 - (S.2 - R.2) * R.1
  let d := detLines P Q R S
  ((c1 * (S.1 - R.1) - c2 * (Q.1 - P.1)) / d,
   ((S.2 - R.2) * c1 - (Q.2 - P.2) * c2) / d)

/-- Vertex `P = AX ∩ BY` of the cevian triangle. -/
noncomputable def cevP (cfg : MenelausConfig) : Pt :=
  interPt cfg.A (ptX cfg) cfg.B (ptY cfg)

/-- Parallelism denominator for the pair of cevians `AX, BY`. -/
def detP (cfg : MenelausConfig) : ℝ := detLines cfg.A (ptX cfg) cfg.B (ptY cfg)

/-- `cevP` lies on the cevian `AX` (when `AX, BY` are not parallel). -/
theorem cevP_on_AX (cfg : MenelausConfig) (hP : detP cfg ≠ 0) :
    collinearDet cfg.A (ptX cfg) (cevP cfg) = 0 := by
  simp only [collinearDet, cevP, interPt, ptX, ptY, detP, detLines] at hP ⊢
  field_simp at hP ⊢
  ring

/-- `cevP` lies on the cevian `BY` (when `AX, BY` are not parallel). -/
theorem cevP_on_BY (cfg : MenelausConfig) (hP : detP cfg ≠ 0) :
    collinearDet cfg.B (ptY cfg) (cevP cfg) = 0 := by
  simp only [collinearDet, cevP, interPt, ptX, ptY, detP, detLines] at hP ⊢
  field_simp at hP ⊢
  ring

/-! ### Concurrency criterion (general triangle) -/

/-- **Concurrency defect identity.** For an arbitrary triangle, the signed area of
    `C, Z, P` (which vanishes exactly when `P` lies on the third cevian `CZ`) equals the
    concurrency defect `(1-t)(1-u)(1-v) - t·u·v` times the square of the triangle's own
    signed area. A pure polynomial identity in all six coordinates and `t, u, v`. -/
theorem concurrency_defect (cfg : MenelausConfig) (hP : detP cfg ≠ 0) :
    collinearDet cfg.C (ptZ cfg) (cevP cfg) * detP cfg
      = ((1 - cfg.t) * (1 - cfg.u) * (1 - cfg.v) - cfg.t * cfg.u * cfg.v)
        * (collinearDet cfg.A cfg.B cfg.C) ^ 2 := by
  simp only [collinearDet, cevP, interPt, ptX, ptY, ptZ, detP, detLines] at hP ⊢
  field_simp at hP ⊢
  ring

/-- **Cevian concurrency criterion.** For a non-degenerate triangle whose cevians
    `AX, BY` are not parallel, the three cevians `AX, BY, CZ` are concurrent (the vertex
    `P = AX ∩ BY` lies on `CZ`) **iff** `t·u·v = (1-t)(1-u)(1-v)`. This is the cevian
    (Ceva-type) companion of the parent's transversal (Menelaus) criterion. -/
theorem cevians_concurrent_iff (cfg : MenelausConfig) (hP : detP cfg ≠ 0) :
    collinearDet cfg.C (ptZ cfg) (cevP cfg) = 0
      ↔ cfg.t * cfg.u * cfg.v = (1 - cfg.t) * (1 - cfg.u) * (1 - cfg.v) := by
  have hΔ : collinearDet cfg.A cfg.B cfg.C ≠ 0 := cfg.nondegen
  have key := concurrency_defect cfg hP
  constructor
  · intro h
    rw [h, zero_mul] at key
    have hsq : (collinearDet cfg.A cfg.B cfg.C) ^ 2 ≠ 0 := pow_ne_zero _ hΔ
    have : (1 - cfg.t) * (1 - cfg.u) * (1 - cfg.v) - cfg.t * cfg.u * cfg.v = 0 :=
      (mul_eq_zero.mp key.symm).resolve_right hsq
    linarith
  · intro h
    have hz : (1 - cfg.t) * (1 - cfg.u) * (1 - cfg.v) - cfg.t * cfg.u * cfg.v = 0 := by
      linarith
    have hzero : collinearDet cfg.C (ptZ cfg) (cevP cfg) * detP cfg = 0 := by
      rw [key, hz, zero_mul]
    exact (mul_eq_zero.mp hzero).resolve_right hP

/-! ### Routh's theorem on the reference triangle

We work with the canonical reference triangle `A=(0,0), B=(1,0), C=(0,1)`, where the
division points are `X=(1-t,t)`, `Y=(0,1-u)`, `Z=(v,0)`. Every triangle is an affine
image of this one and the cevian area ratio is affine-invariant, so the closed form
below is the general Routh ratio. The cevian-triangle vertices are written in explicit
closed form and then *certified* to lie on the correct cevians. -/

/-- Cevian-triangle vertex `P = AX ∩ BY`, reference triangle, closed form. -/
noncomputable def vP (t u v : ℝ) : Pt :=
  ((1 - t) * (1 - u) / (1 - u + t * u), t * (1 - u) / (1 - u + t * u))

/-- Cevian-triangle vertex `Q = BY ∩ CZ`, reference triangle, closed form. -/
noncomputable def vQ (t u v : ℝ) : Pt :=
  (u * v / (1 - v + u * v), (1 - u) * (1 - v) / (1 - v + u * v))

/-- Cevian-triangle vertex `R = CZ ∩ AX`, reference triangle, closed form. -/
noncomputable def vR (t u v : ℝ) : Pt :=
  ((1 - t) * v / (1 - t + v * t), t * v / (1 - t + v * t))

/-- `vP` lies on cevian `AX` (from `A=(0,0)` to `X=(1-t,t)`). -/
theorem vP_on_AX (t u v : ℝ) (hDP : 1 - u + t * u ≠ 0) :
    collinearDet (0, 0) (1 - t, t) (vP t u v) = 0 := by
  simp only [collinearDet, vP]; field_simp; ring

/-- `vP` lies on cevian `BY` (from `B=(1,0)` to `Y=(0,1-u)`). -/
theorem vP_on_BY (t u v : ℝ) (hDP : 1 - u + t * u ≠ 0) :
    collinearDet (1, 0) (0, 1 - u) (vP t u v) = 0 := by
  simp only [collinearDet, vP]; field_simp; ring

/-- `vQ` lies on cevian `BY`. -/
theorem vQ_on_BY (t u v : ℝ) (hDQ : 1 - v + u * v ≠ 0) :
    collinearDet (1, 0) (0, 1 - u) (vQ t u v) = 0 := by
  simp only [collinearDet, vQ]; field_simp; ring

/-- `vQ` lies on cevian `CZ` (from `C=(0,1)` to `Z=(v,0)`). -/
theorem vQ_on_CZ (t u v : ℝ) (hDQ : 1 - v + u * v ≠ 0) :
    collinearDet (0, 1) (v, 0) (vQ t u v) = 0 := by
  have hDQ2 : 1 - v + v * u ≠ 0 := by rwa [mul_comm u v] at hDQ
  simp only [collinearDet, vQ]; field_simp [hDQ, hDQ2]; ring

/-- `vR` lies on cevian `CZ`. -/
theorem vR_on_CZ (t u v : ℝ) (hDR : 1 - t + v * t ≠ 0) :
    collinearDet (0, 1) (v, 0) (vR t u v) = 0 := by
  simp only [collinearDet, vR]; field_simp; ring

/-- `vR` lies on cevian `AX`. -/
theorem vR_on_AX (t u v : ℝ) (hDR : 1 - t + v * t ≠ 0) :
    collinearDet (0, 0) (1 - t, t) (vR t u v) = 0 := by
  simp only [collinearDet, vR]; field_simp; ring

/-- **Routh's theorem (signed-area form).** For the reference triangle, the signed area
    of the cevian triangle `P Q R` is the square of the concurrency defect divided by the
    product of the three "Routh denominators" `1-u+t·u`, `1-v+u·v`, `1-t+v·t`. Since
    `collinearDet A B C = 1` here, this is exactly the area ratio. -/
theorem routh_area (t u v : ℝ)
    (hDP : 1 - u + t * u ≠ 0) (hDQ : 1 - v + u * v ≠ 0) (hDR : 1 - t + v * t ≠ 0) :
    collinearDet (vP t u v) (vQ t u v) (vR t u v)
      = (t * u * v - (1 - t) * (1 - u) * (1 - v)) ^ 2
        / ((1 - u + t * u) * (1 - v + u * v) * (1 - t + v * t)) := by
  have hDP2 : 1 - u + u * t ≠ 0 := by rwa [mul_comm t u] at hDP
  have hDQ2 : 1 - v + v * u ≠ 0 := by rwa [mul_comm u v] at hDQ
  have hDR2 : 1 - t + t * v ≠ 0 := by rwa [mul_comm v t] at hDR
  simp only [collinearDet, vP, vQ, vR]
  field_simp [hDP, hDP2, hDQ, hDQ2, hDR, hDR2]
  ring

/-- **Cevian triangle degenerates iff cevians concur** (reference triangle). The signed
    area vanishes exactly at the Ceva concurrency condition — the numerator of Routh's
    ratio is the *square* of the concurrency defect. -/
theorem routh_area_zero_iff (t u v : ℝ)
    (hDP : 1 - u + t * u ≠ 0) (hDQ : 1 - v + u * v ≠ 0) (hDR : 1 - t + v * t ≠ 0) :
    collinearDet (vP t u v) (vQ t u v) (vR t u v) = 0
      ↔ t * u * v = (1 - t) * (1 - u) * (1 - v) := by
  rw [routh_area t u v hDP hDQ hDR, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have : t * u * v - (1 - t) * (1 - u) * (1 - v) = 0 :=
        pow_eq_zero_iff (by norm_num) |>.mp h
      linarith
    · exact absurd h (by
        simp only [mul_ne_zero_iff]; exact ⟨⟨hDP, hDQ⟩, hDR⟩)
  · intro h
    left
    have : t * u * v - (1 - t) * (1 - u) * (1 - v) = 0 := by linarith
    rw [this]; norm_num

/-- **The one-seventh area triangle.** When `t = u = v = 1/3` the cevians trisect the
    sides (each cuts `1 : 2`), and the cevian triangle has exactly `1/7` the signed area
    of the reference triangle — the classical Routh "one-seventh" instance. -/
theorem routh_one_seventh :
    collinearDet (vP (1/3) (1/3) (1/3)) (vQ (1/3) (1/3) (1/3)) (vR (1/3) (1/3) (1/3))
      = 1 / 7 := by
  rw [routh_area (1/3) (1/3) (1/3) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end MenelausTheoremOQ01OQ03
