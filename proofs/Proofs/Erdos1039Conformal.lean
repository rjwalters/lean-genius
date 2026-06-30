/-
  Erdős Problem #1039 — OQ-03: the conformal-mapping route to bounding ρ(f).

  Source: https://erdosproblems.com/1039
  Status of parent problem: OPEN

  Parent setup.
  For a monic polynomial f(z) = ∏ᵢ (z - zᵢ) ∈ ℂ[z] with all roots zᵢ in the closed
  unit disc, let ρ(f) be the radius of the largest open disc contained in the
  sublevel set (lemniscate interior) {z : |f(z)| < 1}.  Erdős, Herzog and Piranian
  asked whether ρ(f) ≫ 1/n.  The current record lower bound c/(n√(log n)) of
  Krishnapur–Lundberg–Ramachandran (2025) is obtained by an *area* argument:
  an inscribed disc of radius r has area πr², so ρ(f)² · π ≤ area{|f| < 1}.

  OQ-03 asks:
      "Can direct conformal mapping estimates (bypassing the area approach)
       give a sharper bound on ρ(f)?"

  This file formalises the *elementary conformal estimate* underlying that
  question and pins down its precise limitation — an axiom-free contribution that
  does not resolve the OPEN parent.

  Main results.
  1. `norm_deriv_le_inv_of_sphere_le_one` — the Cauchy/Schwarz derivative estimate
     specialised to the unit codomain: a function holomorphic on a disc and bounded
     by 1 on its boundary sphere has |f'(center)| ≤ 1/r.
  2. `norm_le_one_on_closedBall` — boundary bridge: an open disc inside the
     sublevel set has |f| ≤ 1 on the *closed* disc, by continuity.
  3. `inscribed_ball_norm_deriv_le` — if the open disc D(c, r) is inscribed in
     {|f| < 1} then |f'(c)| ≤ 1/r.
  4. `inscribed_radius_le_inv_norm_deriv` — equivalently r ≤ 1/|f'(c)| whenever
     f'(c) ≠ 0.  This is the "direct conformal estimate" of OQ-03: it bounds the
     inscribed radius purely from the derivative, with no recourse to area.
  5. `polynomial_inscribed_radius_le_inv_norm_deriv` — the specialisation to an
     actual monic polynomial ∏ᵢ (z - rootsᵢ).
  6. `conformal_estimate_vacuous_at_critical_point` — the obstruction: at a
     critical point (f'(c) = 0) the estimate degenerates to the false bound r ≤ 0,
     so the conformal estimate alone gives **no** information there.  Because the
     extremal inscribed disc of a lemniscate typically sits where f is flat (near a
     critical point), this is exactly why a *direct* conformal bound on ρ(f) is not
     available and the area approach of KLR is used instead.
-/

import Mathlib

namespace Erdos1039Conformal

open Complex Metric Set

/-- The open sublevel set (lemniscate interior) `{z : ‖f z‖ < 1}` of `f : ℂ → ℂ`. -/
def sublevel (f : ℂ → ℂ) : Set ℂ := {z : ℂ | ‖f z‖ < 1}

/-- **Cauchy/Schwarz derivative estimate, unit codomain.**
If `f` is holomorphic on the open disc `ball c r` and continuous up to the closure,
and `‖f‖ ≤ 1` on the boundary sphere, then `‖f'(c)‖ ≤ 1 / r`.

This is the elementary conformal-mapping estimate behind Erdős #1039 OQ-03: the
first Cauchy coefficient bound, equivalent to the Schwarz lemma for the disc. -/
theorem norm_deriv_le_inv_of_sphere_le_one
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DiffContOnCl ℂ f (ball c r))
    (hb : ∀ z ∈ sphere c r, ‖f z‖ ≤ 1) :
    ‖deriv f c‖ ≤ 1 / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd hb

/-- **Boundary bridge.**
If the open disc `ball c r` is contained in the sublevel set `{‖f‖ < 1}` and `f` is
continuous, then `‖f‖ ≤ 1` on the whole *closed* disc `closedBall c r`.  The strict
bound `< 1` on the open disc passes to `≤ 1` on the closure since `{w : ‖f w‖ ≤ 1}`
is closed. -/
theorem norm_le_one_on_closedBall
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : Continuous f)
    (hsub : ball c r ⊆ sublevel f) :
    ∀ z ∈ closedBall c r, ‖f z‖ ≤ 1 := by
  have hclosed : IsClosed {w : ℂ | ‖f w‖ ≤ 1} :=
    isClosed_le (continuous_norm.comp hcont) continuous_const
  have hball_sub : ball c r ⊆ {w : ℂ | ‖f w‖ ≤ 1} := fun w hw => le_of_lt (hsub hw)
  have hclos : closure (ball c r) ⊆ {w : ℂ | ‖f w‖ ≤ 1} :=
    hclosed.closure_subset_iff.mpr hball_sub
  rw [closure_ball c hr.ne'] at hclos
  exact fun z hz => hclos hz

/-- **Conformal estimate for an inscribed disc (derivative form).**
If the open disc `D(c, r)` is inscribed in the sublevel set `{|f| < 1}` of an entire
function `f`, then `‖f'(c)‖ ≤ 1 / r`. -/
theorem inscribed_ball_norm_deriv_le
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : Differentiable ℂ f)
    (hsub : ball c r ⊆ sublevel f) :
    ‖deriv f c‖ ≤ 1 / r := by
  refine norm_deriv_le_inv_of_sphere_le_one hr hdiff.diffContOnCl ?_
  intro z hz
  exact norm_le_one_on_closedBall hr hdiff.continuous hsub z (sphere_subset_closedBall hz)

/-- **Conformal estimate for an inscribed disc (radius form).**
The radius of any disc inscribed in the sublevel set is bounded by the reciprocal of
the derivative at its centre: `r ≤ 1 / ‖f'(c)‖` (for `f'(c) ≠ 0`).

This is the "direct conformal mapping estimate" of Erdős #1039 OQ-03 — a bound on
the inscribed radius obtained purely from the derivative, with no area input. -/
theorem inscribed_radius_le_inv_norm_deriv
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hdiff : Differentiable ℂ f)
    (hsub : ball c r ⊆ sublevel f)
    (hderiv : deriv f c ≠ 0) :
    r ≤ 1 / ‖deriv f c‖ := by
  have h := inscribed_ball_norm_deriv_le hr hdiff hsub
  have hpos : 0 < ‖deriv f c‖ := norm_pos_iff.mpr hderiv
  rw [le_div_iff₀ hpos]
  calc r * ‖deriv f c‖ ≤ r * (1 / r) := by
        exact mul_le_mul_of_nonneg_left h hr.le
    _ = 1 := by rw [mul_one_div, div_self hr.ne']

/-
## Specialisation to a monic polynomial

For the actual Erdős #1039 setting, `f` is the monic polynomial with prescribed
roots.  It is entire, so the conformal estimate applies verbatim.
-/

/-- The monic polynomial `z ↦ ∏ᵢ (z - rootsᵢ)` determined by a finite root list. -/
noncomputable def rootPoly {n : ℕ} (roots : Fin n → ℂ) : ℂ → ℂ :=
  fun z => ∏ i, (z - roots i)

/-- A monic polynomial is entire (differentiable everywhere). -/
theorem rootPoly_differentiable {n : ℕ} (roots : Fin n → ℂ) :
    Differentiable ℂ (rootPoly roots) := by
  unfold rootPoly
  fun_prop

/-- **Conformal inscribed-radius bound for a monic polynomial.**
If the open disc `D(c, r)` is inscribed in the lemniscate interior
`{z : ‖∏ᵢ (z - rootsᵢ)‖ < 1}` and the centre is not a critical point, then
`r ≤ 1 / ‖f'(c)‖`. -/
theorem polynomial_inscribed_radius_le_inv_norm_deriv
    {n : ℕ} (roots : Fin n → ℂ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : ball c r ⊆ sublevel (rootPoly roots))
    (hderiv : deriv (rootPoly roots) c ≠ 0) :
    r ≤ 1 / ‖deriv (rootPoly roots) c‖ :=
  inscribed_radius_le_inv_norm_deriv hr (rootPoly_differentiable roots) hsub hderiv

/-
## The obstruction: the conformal estimate degenerates at critical points

The radius bound `r ≤ 1/‖f'(c)‖` requires `f'(c) ≠ 0`.  At a critical point the
right-hand side becomes `1/0 = 0` (Lean's junk value), so the estimate asserts the
false inequality `r ≤ 0` and therefore conveys *no* information.

The witness `f ≡ 0` makes this concrete: its sublevel set is all of `ℂ`, so discs of
every radius are inscribed, yet `f' ≡ 0`.  Because the extremal inscribed disc of a
genuine lemniscate tends to sit where the polynomial is flat (near a critical point),
this degeneracy is exactly why a *direct* conformal bound on `ρ(f)` is unavailable —
the reason Krishnapur–Lundberg–Ramachandran fall back on the area approach (OQ-03). -/
theorem conformal_estimate_vacuous_at_critical_point :
    ∃ (f : ℂ → ℂ) (c : ℂ) (r : ℝ),
      0 < r ∧ Differentiable ℂ f ∧ ball c r ⊆ sublevel f ∧
      deriv f c = 0 ∧ ¬ r ≤ 1 / ‖deriv f c‖ := by
  refine ⟨fun _ => 0, 0, 1, one_pos, differentiable_const 0, ?_, ?_, ?_⟩
  · intro z _
    simp [sublevel]
  · simp
  · simp only [deriv_const', norm_zero, div_zero]
    norm_num
