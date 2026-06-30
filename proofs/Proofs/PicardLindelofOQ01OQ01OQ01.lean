import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

/-!
# Non-autonomous Picard–Lindelöf: packaging `IsPicardLindelof` for `y' = F(t, y)`

The parent file (`PicardLindelofOQ01`) packages the autonomous Cauchy–Lipschitz
theorem `y' = f(y)` from Mathlib's ODE library.  This file answers the parent's
open questions by exposing the genuinely **non-autonomous** initial value problem

  `y'(t) = F(t, y(t)),    y(t₀) = x₀`

directly, with `F` Lipschitz in the space variable and continuous in time, and by
quantifying the interval of existence explicitly.

Mathlib's `IsPicardLindelof f t₀ x₀ a r L K` already carries a *time-dependent*
vector field `f : ℝ → E → E`, but its four-field hypothesis bundle (Lipschitz in
`y`, continuous in `t`, norm bound `L`, and the geometric interval condition
`L · max(tmax − t₀, t₀ − tmin) ≤ a − r`) is somewhat opaque.  Here we:

* `isPicardLindelof_of_box` — **package the hypotheses directly**: assemble
  `IsPicardLindelof` for the initial point `x₀` (`r = 0`) out of the three
  analytic conditions plus the explicit box inequality `L · ρ ≤ a` (OQ 1).
* `exists_local_solution_Icc` — local existence on the closed interval, in the
  differential (`HasDerivWithinAt`) form (OQ 1).
* `exists_local_solution_integral` — the solution as a **fixed point of the
  Picard integral operator** `(P y)(t) = x₀ + ∫_{t₀}^{t} F(τ, y(τ)) dτ`,
  exhibiting the successive-approximation form (OQ 2).
* `exists_local_solution` — local existence on an **open** interval with the
  explicit classical estimate `ε = a / L` for the half-width of the interval of
  existence (OQ 3): `ε ≥ a / L` is achieved with equality.
* `solution_unique` — uniqueness on an open interval for a globally (in `y`)
  Lipschitz field, via Grönwall's inequality.

Everything is a 0-axiom derivation from Mathlib's ODE library.
-/

open Metric Set
open scoped NNReal

namespace PicardLindelofOQ01OQ01OQ01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- **Packaging step (OQ 1).**  Build `IsPicardLindelof` for the non-autonomous
field `F` and the initial point `x₀` (so the ball radius `r = 0`) from the three
analytic hypotheses — Lipschitz in `y`, continuous in `t`, norm bound `L` — and
the explicit box inequality `L · max(tmax − t₀, t₀ − tmin) ≤ a`. -/
theorem isPicardLindelof_of_box
    {F : ℝ → E → E} {x₀ : E} {a L K : ℝ≥0} {tmin tmax t₀ : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (F t) (closedBall x₀ a))
    (hcont : ∀ x ∈ closedBall x₀ a, ContinuousOn (F · x) (Icc tmin tmax))
    (hbound : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖F t x‖ ≤ L)
    (hbox : (L : ℝ) * max (tmax - t₀) (t₀ - tmin) ≤ a) :
    IsPicardLindelof F (⟨t₀, ht₀⟩ : Icc tmin tmax) x₀ a 0 L K where
  lipschitzOnWith := hlip
  continuousOn := hcont
  norm_le := hbound
  mul_max_le := by simpa using hbox

/-- **Local existence, differential form on the closed interval (OQ 1).**
A non-autonomous field `F` that is `K`-Lipschitz in `y` on `closedBall x₀ a`,
continuous in `t`, bounded by `L`, and satisfies the box condition admits an
integral curve `α` on `[tmin, tmax]` with `α t₀ = x₀` solving `α'(t) = F(t, α t)`. -/
theorem exists_local_solution_Icc
    {F : ℝ → E → E} {x₀ : E} {a L K : ℝ≥0} {tmin tmax t₀ : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (F t) (closedBall x₀ a))
    (hcont : ∀ x ∈ closedBall x₀ a, ContinuousOn (F · x) (Icc tmin tmax))
    (hbound : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖F t x‖ ≤ L)
    (hbox : (L : ℝ) * max (tmax - t₀) (t₀ - tmin) ≤ a) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (F t (α t)) (Icc tmin tmax) t :=
  (isPicardLindelof_of_box ht₀ hlip hcont hbound hbox).exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- **The solution is a fixed point of the Picard integral operator (OQ 2).**
Under the same hypotheses there is a curve `α` with `α t₀ = x₀` satisfying the
integral equation `α t = x₀ + ∫_{t₀}^{t} F(τ, α τ) dτ` on `[tmin, tmax]` — the
fixed-point form whose successive approximations are the Picard iterates. -/
theorem exists_local_solution_integral
    {F : ℝ → E → E} {x₀ : E} {a L K : ℝ≥0} {tmin tmax t₀ : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (F t) (closedBall x₀ a))
    (hcont : ∀ x ∈ closedBall x₀ a, ContinuousOn (F · x) (Icc tmin tmax))
    (hbound : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖F t x‖ ≤ L)
    (hbox : (L : ℝ) * max (tmax - t₀) (t₀ - tmin) ≤ a) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, α t = x₀ + ∫ τ in t₀..t, F τ (α τ) := by
  obtain ⟨α, hα₀, hα⟩ := (isPicardLindelof_of_box ht₀ hlip hcont hbound hbox).exists_eq_forall_mem_Icc_eq_picard
    (mem_closedBall_self le_rfl)
  exact ⟨α, hα₀, fun t ht => (hα t ht).trans (ODE.picard_apply)⟩

/-- **Local existence on an open interval with the explicit existence estimate
`ε = a / L` (OQ 1 + OQ 3).**  If `F` is `K`-Lipschitz in `y` on `closedBall x₀ a`,
continuous in `t`, and bounded by `L` on the box `[t₀ − a/L, t₀ + a/L] × closedBall x₀ a`,
then `y' = F(t, y)`, `y(t₀) = x₀` has a solution on the open interval of half-width
`ε = a / L`.  This realises the classical lower bound `ε ≥ a / L` with equality. -/
theorem exists_local_solution
    {F : ℝ → E → E} {x₀ : E} {a L K : ℝ≥0} (t₀ : ℝ) (ha : 0 < a) (hL : 0 < L)
    (hlip : ∀ t ∈ Icc (t₀ - a / L) (t₀ + a / L), LipschitzOnWith K (F t) (closedBall x₀ a))
    (hcont : ∀ x ∈ closedBall x₀ a, ContinuousOn (F · x) (Icc (t₀ - a / L) (t₀ + a / L)))
    (hbound : ∀ t ∈ Icc (t₀ - a / L) (t₀ + a / L), ∀ x ∈ closedBall x₀ a, ‖F t x‖ ≤ L) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Ioo (t₀ - a / L) (t₀ + a / L), HasDerivAt α (F t (α t)) t := by
  set ε : ℝ := (a : ℝ) / (L : ℝ) with hε
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hεpos : 0 < ε := div_pos (by exact_mod_cast ha) hLpos
  have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hbox : (L : ℝ) * max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) ≤ a := by
    have : max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) = ε := by
      rw [show t₀ + ε - t₀ = ε from by ring, show t₀ - (t₀ - ε) = ε from by ring, max_self]
    rw [this, hε, mul_div_cancel₀ _ (ne_of_gt hLpos)]
  obtain ⟨α, hα₀, hα⟩ := exists_local_solution_Icc ht₀ hlip hcont hbound hbox
  refine ⟨α, hα₀, fun t ht => ?_⟩
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit [CompleteSpace E] in
/-- **Uniqueness (Cauchy–Lipschitz).**  If `F` is globally `K`-Lipschitz in the
space variable on each time slice, then two integral curves of `y' = F(t, y)`
on an open interval that agree at one interior point `t₀` agree throughout.
A direct consequence of Grönwall's inequality. -/
theorem solution_unique
    {F : ℝ → E → E} {K : ℝ≥0} {a b t₀ : ℝ} {f g : ℝ → E}
    (hlip : ∀ t ∈ Ioo a b, LipschitzWith K (F t)) (ht₀ : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (F t (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (F t (g t)) t)
    (h₀ : f t₀ = g t₀) :
    EqOn f g (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (s := fun _ => Set.univ)
    (fun t ht => (hlip t ht).lipschitzOnWith) ht₀
    (fun t ht => ⟨hf t ht, mem_univ _⟩) (fun t ht => ⟨hg t ht, mem_univ _⟩) h₀

end PicardLindelofOQ01OQ01OQ01
