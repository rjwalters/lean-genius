import Mathlib

/-
# Picard–Lindelöf via the contraction mapping principle: local existence and uniqueness

The Picard–Lindelöf (Cauchy–Lipschitz) theorem is the prototypical application of the
Banach contraction mapping principle.  To solve the autonomous initial value problem

  `y'(t) = f(y(t))`,  `y(t₀) = x₀`,

one rewrites it as the fixed-point equation `y = P y` for the **Picard integral
operator** `(P y)(t) = x₀ + ∫_{t₀}^{t} f(y(s)) ds`.  When `f` is Lipschitz, `P` is a
contraction on a suitable complete space of continuous curves on a short time interval,
so Banach's theorem produces a unique fixed point — the local solution.

Mathlib carries out exactly this construction internally (`IsPicardLindelof`, the
`FunSpace` contraction, and `ODE_solution_unique` via Grönwall's inequality).  This file
packages the two halves of the theorem for the autonomous problem `y' = f(y)` into clean,
directly usable statements:

* `exists_local_solution` — if `f` is `C¹` near `x₀` then the IVP has a local solution on
  a genuine open time interval around `t₀` (existence, from the contraction fixed point).
* `solution_unique` — if `f` is (globally) Lipschitz then any two solutions sharing an
  initial value coincide on their common interval (uniqueness, from Grönwall).
* `exists_unique_local_solution` — the two combined: a `C¹`, Lipschitz field admits a
  local solution that is unique among all solutions on that interval.

Everything is a 0-axiom derivation from Mathlib's ODE library.
-/

open Set Metric

namespace PicardLindelofOQ01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Picard–Lindelöf, local existence.**

If the vector field `f : E → E` is continuously differentiable near `x₀`, then for any
initial time `t₀` the autonomous initial value problem `y' = f(y)`, `y(t₀) = x₀` has a
solution `α` on some genuine open interval `(t₀ - ε, t₀ + ε)` with `α t₀ = x₀`.

This is the existence half of the Cauchy–Lipschitz theorem: the local solution is the
fixed point of the Picard integral operator, obtained from Banach's contraction principle
(carried out inside Mathlib's `IsPicardLindelof.of_contDiffAt_one`). -/
theorem exists_local_solution [CompleteSpace E] {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  obtain ⟨r, hr, ε, hε, h⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt t₀
  obtain ⟨α, hα0, hαderiv⟩ := h x₀ (mem_closedBall_self hr.le)
  exact ⟨ε, hε, α, hα0, hαderiv⟩

/-- **Picard–Lindelöf, local uniqueness.**

If the vector field `f : E → E` is Lipschitz continuous, then any two solutions of the
autonomous equation `y' = f(y)` on an open interval `(a, b)` that agree at one interior
point `t₀` agree on the whole interval.

This is the uniqueness half of the Cauchy–Lipschitz theorem, a consequence of Grönwall's
inequality (`ODE_solution_unique_of_mem_Ioo`); it is what makes the Picard fixed point the
*unique* local solution. -/
theorem solution_unique {f : E → E} {K : NNReal} (hf : LipschitzWith K f)
    {a b t₀ : ℝ} {α β : ℝ → E} (ht₀ : t₀ ∈ Ioo a b)
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (f (α t)) t)
    (hβ : ∀ t ∈ Ioo a b, HasDerivAt β (f (β t)) t) (h0 : α t₀ = β t₀) :
    EqOn α β (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => f) (s := fun _ => univ)
    (fun _ _ => hf.lipschitzOnWith) ht₀
    (fun t ht => ⟨hα t ht, mem_univ _⟩) (fun t ht => ⟨hβ t ht, mem_univ _⟩) h0

/-- **Picard–Lindelöf (Cauchy–Lipschitz), local existence and uniqueness.**

If the vector field `f : E → E` is both `C¹` near `x₀` and globally Lipschitz, then the
autonomous initial value problem `y' = f(y)`, `y(t₀) = x₀` has, on a genuine open interval
around `t₀`, a solution `α` that is unique: any solution `β` on that interval with the same
initial value `β t₀ = x₀` coincides with `α`. -/
theorem exists_unique_local_solution [CompleteSpace E] {f : E → E} {x₀ : E} {K : NNReal}
    (hf : ContDiffAt ℝ 1 f x₀) (hlip : LipschitzWith K f) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E, (α t₀ = x₀ ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t) ∧
      ∀ β : ℝ → E, β t₀ = x₀ →
        (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt β (f (β t)) t) →
          EqOn α β (Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, α, hα0, hαderiv⟩ := exists_local_solution hf t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  refine ⟨ε, hε, α, ⟨hα0, hαderiv⟩, fun β hβ0 hβderiv => ?_⟩
  exact solution_unique hlip ht₀ hαderiv hβderiv (by rw [hα0, hβ0])

end PicardLindelofOQ01
