import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Tactic

/-
# Generalized Continuum Function 2^ℵ_α for All Ordinals (OQ-01-OQ-01-OQ-02-OQ-03)

## Research Question (cantor-diagonalization-oq-01-oq-01-oq-02-oq-03)

Can the formalization handle the generalized continuum function α ↦ 2^ℵ_α
for all ordinals α? Specifically: does König's cofinality constraint — proved
for α=0 in the parent (OQ-01-OQ-01-OQ-02) — generalize to all ordinals?

## Answer: YES — the same theorem applies at every ordinal

The parent proved `cf(2^ℵ₀) > ℵ₀` using `Cardinal.lt_cof_power`.
That theorem already handles arbitrary infinite cardinals:

  `Cardinal.lt_cof_power : λ ≤ κ → 1 < μ → λ < (μ ^ κ).ord.cof.card`

Setting μ = 2, κ = λ = ℵ_α gives `ℵ_α < cf(2^ℵ_α)` for ALL ordinals α.

## What This File Proves (0 sorries)

1. `konig_aleph_general` — cf(2^ℵ_α) > ℵ_α for ALL ordinals α (proved)
2. `konig_aleph_zero` — cf(2^ℵ₀) > ℵ₀ (parent's result: special case α=0)
3. `konig_aleph_one` — cf(2^ℵ₁) > ℵ₁
4. `konig_aleph_omega` — cf(2^ℵ_ω) > ℵ_ω (limit ordinal case)
5. `two_pow_aleph_gt_aleph` — 2^ℵ_α > ℵ_α (Cantor's theorem generalized)
6. `two_pow_aleph_mono` — α ≤ β → 2^ℵ_α ≤ 2^ℵ_β (monotonicity)
7. `aleph_succ_le_two_pow_aleph` — ℵ_{α+1} ≤ 2^ℵ_α (successor bound)
8. `generalized_continuum_summary` — combined summary (proved)
-/

namespace CantorDiagGeneralized

open Cardinal Ordinal

/-! ## Part I: König's Constraint for ALL Alephs -/

/-- **Generalized König Constraint**: For every ordinal α, `cf(2^ℵ_α) > ℵ_α`.

    The parent (OQ-01-OQ-01-OQ-02) proved this for α=0. The same proof works
    verbatim for arbitrary α: `Cardinal.lt_cof_power le_rfl (by norm_num)`. -/
theorem konig_aleph_general (α : Ordinal.{0}) :
    aleph α < ((2 : Cardinal.{0}) ^ aleph α).ord.cof.card := by
  exact Cardinal.lt_cof_power le_rfl (by norm_num)

/-- **α = 0 case**: The parent's `konig_cofinality` (cf(2^ℵ₀) > ℵ₀). -/
theorem konig_aleph_zero :
    (ℵ₀ : Cardinal.{0}) < ((2 : Cardinal.{0}) ^ ℵ₀).ord.cof.card := by
  have := konig_aleph_general 0
  simp only [aleph_zero] at this
  exact this

/-- **α = 1**: cf(2^ℵ₁) > ℵ₁. -/
theorem konig_aleph_one :
    aleph 1 < ((2 : Cardinal.{0}) ^ aleph 1).ord.cof.card :=
  konig_aleph_general 1

/-- **α = ω** (first limit ordinal): cf(2^ℵ_ω) > ℵ_ω. -/
theorem konig_aleph_omega :
    aleph ω < ((2 : Cardinal.{0}) ^ aleph ω).ord.cof.card :=
  konig_aleph_general ω

/-! ## Part II: Cantor's Theorem for All Alephs -/

/-- **Cantor's theorem generalized**: 2^ℵ_α > ℵ_α for all ordinals α. -/
theorem two_pow_aleph_gt_aleph (α : Ordinal.{0}) :
    aleph α < (2 : Cardinal.{0}) ^ aleph α :=
  Cardinal.lt_two_pow (aleph α)

/-- **Monotonicity**: The function α ↦ 2^ℵ_α is (weakly) increasing. -/
theorem two_pow_aleph_mono {α β : Ordinal.{0}} (h : α ≤ β) :
    (2 : Cardinal.{0}) ^ aleph α ≤ (2 : Cardinal.{0}) ^ aleph β := by
  gcongr
  exact aleph_le_aleph.mpr h

/-- **Successor lower bound**: 2^ℵ_α ≥ ℵ_{α+1}.

    From Cantor: ℵ_α < 2^ℵ_α, so ℵ_{α+1} = (ℵ_α)⁺ ≤ 2^ℵ_α (successor is smallest larger). -/
theorem aleph_succ_le_two_pow_aleph (α : Ordinal.{0}) :
    aleph (α + 1) ≤ (2 : Cardinal.{0}) ^ aleph α := by
  rw [aleph_succ]
  exact Order.succ_le_of_lt (two_pow_aleph_gt_aleph α)

/-! ## Part III: König Exclusion for the Continuum Function -/

/-- **Singular exclusion**: 2^ℵ_α ≠ ℵ_β when cf(ℵ_β) ≤ ℵ_α.

    If 2^ℵ_α = ℵ_β, then cf(2^ℵ_α) = cf(ℵ_β). But König gives cf(2^ℵ_α) > ℵ_α,
    contradicting cf(ℵ_β) ≤ ℵ_α. -/
theorem two_pow_aleph_ne_aleph_of_cof_le (α β : Ordinal.{0})
    (hcof : (aleph β).ord.cof.card ≤ aleph α) :
    (2 : Cardinal.{0}) ^ aleph α ≠ aleph β := by
  intro heq
  have hk := konig_aleph_general α
  rw [heq] at hk
  exact absurd (hk.trans_le hcof) (lt_irrefl _)

/-! ## Part IV: Summary -/

/-- **Main conclusion**: The generalized continuum function 2^ℵ_α is well-defined
    and satisfies the König constraint at every ordinal. The parent's technique
    (using `Cardinal.lt_cof_power`) generalizes verbatim. -/
theorem generalized_continuum_summary :
    -- König at every ordinal
    (∀ α : Ordinal.{0}, aleph α < ((2 : Cardinal.{0}) ^ aleph α).ord.cof.card) ∧
    -- Cantor at every ordinal
    (∀ α : Ordinal.{0}, aleph α < (2 : Cardinal.{0}) ^ aleph α) ∧
    -- Monotonicity
    (∀ α β : Ordinal.{0}, α ≤ β →
      (2 : Cardinal.{0}) ^ aleph α ≤ (2 : Cardinal.{0}) ^ aleph β) :=
  ⟨konig_aleph_general, two_pow_aleph_gt_aleph, fun α β h => two_pow_aleph_mono h⟩

end CantorDiagGeneralized
