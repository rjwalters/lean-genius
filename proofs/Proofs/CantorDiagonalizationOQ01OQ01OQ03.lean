/-
The generalized continuum function: which patterns of 2^{ℵ_α} are consistent? (OQ-01-OQ-01-OQ-03)

Parent entry `cantor-diagonalization-oq-01-oq-01` ("The Continuum Hypothesis:
Independence and Consequences") formalizes CH and states König's constraint and Easton's
theorem at the level of `2^{ℵ₀}`, leaving as an open question:

  *What happens at the generalized continuum level — which patterns of `2^{ℵ_α}` are
  consistent?*

Easton's theorem (1970) answers this for regular cardinals: the **only** ZFC constraints
on the continuum function `α ↦ 2^{ℵ_α}` are (i) monotonicity, (ii) Cantor's strict
inequality `ℵ_α < 2^{ℵ_α}`, and (iii) König's constraint `cf(2^{ℵ_α}) > ℵ_α`; subject to
these, any pattern is consistent.  This file proves all three constraints **unconditionally
in ZFC and axiom-free**, directly from Mathlib's cardinal/cofinality API — in particular
discharging König's constraint (which the parent only stated) via
`Cardinal.lt_cof_power`.

Main results (writing `contFn α = 2 ^ ℵ_α`):
* `contFn_monotone`        — `α ≤ β → contFn α ≤ contFn β`.
* `aleph_lt_contFn`        — `ℵ_α < contFn α` (Cantor; the function strictly dominates its index).
* `aleph_lt_cof_contFn`    — `ℵ_α < cof(contFn α)` (König's constraint, generalized to all α).
* `aleph0_lt_cof_continuum`— the classical case `cf(2^{ℵ₀}) > ℵ₀`.
* `contFn_ne_aleph`        — the continuum function has no fixed point.

A subtlety worth recording: the continuum function is **monotone but not strictly
monotone** — `2^{ℵ_α} = 2^{ℵ_β}` for `α < β` is consistent (e.g. under Martin's Axiom) — so
only `≤`, not `<`, holds between distinct indices; the strict inequality is between an index
and *its own* value (Cantor).
-/

import Mathlib

namespace CantorDiagOQ010103

open Cardinal Ordinal

/-- The generalized continuum function `α ↦ 2 ^ ℵ_α`. -/
noncomputable def contFn (α : Ordinal.{0}) : Cardinal.{0} := 2 ^ (aleph α)

theorem two_ne_zero_card : (2 : Cardinal.{0}) ≠ 0 :=
  (zero_le_one.trans_lt one_lt_two).ne'

/-- **Monotonicity.** The continuum function is monotone: a larger index gives a
(weakly) larger power set. -/
theorem contFn_monotone {α β : Ordinal.{0}} (h : α ≤ β) : contFn α ≤ contFn β := by
  unfold contFn
  exact power_le_power_left two_ne_zero_card (aleph_le_aleph.mpr h)

/-- **Cantor's constraint.** The continuum function strictly dominates its index:
`ℵ_α < 2 ^ ℵ_α`. -/
theorem aleph_lt_contFn (α : Ordinal.{0}) : aleph α < contFn α :=
  Cardinal.cantor (aleph α)

/-- **König's constraint (generalized).** The cofinality of `2 ^ ℵ_α` exceeds `ℵ_α`:
`ℵ_α < cf(2 ^ ℵ_α)`.  This is the consequence of König's theorem that, together with
monotonicity and Cantor, exhausts the ZFC constraints on the continuum function. -/
theorem aleph_lt_cof_contFn (α : Ordinal.{0}) : aleph α < (contFn α).ord.cof :=
  lt_cof_power (aleph0_le_aleph α) one_lt_two

/-- **Classical König's constraint.** `cf(2 ^ ℵ₀) > ℵ₀`: the continuum cannot have
countable cofinality (so e.g. `2^{ℵ₀} ≠ ℵ_ω`). -/
theorem aleph0_lt_cof_continuum : ℵ₀ < (contFn 0).ord.cof := by
  have h := aleph_lt_cof_contFn 0
  rwa [aleph_zero] at h

/-- **No fixed point.** The continuum function never equals its index. -/
theorem contFn_ne_aleph (α : Ordinal.{0}) : contFn α ≠ aleph α :=
  (aleph_lt_contFn α).ne'

/-- **Admissibility, packaged.** Any consistent value of the generalized continuum
function satisfies all three ZFC constraints simultaneously: it dominates `ℵ_α`, has
cofinality above `ℵ_α`, and respects monotonicity. -/
theorem contFn_constraints (α : Ordinal.{0}) :
    aleph α < contFn α ∧ aleph α < (contFn α).ord.cof ∧
      ∀ β, α ≤ β → contFn α ≤ contFn β :=
  ⟨aleph_lt_contFn α, aleph_lt_cof_contFn α, fun _ h => contFn_monotone h⟩

end CantorDiagOQ010103
