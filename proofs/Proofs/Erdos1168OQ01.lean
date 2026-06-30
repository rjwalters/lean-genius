/-
Erdős Problem #1168 — follow-up OQ-01:
The ZFC lower bound  ℵ_{ω+1} ≤ ℵ_ω^{ℵ₀}  on the singular-cardinal power.

Source: https://erdosproblems.com/1168
Related file: Proofs/Erdos1168Problem.lean (the parent partition-relation entry)

Context (pcf theory / singular cardinal arithmetic):
The open question oq-01 attached to Erdős #1168 asks to "encode pcf theory in
Lean 4 using Mathlib's ordinal/cardinal infrastructure." pcf theory (Shelah)
is, at heart, the study of the cardinal arithmetic of singular cardinals — and
its single most famous concrete consequence is the ZFC bound

        ℵ_ω^{ℵ₀} < ℵ_{ω₄}      (Shelah, 1990s)

which controls the power ℵ_ω^{ℵ₀} of the first singular cardinal *without* GCH.
That upper bound is deep (it is the payoff of the whole pcf machinery). The
matching *lower* bound, by contrast, is elementary and provable in pure ZFC
straight from König's theorem:

        ℵ_{ω+1} ≤ ℵ_ω^{ℵ₀} ≤ 2^{ℵ_ω}.

This file formalizes that elementary half. It is the natural first brick of a
pcf encoding: it pins the bottom of the interval that pcf theory squeezes from
above, and it isolates the general "singular cardinal inequality"
κ⁺ ≤ κ^{cf κ} that underlies the whole subject.

The cofinality consequences of König's lemma (`Cardinal.lt_power_cof`,
`Cardinal.lt_cof_power`) are already in Mathlib; the singular-cardinal *power
successor* bound and its specialization to ℵ_ω are not. Everything here is
0-axiom and self-contained (the file rebuilds the small amount of ℵ_ω cardinal
infrastructure it needs rather than importing it). Note: a sibling gallery file
axiomatizes König's continuum cofinality bound; the same fact is in fact
provable, and we use the provable form.

Tags: set-theory, cardinal-arithmetic, pcf-theory, singular-cardinals, koenig
-/

import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic

open Cardinal Ordinal

namespace Erdos1168OQ01

/- ## Part 0: Cardinal infrastructure for ℵ_ω

ℵ_ω is the first singular cardinal: it is the supremum of the ℵ_n and has
cofinality ℵ₀. We record the few facts about ℵ_ω and its successor ℵ_{ω+1} that
the main results need. -/

/-- The cardinal ℵ_ω = ℵ_(ω): the first singular cardinal. -/
noncomputable def aleph_omega : Cardinal := Cardinal.aleph Ordinal.omega0

/-- The cardinal ℵ_{ω+1} = ℵ_(ω+1): the successor of the first singular cardinal. -/
noncomputable def aleph_omega_succ : Cardinal :=
  Cardinal.aleph (Order.succ Ordinal.omega0)

/-- ℵ_{ω+1} = Order.succ ℵ_ω: the successor-cardinal identity, from
    `Cardinal.aleph_succ`. -/
theorem aleph_omega_succ_eq_succ : aleph_omega_succ = Order.succ aleph_omega := by
  unfold aleph_omega_succ aleph_omega
  rw [Cardinal.aleph_succ]

/-- ℵ₀ < ℵ_ω: the first singular cardinal is uncountable. -/
theorem aleph0_lt_aleph_omega : ℵ₀ < aleph_omega := by
  unfold aleph_omega
  rw [← Cardinal.aleph_zero]
  exact Cardinal.aleph_lt_aleph.mpr Ordinal.omega0_pos

/-- ℵ_ω is singular: cf(ℵ_ω) = ℵ₀. The cofinality of the ω-th initial ordinal
    equals the cofinality of ω, namely ℵ₀. -/
theorem aleph_omega_cof : aleph_omega.ord.cof = ℵ₀ := by
  unfold aleph_omega
  rw [Cardinal.ord_aleph, Ordinal.cof_omega Ordinal.isSuccLimit_omega0,
    Ordinal.cof_omega0]

/- ## Part I: The general singular cardinal inequality (König)

For every infinite cardinal κ, König's theorem gives κ < κ^{cf κ}. Hence the
successor cardinal κ⁺ already lies below κ^{cf κ}. When κ is *singular*
(cf κ < κ) this is a genuine constraint on the cardinal arithmetic of κ; it is
the elementary engine behind pcf theory. -/

/-- König's singular cardinal inequality: an infinite cardinal is strictly below
    its own cofinal power. This is `Cardinal.lt_power_cof`, recorded here as the
    starting point. -/
theorem lt_power_cof_of_aleph0_le (κ : Cardinal) (hκ : ℵ₀ ≤ κ) :
    κ < κ ^ κ.ord.cof :=
  Cardinal.lt_power_cof hκ

/-- The successor form: for every infinite cardinal κ, the successor κ⁺ is at
    most κ^{cf κ}. (For regular κ this just says κ⁺ ≤ κ^κ; for singular κ it is
    the basic pcf constraint κ⁺ ≤ κ^{cf κ}.) -/
theorem succ_le_power_cof (κ : Cardinal) (hκ : ℵ₀ ≤ κ) :
    Order.succ κ ≤ κ ^ κ.ord.cof :=
  Order.succ_le_of_lt (Cardinal.lt_power_cof hκ)

/- ## Part II: Specialization to ℵ_ω

Plugging cf(ℵ_ω) = ℵ₀ into the inequalities above yields the concrete lower
bound on ℵ_ω^{ℵ₀}. -/

/-- ℵ_ω < ℵ_ω^{ℵ₀}: König applied at the singular cardinal ℵ_ω.
    Since cf(ℵ_ω) = ℵ₀ < ℵ_ω, the power ℵ_ω^{ℵ₀} strictly exceeds ℵ_ω. -/
theorem aleph_omega_lt_power : aleph_omega < aleph_omega ^ (ℵ₀ : Cardinal) := by
  have h := Cardinal.lt_power_cof (c := aleph_omega) aleph0_lt_aleph_omega.le
  rwa [aleph_omega_cof] at h

/-- **Main result (lower bound).** ℵ_{ω+1} ≤ ℵ_ω^{ℵ₀}.

    The successor of the first singular cardinal is bounded above by its
    countable power. This is the elementary ZFC half of the famous pcf bound
    ℵ_{ω+1} ≤ ℵ_ω^{ℵ₀} < ℵ_{ω₄}; the upper inequality is Shelah's deep theorem,
    while this lower inequality is immediate from König's theorem. -/
theorem aleph_omega_succ_le_power :
    aleph_omega_succ ≤ aleph_omega ^ (ℵ₀ : Cardinal) := by
  rw [aleph_omega_succ_eq_succ]
  exact Order.succ_le_of_lt aleph_omega_lt_power

/- ## Part III: The matching upper bound and the pcf interval

ℵ_ω^{ℵ₀} ≤ 2^{ℵ_ω}: the countable power never exceeds the full power set.
Together with Part II this traps ℵ_ω^{ℵ₀} in the interval [ℵ_{ω+1}, 2^{ℵ_ω}].
pcf theory's contribution is the far sharper ZFC upper bound ℵ_ω^{ℵ₀} < ℵ_{ω₄},
which lives inside this elementary interval. -/

/-- ℵ_ω^{ℵ₀} ≤ 2^{ℵ_ω}: the countable power is dominated by the power set.
    Uses ℵ_ω ≤ 2^{ℵ_ω} (Cantor) and ℵ_ω · ℵ₀ = ℵ_ω (cardinal absorption). -/
theorem power_le_two_pow_aleph_omega :
    aleph_omega ^ (ℵ₀ : Cardinal) ≤ 2 ^ aleph_omega := by
  calc aleph_omega ^ (ℵ₀ : Cardinal)
      ≤ (2 ^ aleph_omega) ^ (ℵ₀ : Cardinal) :=
        power_le_power_right (Cardinal.cantor aleph_omega).le
    _ = 2 ^ (aleph_omega * ℵ₀) := by rw [← power_mul]
    _ = 2 ^ aleph_omega := by
        rw [Cardinal.mul_eq_max aleph0_lt_aleph_omega.le le_rfl,
          max_eq_left aleph0_lt_aleph_omega.le]

/-- The pcf interval for ℵ_ω^{ℵ₀}: ℵ_{ω+1} ≤ ℵ_ω^{ℵ₀} ≤ 2^{ℵ_ω}, in ZFC.
    The deep pcf upper bound ℵ_ω^{ℵ₀} < ℵ_{ω₄} (Shelah) refines the right end. -/
theorem aleph_omega_power_interval :
    aleph_omega_succ ≤ aleph_omega ^ (ℵ₀ : Cardinal) ∧
      aleph_omega ^ (ℵ₀ : Cardinal) ≤ 2 ^ aleph_omega :=
  ⟨aleph_omega_succ_le_power, power_le_two_pow_aleph_omega⟩

/-- Corollary: ℵ_ω^{ℵ₀} ≠ ℵ_ω. Unlike a regular cardinal, the singular cardinal
    ℵ_ω is not closed under its own cofinal power — exponentiation by ℵ₀
    strictly increases it. -/
theorem aleph_omega_ne_power : aleph_omega ≠ aleph_omega ^ (ℵ₀ : Cardinal) :=
  ne_of_lt aleph_omega_lt_power

/- ## Part IV: König cofinality of the power itself

A second consequence of König's theorem: the power ℵ_ω^{ℵ₀} has uncountable
cofinality. This is `Cardinal.lt_cof_power` with base ℵ_ω and exponent ℵ₀, and
it shows ℵ_ω^{ℵ₀} can itself never be a cardinal of countable cofinality (e.g.
it is never of the form ℵ_{ω+ω} with cofinality ω). -/

/-- cf(ℵ_ω^{ℵ₀}) > ℵ₀: König's theorem forces the countable power of ℵ_ω to have
    uncountable cofinality. -/
theorem aleph0_lt_cof_power :
    ℵ₀ < (aleph_omega ^ (ℵ₀ : Cardinal)).ord.cof :=
  Cardinal.lt_cof_power le_rfl (one_lt_aleph0.trans aleph0_lt_aleph_omega)

end Erdos1168OQ01
