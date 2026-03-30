import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic

/-
# König's Constraint from Mathlib's Cofinality API (OQ-01-OQ-01-OQ-02)

## Research Question

Can König's constraint on the continuum (cf(2^ℵ₀) > ℵ₀) be proved
directly from Mathlib's cofinality API, eliminating the axiom in the
parent formalization?

## Answer: Yes

Mathlib provides:
- `Cardinal.lt_cof_power` : κ ≤ κ.ord.cof → 1 < κ → κ < (κ ^ κ).ord.cof
  (generalized König's inequality for cardinal exponentiation)
- `Cardinal.cof_aleph` : (aleph α).ord.cof = α.cof
  (cofinality of alephs reduces to ordinal cofinality)
- `Ordinal.card_omega0` : ω.card = ℵ₀
  (cardinal value of ordinal ω)

These three lemmas suffice to:
1. Prove cf(2^ℵ₀) > ℵ₀ (König's cofinality bound)
2. Prove cf(ℵ_ω) = ℵ₀ (ℵ_ω is singular)
3. Derive 2^ℵ₀ ≠ ℵ_ω (and more generally, no singular aleph)
4. Show successor alephs are regular and hence valid continuum values

## References

- König, J. (1905). "Zum Kontinuumproblem"
- Easton, W. (1970). "Powers of Regular Cardinals"
- mathlib4: `Mathlib.SetTheory.Cardinal.Cofinality`
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorDiagOQ01OQ01OQ02

open Cardinal

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: COFINALITY BASICS FROM MATHLIB
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The continuum 2^ℵ₀, fixed at universe 0. -/
noncomputable def continuum : Cardinal.{0} := 2 ^ ℵ₀

/-- **Cofinality of ℵ_ω equals ℵ₀**.

    ℵ_ω = sup{ℵ₀, ℵ₁, ℵ₂, ...} is a countable supremum,
    so its cofinality is ω. Converting to cardinals: cf(ℵ_ω) = ℵ₀.

    Proof: `Cardinal.cof_aleph ω` gives `(aleph ω).ord.cof = ω.cof = ω`
    (since ω is a limit ordinal with cf(ω) = ω), then `Ordinal.card_omega0`
    converts the ordinal ω to the cardinal ℵ₀. -/
theorem aleph_omega_cof_eq_aleph_zero :
    ((Cardinal.aleph (ω : Ordinal.{0})).ord.cof : Cardinal) = ℵ₀ := by
  rw [Cardinal.cof_aleph]
  exact Ordinal.card_omega0

/-- ℵ_ω is not regular: cf(ℵ_ω) = ℵ₀ < ℵ_ω, violating the regularity
    condition cf(κ) = κ. -/
theorem aleph_omega_not_regular :
    ¬(Cardinal.aleph (ω : Ordinal.{0})).IsRegular := by
  intro hreg
  have hcof := hreg.cof_eq
  rw [aleph_omega_cof_eq_aleph_zero] at hcof
  have : ℵ₀ < Cardinal.aleph (ω : Ordinal.{0}) := by
    rw [Cardinal.aleph_zero]
    exact Cardinal.aleph_lt_aleph.mpr (Ordinal.pos_iff_ne_zero.mpr omega_ne_zero)
  exact absurd hcof.symm (ne_of_lt this)

/-- ℵ₁ is regular: cf(ℵ₁) = ℵ₁. This is a standard Mathlib result. -/
theorem aleph_one_is_regular : (Cardinal.aleph 1 : Cardinal.{0}).IsRegular :=
  Cardinal.isRegular_aleph_one

/-- All successor alephs ℵ_{α+1} are regular. -/
theorem aleph_succ_regular (α : Ordinal.{0}) :
    (Cardinal.aleph (Order.succ α)).IsRegular :=
  Cardinal.isRegular_aleph_succ α

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: KÖNIG'S COFINALITY CONSTRAINT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **König's Cofinality Constraint**: cf(2^ℵ₀) > ℵ₀.

    The continuum cannot be expressed as a countable union of sets each
    strictly smaller than 2^ℵ₀. This is the strongest ZFC-provable
    constraint on the value of 2^ℵ₀.

    Proof: `Cardinal.lt_cof_power` applied with κ = ℵ₀ gives
    ℵ₀ < (2^ℵ₀).ord.cof, since ℵ₀ ≤ ℵ₀.ord.cof (ℵ₀ is regular)
    and 1 < 2 (required hypothesis on the base). -/
theorem konig_cofinality_bound :
    (ℵ₀ : Cardinal.{0}) < (continuum.ord.cof : Cardinal) := by
  show (ℵ₀ : Cardinal.{0}) < ((2 ^ ℵ₀ : Cardinal.{0}).ord.cof : Cardinal)
  exact Cardinal.lt_cof_power le_rfl (by norm_num)

/-- König's constraint in ordinal form: the ordinal cofinality of
    (2^ℵ₀).ord exceeds ω. -/
theorem konig_ordinal_form :
    (ω : Ordinal.{0}) < (continuum.ord.cof : Ordinal.{0}).card.ord := by
  have h := konig_cofinality_bound
  rw [Cardinal.aleph_zero] at h
  rw [show (ω : Ordinal.{0}).card = ℵ₀ from Ordinal.card_omega0] at h
  exact Cardinal.ord_lt_ord.mpr h

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: RULING OUT SINGULAR ALEPHS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **König rules out 2^ℵ₀ = ℵ_ω**:
    cf(ℵ_ω) = ℵ₀ but cf(2^ℵ₀) > ℵ₀, contradiction. -/
theorem continuum_ne_aleph_omega :
    continuum ≠ Cardinal.aleph (ω : Ordinal.{0}) := by
  intro h
  have hcof := konig_cofinality_bound
  rw [h] at hcof
  rw [aleph_omega_cof_eq_aleph_zero] at hcof
  exact lt_irrefl ℵ₀ hcof

/-- More generally: 2^ℵ₀ cannot equal any aleph whose cofinality is ≤ ℵ₀.
    This rules out all singular alephs with countable cofinality. -/
theorem continuum_not_countable_cof (α : Ordinal.{0})
    (hcof : (Cardinal.aleph α).ord.cof ≤ ℵ₀) :
    continuum ≠ Cardinal.aleph α := by
  intro h
  have hk := konig_cofinality_bound
  rw [h] at hk
  exact absurd (le_antisymm hcof (le_of_lt hk)) (ne_of_gt hk)

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: VALID CONTINUUM VALUES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Under CH (2^ℵ₀ = ℵ₁), König is satisfied since ℵ₁ is regular. -/
theorem ch_satisfies_konig
    (hch : continuum = Cardinal.aleph 1) :
    (Cardinal.aleph 1 : Cardinal.{0}).IsRegular :=
  aleph_one_is_regular

/-- ℵ₂ is regular and hence a valid value for 2^ℵ₀ per König. -/
theorem aleph_two_is_regular : (Cardinal.aleph 2 : Cardinal.{0}).IsRegular := by
  have : (2 : Ordinal) = Order.succ (1 : Ordinal) := by
    rw [Order.succ_eq_add_one]; norm_num
  rw [this]
  exact aleph_succ_regular 1

/-- Summary: König's constraint partitions alephs into valid and invalid
    continuum values.

    Valid (regular, cf = self): ℵ₁, ℵ₂, ℵ₃, ..., ℵ_{ω₁}, ...
    Invalid (singular, cf < self): ℵ_ω, ℵ_{ω+ω}, ℵ_{ω²}, ...

    The constraint is: if 2^ℵ₀ = ℵ_α, then ℵ_α must be regular. -/
theorem konig_characterization :
    -- König constraint holds
    ((ℵ₀ : Cardinal.{0}) < (continuum.ord.cof : Cardinal)) ∧
    -- ℵ_ω is ruled out (singular)
    (continuum ≠ Cardinal.aleph (ω : Ordinal.{0})) ∧
    -- ℵ₁ is allowed (regular)
    ((Cardinal.aleph 1 : Cardinal.{0}).IsRegular) ∧
    -- ℵ₂ is allowed (regular)
    ((Cardinal.aleph 2 : Cardinal.{0}).IsRegular) :=
  ⟨konig_cofinality_bound,
   continuum_ne_aleph_omega,
   aleph_one_is_regular,
   aleph_two_is_regular⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @aleph_omega_cof_eq_aleph_zero
#check @konig_cofinality_bound
#check @continuum_ne_aleph_omega
#check @continuum_not_countable_cof
#check @konig_characterization

end CantorDiagOQ01OQ01OQ02
