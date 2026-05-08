import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic

/-
# Permitted Values for the Continuum (OQ-01-OQ-01-OQ-02-OQ-01)

## Research Question

The parent file `CantorDiagonalizationOQ01OQ01OQ02.lean` ENUMERATES which
cardinals are EXCLUDED as values of 2^ℵ₀ (singular cardinals: ℵ_ω and any
cardinal of cofinality ≤ ℵ₀). This file formalizes the CONVERSE direction:
every regular cardinal κ ≥ ℵ₁ is a PERMITTED value, i.e., consistent with
both Cantor's lower bound and König's cofinality constraint.

Easton's 1970 theorem states that every permitted value is REALIZABLE as
2^ℵ₀ in some forcing extension of ZFC. Its proof requires class forcing,
not yet formalized in Lean. We therefore axiomatize the consistency claim
and develop the object-level scaffold around it.

## What This File Proves (from Mathlib, axiom-free)

### Permitted values (pointwise):
1. `IsPermittedValue κ` — predicate: κ is regular and uncountable
2. `permitted_satisfies_konig` — every permitted value satisfies cf(κ) > ℵ₀
3. `aleph_one_permitted` — ℵ₁ is permitted (CH value)
4. `aleph_two_permitted` — ℵ₂ is permitted (PFA value)
5. `aleph_succ_permitted` — every successor aleph is permitted
6. `permitted_unbounded` — the permitted-value class is proper (unbounded)

### Easton functions (function-level):
7. `IsEastonFunction F` — structure capturing the three Easton constraints
8. `isEastonFunction_continuum` — `κ ↦ 2^κ` is an Easton function (all three
   constraints proved axiom-free: (E1) Cantor, (E2) exponent monotonicity via
   `Cardinal.power_le_power_left` (note: `_left` varies the exponent in
   current Mathlib, `_right` varies the base), (E3) König via
   `Cardinal.lt_cof_power`)
9. `isEastonFunction_nonempty` — the constraint set is non-vacuous

## What This File Axiomatizes (proof requires class forcing)

10. `easton_permitted_realizable` — every permitted value is realizable
11. `easton_consistency` — every Easton function is realizable

The True codomain on these axioms is a placeholder. A future Phase-3b
file will introduce `ConsistencyOf : (Cardinal → Cardinal) → Prop`
(requires Gödel-encoding ZFC) and re-state the axioms in those terms.

## References

- Easton, W. (1970). "Powers of regular cardinals." Annals of Math. Logic 1.
- Cohen, P. (1963). "The independence of the continuum hypothesis."
- Han, Van Doorn (2020). "A formal proof of the independence of CH" (flypitch, Lean 3).
- Jech, T. (2003). Set Theory, Springer. Chapter 15: Easton's theorem.
- Mathlib: `Cardinal.lt_cof_power` (König), `Cardinal.cantor`, `Cardinal.power_le_power_left`,
  `Cardinal.isRegular_aleph_succ`, `IsRegular.cof_eq`.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorDiagOQ01OQ01OQ02OQ01

open Cardinal

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: PERMITTED VALUES — POINTWISE CHARACTERIZATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A cardinal κ is a **permitted value** for 2^ℵ₀ if it is regular and
    uncountable. These are exactly the values consistent with the two
    ZFC-provable constraints on the continuum:
    (1) Cantor's lower bound: 2^ℵ₀ > ℵ₀
    (2) König's constraint: cf(2^ℵ₀) > ℵ₀

    By Easton 1970, these conditions are also SUFFICIENT: every permitted
    value is realizable as 2^ℵ₀ in some forcing extension (axiomatized
    in Part III since the proof uses class forcing). -/
def IsPermittedValue (κ : Cardinal.{0}) : Prop :=
  κ.IsRegular ∧ ℵ₀ < κ

/-- Every permitted value satisfies König's cofinality constraint cf(κ) > ℵ₀.
    This is the object-level (no-forcing) verification that the permitted
    values do not violate the König obstruction. -/
theorem permitted_satisfies_konig (κ : Cardinal.{0}) (h : IsPermittedValue κ) :
    κ.ord.cof > ℵ₀ := by
  rcases h with ⟨hreg, hgt⟩
  rw [hreg.cof_eq]
  exact hgt

/-- ℵ₁ is permitted: this is the CH value, 2^ℵ₀ = ℵ₁.

    ℵ₁ is regular (every successor aleph is) and ℵ₁ > ℵ₀ since
    aleph is strictly monotone. -/
theorem aleph_one_permitted : IsPermittedValue (Cardinal.aleph 1) := by
  refine ⟨Cardinal.isRegular_aleph_one, ?_⟩
  -- ℵ₀ < ℵ_ 1 via the chain ℵ_ 1 = ℵ_ (succ 0) = succ (ℵ_ 0) = succ ℵ₀.
  -- Note: (1 : Ordinal) = Order.succ 0 is NOT rfl in current Mathlib —
  -- need to unfold via Order.succ_eq_add_one + zero_add.
  rw [show (1 : Ordinal.{0}) = Order.succ 0 from by rw [Order.succ_eq_add_one, zero_add],
      Cardinal.aleph_succ, Cardinal.aleph_zero]
  exact Order.lt_succ _

/-- ℵ₂ is permitted: this is the PFA value, 2^ℵ₀ = ℵ₂. -/
theorem aleph_two_permitted : IsPermittedValue (Cardinal.aleph 2) := by
  -- ℵ_2 = ℵ_(succ 1) = succ (ℵ_ 1) = succ (succ ℵ₀).
  rw [show (2 : Ordinal.{0}) = Order.succ 1 from by rw [Order.succ_eq_add_one, one_add_one_eq_two]]
  refine ⟨Cardinal.isRegular_aleph_succ 1, ?_⟩
  rw [Cardinal.aleph_succ,
      show (1 : Ordinal.{0}) = Order.succ 0 from by rw [Order.succ_eq_add_one, zero_add],
      Cardinal.aleph_succ, Cardinal.aleph_zero]
  exact lt_trans (Order.lt_succ _) (Order.lt_succ _)

/-- Every successor aleph ℵ_{α+1} is permitted. The successor alephs
    form an inexhaustible supply of permitted values. -/
theorem aleph_succ_permitted (α : Ordinal.{0}) :
    IsPermittedValue (Cardinal.aleph (Order.succ α)) := by
  refine ⟨Cardinal.isRegular_aleph_succ α, ?_⟩
  -- ℵ₀ < ℵ_(succ α) via the chain ℵ₀ = ℵ_0 ≤ ℵ_α < succ (ℵ_α) = ℵ_(succ α).
  rw [Cardinal.aleph_succ]
  refine lt_of_le_of_lt ?_ (Order.lt_succ _)
  rw [← Cardinal.aleph_zero]
  exact Cardinal.aleph_le_aleph.mpr (zero_le α)

/-- The permitted values form a proper class: for every ordinal α, there
    is a permitted value strictly above ℵ_α (namely ℵ_{α+1}).

    This rules out the possibility that 2^ℵ₀ is bounded by some specific
    cardinal — the Easton spectrum has no upper bound. -/
theorem permitted_unbounded :
    ∀ α : Ordinal.{0}, ∃ κ : Cardinal.{0},
      Cardinal.aleph α < κ ∧ IsPermittedValue κ := by
  intro α
  refine ⟨Cardinal.aleph (Order.succ α), ?_, aleph_succ_permitted α⟩
  -- ℵ_ α < ℵ_ (succ α) via aleph_succ: ℵ_ (succ α) = succ (ℵ_ α) > ℵ_ α
  rw [Cardinal.aleph_succ]
  exact Order.lt_succ _

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: EASTON FUNCTIONS — FUNCTION-LEVEL CONSTRAINTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- An **Easton function** F : Cardinal → Cardinal must satisfy three
    constraints on every regular infinite cardinal κ:

    (E1) `succ_le`: F(κ) ≥ Order.succ κ — exceed the immediate successor
                     (Cantor's bound generalized: 2^κ > κ ⇒ 2^κ ≥ κ⁺)
    (E2) `monotone`: F is monotone on regular cardinals
                     (κ ≤ λ ⟹ 2^κ ≤ 2^λ generalized)
    (E3) `konig_pointwise`: cf(F(κ)) > κ — König's constraint

    Easton 1970 shows that these three constraints are jointly NECESSARY
    AND SUFFICIENT: any function satisfying them is realizable as the
    continuum function on regular cardinals in some forcing extension. -/
structure IsEastonFunction (F : Cardinal.{0} → Cardinal.{0}) : Prop where
  succ_le : ∀ κ : Cardinal.{0}, κ.IsRegular → ℵ₀ ≤ κ → Order.succ κ ≤ F κ
  monotone : ∀ κ ν : Cardinal.{0},
              κ.IsRegular → ν.IsRegular → ℵ₀ ≤ κ → κ ≤ ν → F κ ≤ F ν
  -- Note: Ordinal.cof returns Cardinal directly in current Mathlib
  -- (no .card accessor needed); see Proofs.CantorDiagonalizationOQ01OQ01OQ02OQ03 for context.
  konig_pointwise : ∀ κ : Cardinal.{0}, κ.IsRegular → ℵ₀ ≤ κ →
                      κ < (F κ).ord.cof

/-- The actual continuum function `κ ↦ 2^κ` is an Easton function. All
    three constraints are provable from Mathlib without forcing:
    - (E1) `succ_le` follows from Cantor's theorem κ < 2^κ
    - (E2) `monotone` uses `Cardinal.power_le_power_left` (exponent
      monotonic with fixed nonzero base — note the Mathlib naming
      convention: `power_le_power_left` varies the EXPONENT, while
      `power_le_power_right` varies the BASE). The base hypothesis
      `(2 : Cardinal) ≠ 0` is discharged by `norm_num`.
    - (E3) `konig_pointwise` is exactly `Cardinal.lt_cof_power` (König's
      theorem). -/
theorem isEastonFunction_continuum :
    IsEastonFunction (fun κ => (2 : Cardinal.{0}) ^ κ) where
  succ_le κ _ _ := Order.succ_le_of_lt (Cardinal.cantor κ)
  monotone _ _ _ _ _ hκν :=
    Cardinal.power_le_power_left (by norm_num : (2 : Cardinal.{0}) ≠ 0) hκν
  konig_pointwise κ _ hℵ₀ := Cardinal.lt_cof_power hℵ₀ (by norm_num)

/-- The Easton-function constraint set is non-vacuous: the continuum
    function `κ ↦ 2^κ` witnesses it. This means Easton's consistency
    claim (Part III) is not vacuously true — there exist functions to
    which the axiom applies. -/
theorem isEastonFunction_nonempty :
    ∃ F : Cardinal.{0} → Cardinal.{0}, IsEastonFunction F :=
  ⟨_, isEastonFunction_continuum⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: EASTON CONSISTENCY — AXIOMATIZED (PROOF NEEDS CLASS FORCING)
═══════════════════════════════════════════════════════════════════════════════

The two axioms below state Easton's 1970 consistency theorem at two
granularities (pointwise and function-level). The proofs require:

  - Class-sized partial orders (Easton product forcing posets)
  - Generic filter constructions on proper classes
  - Forcing-language semantics for ZFC's class-comprehension schema

None of this infrastructure exists in Lean 4 / Mathlib. The closest
existing work is the `flypitch` project (Han, Van Doorn 2020), which
formalized Cohen's set forcing for CH-independence in Lean 3 — but
class-sized forcing has not been ported and is a strictly stronger
construction.

The `True` codomain on the axioms is a placeholder. A future Phase-3b
file will introduce `ConsistencyOf : (Cardinal → Cardinal) → Prop`
(requires Gödel-encoding ZFC formulas) and replace the placeholder
with the genuine consistency predicate.
-/

/-- **Axiom (Easton 1970, pointwise form)**: Every permitted value is
    realizable as 2^ℵ₀ in some forcing extension of ZFC.

    Concretely: for every regular κ > ℵ₀, the theory
    ZFC + (2^ℵ₀ = κ) is consistent (assuming Con(ZFC)).

    The codomain `True` is a Phase-3b placeholder; the genuine target
    is `Consistent (ZFC ∪ ⟦2^ℵ₀ = κ⟧)`. -/
axiom easton_permitted_realizable :
    ∀ κ : Cardinal.{0}, IsPermittedValue κ → True

/-- **Axiom (Easton 1970, function-level form)**: Every Easton function
    F : Cardinal → Cardinal is realizable as the continuum function
    on regular cardinals in some forcing extension of ZFC.

    Concretely: for every Easton function F, the theory
    ZFC + (∀ regular κ ≥ ℵ₀: 2^κ = F κ) is consistent (assuming Con(ZFC)).

    The codomain `True` is a Phase-3b placeholder; the genuine target
    is `Consistent (ZFC ∪ ⟦∀ κ regular: 2^κ = F κ⟧)`. -/
axiom easton_consistency :
    ∀ F : Cardinal.{0} → Cardinal.{0}, IsEastonFunction F → True

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @IsPermittedValue
#check @permitted_satisfies_konig
#check @aleph_one_permitted
#check @aleph_two_permitted
#check @aleph_succ_permitted
#check @permitted_unbounded
#check @IsEastonFunction
#check @isEastonFunction_continuum
#check @isEastonFunction_nonempty
#check @easton_permitted_realizable
#check @easton_consistency

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: PERMITTED-VALUE NON-EXAMPLES (S7, Phase-3a)
═══════════════════════════════════════════════════════════════════════════════

Part I gives positive examples of permitted values (ℵ₁, ℵ₂, every successor
aleph). The constraint set `IsPermittedValue` is purely object-level —
`IsRegular ∧ ℵ₀ < κ` — so non-examples come from the failure of EITHER
conjunct: a non-regular cardinal (e.g., ℵ_ω, cofinality ℵ₀), or a regular
cardinal that fails uncountability (i.e., ℵ₀ itself).

The latter is the only "boundary case": ℵ₀ is regular (`Cardinal.isRegular_aleph0`),
and yet not permitted, witnessing that Cantor's theorem (2^ℵ₀ > ℵ₀) is a
genuine constraint distinct from the regularity constraint Part I encodes.
The non-example reified below clarifies that the "ℵ₀ <" half of
`IsPermittedValue` is not redundant under regularity. -/

/-- ℵ₀ is NOT a permitted value: although `Cardinal.aleph0` is regular
    (`Cardinal.isRegular_aleph0`), the uncountability requirement `ℵ₀ < κ`
    fails — by `lt_irrefl` no cardinal is strictly less than itself.

    Mathematically, this is exactly Cantor's theorem 2^ℵ₀ > ℵ₀ enforced at
    the object level: even though ℵ₀ is regular (so the regularity half of
    `IsPermittedValue` succeeds), the strict-inequality clause `ℵ₀ < κ`
    excludes ℵ₀ — capturing the fact that the continuum cannot equal ℵ₀. -/
theorem not_permitted_aleph_zero : ¬ IsPermittedValue (ℵ₀ : Cardinal.{0}) := by
  rintro ⟨_, hgt⟩
  exact lt_irrefl _ hgt

#check @not_permitted_aleph_zero

end CantorDiagOQ01OQ01OQ02OQ01
