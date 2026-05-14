import Proofs.CantorDiagonalizationOQ01OQ01OQ02OQ01

/-
# Permitted Values for the Continuum — Phase-3b: ConsistencyOf predicate
  (OQ-01-OQ-01-OQ-02-OQ-01 sibling extension)

## What This File Adds

The parent file `CantorDiagonalizationOQ01OQ01OQ02OQ01.lean` axiomatizes
Easton's 1970 consistency theorem with a `True` codomain placeholder:

  axiom easton_permitted_realizable :
      ∀ κ : Cardinal.{0}, IsPermittedValue κ → True
  axiom easton_consistency :
      ∀ F : Cardinal.{0} → Cardinal.{0}, IsEastonFunction F → True

The `True` codomain renders the axioms VACUOUSLY satisfied — callers
who apply them receive only `trivial : True`, no mathematical content.
This file introduces abstract consistency predicates and strengthened
axioms that pin down what discharge of the parent axioms WOULD mean,
making the mathematical content of Easton's theorem explicit at the
type level.

## Honesty: Deeper Axiomatization, Not Axiom Reduction

Adding `ConsistencyOf` axioms does NOT reduce the total axiom count.
The parent file's 2 vacuous axioms remain; this file adds 4 new
axioms (2 predicates + 2 strong claims) with genuine mathematical
content. The trade is: callers built on the strong axioms produce
non-trivial terms (e.g. `ConsistencyOfContinuumValue (Cardinal.aleph 1)`
rather than `True`), and a future flypitch-style discharge has a clear
target type to instantiate.

A future Phase-4 effort would port flypitch's Cohen-forcing model to
Lean 4 and extend it to Easton-style class forcing, discharging
`easton_consistency_strong` as a theorem; that work is multi-session
and out of scope for Phase-3b.

## References

- Easton (1970): "Powers of regular cardinals." Annals of Math. Logic 1.
- Han, Van Doorn (2020): flypitch — Cohen forcing for CH-independence (Lean 3).
- Jech (2003): Set Theory, Ch. 15.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorDiagOQ01OQ01OQ02OQ01

open Cardinal

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: ABSTRACT CONSISTENCY PREDICATES (PHASE-3B)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Pointwise consistency predicate** (axiomatized abstract predicate).

    `ConsistencyOfContinuumValue κ` is read as "the theory
    ZFC ∪ {2^ℵ₀ = κ} is consistent, assuming Con(ZFC)".

    The predicate is left abstract because expressing it in Lean would
    require Gödel-encoding ZFC formulas — infrastructure not yet in
    Mathlib. A future Phase-4 port of `flypitch` (Han–Van Doorn 2020,
    Lean 3) would provide a `Consistent : Set Formula → Prop`
    predicate against which this could be discharged. -/
axiom ConsistencyOfContinuumValue : Cardinal.{0} → Prop

/-- **Function-level consistency predicate** (axiomatized abstract predicate).

    `ConsistencyOfContinuumFunction F` is read as "the theory
    ZFC ∪ {∀ regular κ ≥ ℵ₀: 2^κ = F κ} is consistent, assuming
    Con(ZFC)".

    Same abstraction rationale as `ConsistencyOfContinuumValue`. The
    function-level form is the one actually proved by Easton 1970 via
    class forcing; the pointwise form is its restriction to κ = ℵ₀. -/
axiom ConsistencyOfContinuumFunction : (Cardinal.{0} → Cardinal.{0}) → Prop

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: STRONG EASTON AXIOMS (REPLACE PARENT'S `True` CODOMAIN)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Strong Easton 1970 (pointwise form)**: every permitted value is
    realizable as 2^ℵ₀ in some forcing extension of ZFC.

    This is the parent's `easton_permitted_realizable` with the `True`
    codomain replaced by `ConsistencyOfContinuumValue κ`, making the
    mathematical content of the claim explicit. Unlike the parent
    axiom, this version cannot be trivially discharged: producing a
    term of type `ConsistencyOfContinuumValue κ` requires the
    flypitch-port infrastructure plus Easton's forcing construction. -/
axiom easton_permitted_realizable_strong :
    ∀ κ : Cardinal.{0}, IsPermittedValue κ → ConsistencyOfContinuumValue κ

/-- **Strong Easton 1970 (function-level form)**: every Easton function
    is realizable as the continuum function on regular cardinals in
    some forcing extension of ZFC.

    Parent's `easton_consistency` with `True` codomain replaced by
    `ConsistencyOfContinuumFunction F`. Discharge requires the same
    class-forcing infrastructure as the pointwise version. -/
axiom easton_consistency_strong :
    ∀ F : Cardinal.{0} → Cardinal.{0}, IsEastonFunction F →
      ConsistencyOfContinuumFunction F

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: DERIVED CONSISTENCY THEOREMS (CALLABLE CONTENT)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The actual continuum function `κ ↦ 2^κ` is a consistent continuum
    function. The trivial witness — the ground model is its own
    forcing extension. Uses `isEastonFunction_continuum` from the
    parent file as the input to `easton_consistency_strong`.

    Contrast with the parent's `easton_consistency` applied to the
    same input: that produced only `trivial : True`, while this
    corollary produces a term of type
    `ConsistencyOfContinuumFunction (fun κ => 2^κ)` that downstream
    callers can cite. -/
theorem consistencyOfContinuumFunction_continuum :
    ConsistencyOfContinuumFunction (fun κ => (2 : Cardinal.{0}) ^ κ) :=
  easton_consistency_strong _ isEastonFunction_continuum

/-- ℵ₁ is a consistent continuum value: this is the CH model
    (Cohen 1963 lower bound on the strength of forcing). -/
theorem consistencyOfContinuumValue_aleph_one :
    ConsistencyOfContinuumValue (Cardinal.aleph 1) :=
  easton_permitted_realizable_strong _ aleph_one_permitted

/-- ℵ₂ is a consistent continuum value: this is the PFA-compatible
    value used by Todorcevic, Veličković, and others. -/
theorem consistencyOfContinuumValue_aleph_two :
    ConsistencyOfContinuumValue (Cardinal.aleph 2) :=
  easton_permitted_realizable_strong _ aleph_two_permitted

/-- Every successor aleph ℵ_{α+1} is a consistent continuum value.
    Combined with `permitted_unbounded` from the parent file, this
    confirms that the consistent continuum values form a proper class
    — there is no large-cardinal upper bound. -/
theorem consistencyOfContinuumValue_aleph_succ (α : Ordinal.{0}) :
    ConsistencyOfContinuumValue (Cardinal.aleph (Order.succ α)) :=
  easton_permitted_realizable_strong _ (aleph_succ_permitted α)

/-- The consistent continuum values are unbounded: above every aleph
    there is a strictly larger consistent value. Restates
    `permitted_unbounded` from the parent in `ConsistencyOf` form. -/
theorem consistencyOfContinuumValue_unbounded :
    ∀ α : Ordinal.{0}, ∃ κ : Cardinal.{0},
      Cardinal.aleph α < κ ∧ ConsistencyOfContinuumValue κ := by
  intro α
  obtain ⟨κ, hlt, hperm⟩ := permitted_unbounded α
  exact ⟨κ, hlt, easton_permitted_realizable_strong κ hperm⟩

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @ConsistencyOfContinuumValue
#check @ConsistencyOfContinuumFunction
#check @easton_permitted_realizable_strong
#check @easton_consistency_strong
#check @consistencyOfContinuumFunction_continuum
#check @consistencyOfContinuumValue_aleph_one
#check @consistencyOfContinuumValue_aleph_two
#check @consistencyOfContinuumValue_aleph_succ
#check @consistencyOfContinuumValue_unbounded

end CantorDiagOQ01OQ01OQ02OQ01
