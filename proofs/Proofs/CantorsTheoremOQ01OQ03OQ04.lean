import Proofs.CantorsTheoremOQ01
import Proofs.CantorsTheoremOQ01OQ03
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-
# Generalised Cofinality Exclusion for |𝒫(ℝ)|

## Open Question (resolved YES): cantors-theorem-oq-01-oq-03-oq-04

The parent file `CantorsTheoremOQ01OQ03.lean` proved (as one of its
seven main theorems) the canonical corollary

  `cf_powerSet_real_ne_aleph0 : (#(Set ℝ)).ord.cof ≠ ℵ₀`

which rules out one specific value (`κ = ℵ₀`) for the cofinality of the
continuum power set. The OQ-04 child asks the natural generalisation:

  **Can the corollary `cf(|𝒫(ℝ)|) ≠ κ` be proved uniformly for every
   specific cardinal `κ ≤ 𝔠`?**

The answer is yes, and the proof is a one-line reduction to the parent's
`cf_powerSet_real_gt_continuum : 𝔠 < (#(Set ℝ)).ord.cof`. The general
form makes explicit that *every* small cardinal — every aleph below
the continuum, every beth below the continuum, and the continuum
itself — is excluded as a possible cofinality of `|𝒫(ℝ)|`.

## Caveats on "Without Axioms"

Identical to the parent file. No additional axioms or sorries are
introduced. The parent file's caveats on `Classical.choice` carry
through unchanged: all results below are 0-axiom, 0-sorry under the
standard Mathlib convention.

## Main Results

1. `cf_powerSet_real_ne_of_le_continuum` — for every cardinal `κ ≤ 𝔠`,
   the cofinality of `|𝒫(ℝ)|` is not `κ`. This is the **general
   exclusion** form.
2. `cf_powerSet_real_ne_aleph0_general` — specialisation to `κ = ℵ₀`,
   re-deriving the parent's `cf_powerSet_real_ne_aleph0` corollary
   from the general form.
3. `cf_powerSet_real_ne_continuum` — specialisation to `κ = 𝔠` itself.
   This is the strongest single-cardinal exclusion implied by König's
   constraint and was *not* explicitly stated in the parent file.
4. `cf_powerSet_real_ne_aleph_of_aleph_le_continuum` — specialisation
   to `κ = ℵ_α` for any ordinal `α` with `ℵ_α ≤ 𝔠`.
5. `cf_powerSet_real_ne_beth_of_beth_le_continuum` — specialisation
   to `κ = ℶ_α` for any ordinal `α` with `ℶ_α ≤ 𝔠`. The natural pair
   of (4); `ℶ₁ = 𝔠` so `α = 1` is the boundary case.
6. `oq01oq03oq04_resolution` — bundle theorem packaging the affirmative
   resolution of the OQ.

## Relationship to Parent

- Parent `CantorsTheoremOQ01OQ03` proves the stronger inequality
  `𝔠 < cf(|𝒫(ℝ)|)` (`cf_powerSet_real_gt_continuum`). The OQ-04
  generalisation extracts the equivalence class
  `{κ : Cardinal | κ ≤ 𝔠} → cf(|𝒫(ℝ)|) ≠ κ` from this single inequality
  by a one-line `intro h; rw[h] at …; exact absurd …` argument.
- The parent's `cf_powerSet_real_ne_aleph0` becomes a corollary of the
  general form rather than an independently-proven theorem; this
  refactors the proof tree.
- All new specialisations (`κ = 𝔠`, `κ = ℵ_α`, `κ = ℶ_α`) are derived
  uniformly from the same general lemma.
-/

set_option linter.unusedVariables false

namespace CantorsTheoremOQ01OQ03OQ04

open Cardinal

-- ============================================================
-- PART 1: The General Cofinality Exclusion
-- ============================================================

/-- **General cofinality exclusion**: For every cardinal `κ ≤ 𝔠`, the
    cofinality of `|𝒫(ℝ)|` is strictly greater than `κ`, and in
    particular different from `κ`.

    This is the uniform corollary of König's constraint
    `cf(|𝒫(ℝ)|) > 𝔠` (parent's `cf_powerSet_real_gt_continuum`): every
    cardinal up to and including the continuum is ruled out as a
    cofinality of the continuum's power set.

    Proof: if `cf(|𝒫(ℝ)|) = κ ≤ 𝔠`, transport
    `𝔠 < cf(|𝒫(ℝ)|)` through the equation to get `𝔠 < κ ≤ 𝔠`,
    contradicting irreflexivity of `<`. -/
theorem cf_powerSet_real_ne_of_le_continuum
    {κ : Cardinal.{0}} (hκ : κ ≤ (𝔠 : Cardinal.{0})) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ κ := by
  intro h
  have h1 : (𝔠 : Cardinal.{0}) < κ := h ▸ CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum
  exact absurd (h1.trans_le hκ) (lt_irrefl _)

-- ============================================================
-- PART 2: Specific Cardinal Specialisations
-- ============================================================

/-- **Specialisation to ℵ₀**: `cf(|𝒫(ℝ)|) ≠ ℵ₀`.

    Re-derivation of the parent's `cf_powerSet_real_ne_aleph0` via
    the general exclusion form. Demonstrates that the parent's
    specific corollary is the `κ = ℵ₀` instance of the general
    `cf_powerSet_real_ne_of_le_continuum` lemma. -/
theorem cf_powerSet_real_ne_aleph0_general :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ ℵ₀ :=
  cf_powerSet_real_ne_of_le_continuum Cardinal.aleph0_le_continuum

/-- **Specialisation to 𝔠 itself**: `cf(|𝒫(ℝ)|) ≠ 𝔠`.

    The strongest single-cardinal exclusion implied by König's
    constraint. The parent file proved `𝔠 < cf(|𝒫(ℝ)|)`; this
    corollary states the inequational form `cf(|𝒫(ℝ)|) ≠ 𝔠`
    explicitly, since some downstream proofs care only about the
    disequation rather than the strict inequality. -/
theorem cf_powerSet_real_ne_continuum :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ (𝔠 : Cardinal.{0}) :=
  cf_powerSet_real_ne_of_le_continuum (le_refl _)

/-- **Specialisation to ℵ_α (with `ℵ_α ≤ 𝔠`)**: `cf(|𝒫(ℝ)|) ≠ ℵ_α`.

    Parameterises the aleph index `α` so that the exclusion holds
    *uniformly* over the entire below-continuum aleph hierarchy.
    The hypothesis `ℵ_α ≤ 𝔠` is a global constraint: under CH it
    forces `α = 0` (since then `𝔠 = ℵ₁`), but in general (e.g. under
    Martin's axiom + ¬CH) the range of valid `α` extends. -/
theorem cf_powerSet_real_ne_aleph_of_aleph_le_continuum
    {α : Ordinal.{0}} (hα : (Cardinal.aleph α : Cardinal.{0}) ≤ (𝔠 : Cardinal.{0})) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.aleph α :=
  cf_powerSet_real_ne_of_le_continuum hα

/-- **Specialisation to ℶ_α (with `ℶ_α ≤ 𝔠`)**: `cf(|𝒫(ℝ)|) ≠ ℶ_α`.

    Beth-indexed analogue of the aleph specialisation. The
    boundary case is `α = 1`, since `ℶ₁ = 2^ℵ₀ = 𝔠`; the constraint
    `ℶ_α ≤ 𝔠` therefore forces `α ≤ 1`. -/
theorem cf_powerSet_real_ne_beth_of_beth_le_continuum
    {α : Ordinal.{0}} (hα : (Cardinal.beth α : Cardinal.{0}) ≤ (𝔠 : Cardinal.{0})) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.beth α :=
  cf_powerSet_real_ne_of_le_continuum hα

-- ============================================================
-- PART 3: Resolution Bundle
-- ============================================================

/-- **Resolution of `cantors-theorem-oq-01-oq-03-oq-04`**: The parent's
    `cf(|𝒫(ℝ)|) ≠ ℵ₀` corollary generalises uniformly to every
    cardinal `κ ≤ 𝔠`.

    Bundle theorem packaging five forms of the general exclusion:
    the universally-quantified statement, the original parent
    specialisation (`κ = ℵ₀`), the strongest single-cardinal
    specialisation (`κ = 𝔠`), the aleph specialisation, and the
    beth specialisation. -/
theorem oq01oq03oq04_resolution :
    -- (1) Universally quantified general exclusion
    (∀ {κ : Cardinal.{0}}, κ ≤ (𝔠 : Cardinal.{0}) →
        (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ κ) ∧
    -- (2) ℵ₀ specialisation (parent's original corollary)
    ((#(Set ℝ) : Cardinal.{0}).ord.cof ≠ ℵ₀) ∧
    -- (3) 𝔠 specialisation
    ((#(Set ℝ) : Cardinal.{0}).ord.cof ≠ (𝔠 : Cardinal.{0})) ∧
    -- (4) Aleph specialisation (parameterised)
    (∀ {α : Ordinal.{0}}, (Cardinal.aleph α : Cardinal.{0}) ≤ 𝔠 →
        (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.aleph α) ∧
    -- (5) Beth specialisation (parameterised)
    (∀ {α : Ordinal.{0}}, (Cardinal.beth α : Cardinal.{0}) ≤ 𝔠 →
        (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.beth α) :=
  ⟨@cf_powerSet_real_ne_of_le_continuum,
   cf_powerSet_real_ne_aleph0_general,
   cf_powerSet_real_ne_continuum,
   @cf_powerSet_real_ne_aleph_of_aleph_le_continuum,
   @cf_powerSet_real_ne_beth_of_beth_le_continuum⟩

/-
## Conclusion

**OQ-01-OQ-03-OQ-04**: "Generalise the `cf ≠ ℵ₀` corollary to
`cf ≠ κ` for any specific `κ ≤ 𝔠`."

**Resolution: YES (affirmative)**

The general exclusion `cf(|𝒫(ℝ)|) ≠ κ` for every `κ ≤ 𝔠` is a
one-line consequence of the parent file's
`cf_powerSet_real_gt_continuum : 𝔠 < cf(|𝒫(ℝ)|)`. The reduction is

  `cf(|𝒫(ℝ)|) = κ ≤ 𝔠   →   𝔠 < κ ≤ 𝔠   →   ⊥`.

Specialisations follow uniformly:

- `κ = ℵ₀`: parent's `cf_powerSet_real_ne_aleph0`, re-proved as a
  corollary of the general form rather than a direct specialisation
  of `cf_powerSet_real_gt_continuum`.
- `κ = 𝔠`: the strongest below-continuum exclusion. Independent
  interest because it expresses that `|𝒫(ℝ)|` is "more singular
  than" the continuum in cofinality terms — the strict inequality
  rules out equality.
- `κ = ℵ_α` with `ℵ_α ≤ 𝔠`: aleph-indexed family. Under CH the
  range collapses to `α = 0`; in general it depends on the
  cardinal arithmetic axioms.
- `κ = ℶ_α` with `ℶ_α ≤ 𝔠`: beth-indexed family. `ℶ₁ = 𝔠` so the
  range is `α ≤ 1` outright (no CH dependence).

All proofs: 0 sorries, 0 explicit `axiom` declarations.

### Why this is a useful generalisation

The parent's specific corollary `cf ≠ ℵ₀` is the smallest possible
specialisation and was sufficient to "rule out `|𝒫(ℝ)| = ℵ_ω`"
since `cf(ℵ_ω) = ℵ₀`. But the general form rules out a much
larger family of singular alephs in one shot:

- `|𝒫(ℝ)| ≠ ℵ_ω`           (cf = ℵ₀ ≤ 𝔠)
- `|𝒫(ℝ)| ≠ ℵ_{ω₁}`        (cf = ℵ₁ ≤ 𝔠)
- `|𝒫(ℝ)| ≠ ℵ_{ω · α}` for any `α` with `ℵ_{cf(ω·α)} ≤ 𝔠`.

Each of these is now a single application of
`cf_powerSet_real_ne_aleph_of_aleph_le_continuum`. Without the
generalisation each would require an ad-hoc cofinality computation
on the index ordinal.

### Comparison with sibling Easton-stub (oq-04 of the cousin slug)

The cousin slug `cantor-diagonalization-oq-01-oq-01-oq-02-oq-01`
(Easton's theorem stub) consumes the parent's
`cf_powerSet_real_gt_continuum` to argue that "every regular
cardinal > ℵ₀ is consistent with ZFC as the value of `|𝒫(ℝ)|`".
The general exclusion proved here is the dual: it pins down which
cardinals are *impossible* as `|𝒫(ℝ)|` (the small ones, up to and
including 𝔠). Together they tell the full Easton-theorem story:
above 𝔠, anything regular is consistent; at or below 𝔠, nothing
is.
-/

end CantorsTheoremOQ01OQ03OQ04

-- Export key theorems
#check CantorsTheoremOQ01OQ03OQ04.cf_powerSet_real_ne_of_le_continuum
#check CantorsTheoremOQ01OQ03OQ04.cf_powerSet_real_ne_aleph0_general
#check CantorsTheoremOQ01OQ03OQ04.cf_powerSet_real_ne_continuum
#check CantorsTheoremOQ01OQ03OQ04.cf_powerSet_real_ne_aleph_of_aleph_le_continuum
#check CantorsTheoremOQ01OQ03OQ04.cf_powerSet_real_ne_beth_of_beth_le_continuum
#check CantorsTheoremOQ01OQ03OQ04.oq01oq03oq04_resolution
