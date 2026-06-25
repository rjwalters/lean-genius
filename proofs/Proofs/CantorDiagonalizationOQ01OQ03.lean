import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Logic.Basic
import Mathlib.Tactic

/-
# König's Constraint on the Continuum, Axiom-Free (OQ-01-OQ-03)

## Open Question

The parent entry "The Continuum Hypothesis" (cantor-diagonalization-oq-01)
lists, among the facts the diagonal argument *can* establish:

> **König's constraint**: `cf(2^ℵ₀) > ℵ₀`, hence `2^ℵ₀ ≠ ℵ_ω`.

but discharges it with two `axiom` declarations:

```
  axiom konig_cofinality_bound :
      (ℵ₀ : Cardinal.{0}) < (continuum.ord.cof : Cardinal)
  axiom aleph_omega_cofinality_is_aleph_zero :
      ((Cardinal.aleph (ω : Ordinal.{0})).ord.cof : Cardinal) = ℵ₀
```

## What this entry proves

Both axioms are unnecessary: they are theorems of ZFC and are available in
Mathlib. This entry **eliminates them**, giving a fully machine-checked,
0-axiom account of König's structural constraint on the continuum.

The engine is König's theorem for cardinals, `Σᵢ κᵢ < Πᵢ λᵢ` whenever
`κᵢ < λᵢ`, packaged in Mathlib as
`Cardinal.lt_cof_power : ℵ₀ ≤ a → 1 < b → a < (b ^ a).ord.cof`.

We prove:

1. `konig_cofinality_general` — for every infinite `κ`, `κ < cf(2^κ)`.
2. `continuum_cofinality_gt_aleph0` — the specialization `ℵ₀ < cf(2^ℵ₀)`
   (the parent's first axiom, now a theorem).
3. `cof_aleph_omega` — `cf(ℵ_ω) = ℵ₀` (the parent's second axiom, now a theorem),
   via `Ordinal.cof_omega` + `Ordinal.cof_omega0`.
4. `continuum_ne_aleph_omega` — `2^ℵ₀ ≠ ℵ_ω`.
5. `continuum_ne_of_cof_aleph0` — the sharper statement that `2^ℵ₀` differs
   from *every* cardinal of countable cofinality, of which `ℵ_ω` is one case.

## Why this is the diagonal argument's true reach

Cantor's diagonal argument proves `ℵ₀ < 2^ℵ₀` but says nothing about *where*
`2^ℵ₀` sits in the aleph hierarchy. König's theorem is the one nontrivial
ZFC-provable restriction: the continuum cannot be a countable supremum of
smaller cardinals, so it skips `ℵ_ω`, `ℵ_{ω+ω}`, and every `ℵ_α` with
`cf(α) = ω`. CH (`2^ℵ₀ = ℵ₁`) and many `¬CH` values remain, but these
singular alephs are forbidden — a fact, not an assumption.

## References
- König (1905): `Σ κᵢ < Π λᵢ` (König's inequality for cardinals)
- Jech, *Set Theory* (2003), Theorem 3.11 (König) and Corollary 5.13 (cf 2^κ > κ)
- Mathlib: `Cardinal.lt_cof_power`, `Ordinal.cof_omega`, `Ordinal.cof_omega0`
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorDiagOQ01OQ03

open Cardinal Ordinal

/-- The continuum, `2 ^ ℵ₀`. -/
noncomputable def continuum : Cardinal.{0} := 2 ^ ℵ₀

theorem continuum_def : continuum = 2 ^ ℵ₀ := rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: KÖNIG'S COFINALITY BOUND (replaces `konig_cofinality_bound`)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **König's theorem, cofinality form.** For every infinite cardinal `κ`,
    the cofinality of `2 ^ κ` strictly exceeds `κ`. This is the cardinal
    consequence of König's inequality `Σᵢ κᵢ < Πᵢ λᵢ`; in particular
    `2 ^ κ` is never a sum of `κ`-many smaller cardinals. -/
theorem konig_cofinality_general {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) :
    κ < ((2 : Cardinal.{0}) ^ κ).ord.cof :=
  Cardinal.lt_cof_power hκ one_lt_two

/-- **The parent's first axiom, now a theorem.** The cofinality of the
    continuum exceeds `ℵ₀`: `ℵ₀ < cf(2^ℵ₀)`. -/
theorem continuum_cofinality_gt_aleph0 :
    (ℵ₀ : Cardinal.{0}) < continuum.ord.cof := by
  rw [continuum_def]
  exact konig_cofinality_general le_rfl

/-- Restated for the diagonal-argument narrative: the continuum has
    *uncountable* cofinality, so it is a regular-or-larger obstruction —
    it cannot be approached by a countable increasing sequence of
    smaller cardinals. -/
theorem continuum_uncountable_cofinality :
    ¬ (continuum.ord.cof ≤ ℵ₀) := by
  intro h
  exact absurd (lt_of_lt_of_le continuum_cofinality_gt_aleph0 h) (lt_irrefl _)

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: COFINALITY OF ℵ_ω (replaces `aleph_omega_cofinality_is_aleph_zero`)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **The parent's second axiom, now a theorem.** `ℵ_ω` is the first singular
    aleph: its cofinality is `ℵ₀`, because the initial ordinal `ω_ ω = (ℵ_ω).ord`
    is normal-image of the limit ordinal `ω`, whose cofinality is `ℵ₀`. -/
theorem cof_aleph_omega :
    (Cardinal.aleph (ω : Ordinal.{0})).ord.cof = ℵ₀ := by
  rw [Cardinal.ord_aleph, Ordinal.cof_omega Ordinal.isSuccLimit_omega0,
    Ordinal.cof_omega0]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE CONTINUUM SKIPS THE SINGULAR ALEPHS
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **König rules out `ℵ_ω`.** `2^ℵ₀ ≠ ℵ_ω`. The continuum has uncountable
    cofinality (Part I), but `ℵ_ω` has cofinality `ℵ₀` (Part II). -/
theorem continuum_ne_aleph_omega :
    continuum ≠ Cardinal.aleph (ω : Ordinal.{0}) := by
  intro h
  have hcof := continuum_cofinality_gt_aleph0
  rw [h, cof_aleph_omega] at hcof
  exact lt_irrefl ℵ₀ hcof

/-- **The sharp obstruction.** `2^ℵ₀` differs from *every* cardinal of countable
    cofinality. `ℵ_ω` (Part III above) is merely the first such cardinal;
    `ℵ_{ω+ω}`, `ℵ_{ω·ω}`, … are equally forbidden. The diagonal argument
    leaves the value of the continuum open, but König's theorem forbids it
    from being any of these singular alephs. -/
theorem continuum_ne_of_cof_aleph0 {c : Cardinal.{0}} (hc : c.ord.cof = ℵ₀) :
    continuum ≠ c := by
  intro h
  have hcof := continuum_cofinality_gt_aleph0
  rw [h, hc] at hcof
  exact lt_irrefl ℵ₀ hcof

/-- `continuum_ne_aleph_omega` recovered from the general obstruction. -/
example : continuum ≠ Cardinal.aleph (ω : Ordinal.{0}) :=
  continuum_ne_of_cof_aleph0 cof_aleph_omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: SUMMARY — THE DIAGONAL ARGUMENT'S TRUE, AXIOM-FREE REACH
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Summary.** Everything the diagonal argument plus ZFC establishes about the
    *cofinality* of the continuum, with no axioms beyond Mathlib's foundations:

    1. `ℵ₀ < 2^ℵ₀`           (Cantor: the gap exists);
    2. `ℵ₀ < cf(2^ℵ₀)`        (König: the gap has uncountable cofinality);
    3. `2^ℵ₀ ≠ ℵ_ω`           (so the continuum skips the first singular aleph).

    Note 1 is `Cardinal.cantor`; 2 and 3 were *axioms* in the parent entry and
    are here discharged as theorems. -/
theorem konig_constraint_summary :
    ((ℵ₀ : Cardinal.{0}) < continuum) ∧
    ((ℵ₀ : Cardinal.{0}) < continuum.ord.cof) ∧
    (continuum ≠ Cardinal.aleph (ω : Ordinal.{0})) := by
  refine ⟨?_, continuum_cofinality_gt_aleph0, continuum_ne_aleph_omega⟩
  rw [continuum_def]
  exact Cardinal.cantor ℵ₀

end CantorDiagOQ01OQ03
