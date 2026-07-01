/-
  Schröder–Bernstein OQ-05 — Dual Schröder–Bernstein
  "Mutual surjections imply equinumerosity."

  Statement: if there exist surjections `f : A ↠ B` and `g : B ↠ A`, then
  `A` and `B` are equinumerous (there is a bijection `A ≃ B`).

  This is the *dual* of the classical Cantor–Schröder–Bernstein theorem
  (mutual injections ⇒ bijection), proved in the parent `SchroederBernstein.lean`.
  Whereas the injective form is choice-free, the surjective form genuinely uses
  the Axiom of Choice: each surjection is split by a right inverse, which is an
  injection, and the classical Schröder–Bernstein theorem is then applied to the
  two resulting injections. (In fact the dual statement, for arbitrary sets, is
  *equivalent* to AC; here we formalize the forward implication under Mathlib's
  ambient choice.)

  Everything below is a genuine `theorem`/`def` with a real proof — no `sorry`,
  no custom axioms beyond Lean/Mathlib's standard
  `propext`/`Classical.choice`/`Quot.sound`.
-/

import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

namespace SchroederBernsteinOQ05

open Function

variable {A B : Type*}

/-- **Splitting a surjection.** Every surjection `f : A → B` admits a right
    inverse `f' : B → A` (a section), and any such section is injective. This is
    the one place the Axiom of Choice enters the dual theorem. -/
theorem exists_injective_section {f : A → B} (hf : Surjective f) :
    ∃ f' : B → A, RightInverse f' f ∧ Injective f' := by
  obtain ⟨f', hf'⟩ := hf.hasRightInverse
  exact ⟨f', hf', hf'.injective⟩

/-- **Dual Schröder–Bernstein (bijection form).** Surjections both ways yield a
    bijection `A → B`: split each surjection into an injective section, then feed
    the two injections to the classical Schröder–Bernstein theorem. -/
theorem exists_bijective_of_surjective₂
    {f : A → B} (hf : Surjective f) {g : B → A} (hg : Surjective g) :
    ∃ h : A → B, Bijective h := by
  obtain ⟨_f', _, hf'inj⟩ := exists_injective_section hf   -- f' : B → A, injective
  obtain ⟨_g', _, hg'inj⟩ := exists_injective_section hg   -- g' : A → B, injective
  exact Function.Embedding.schroeder_bernstein hg'inj hf'inj

/-- **Dual Schröder–Bernstein (equivalence form).** An explicit `A ≃ B`
    witnessing equinumerosity from mutual surjections. Noncomputable because the
    underlying sections are chosen. -/
noncomputable def equivOfSurjective₂
    {f : A → B} (hf : Surjective f) {g : B → A} (hg : Surjective g) : A ≃ B :=
  Equiv.ofBijective _ (exists_bijective_of_surjective₂ hf hg).choose_spec

/-- Nonempty-equivalence form: mutual surjections make `A` and `B` equinumerous. -/
theorem nonempty_equiv_of_surjective₂
    {f : A → B} (hf : Surjective f) {g : B → A} (hg : Surjective g) :
    Nonempty (A ≃ B) :=
  ⟨equivOfSurjective₂ hf hg⟩

/-- **Cardinal form.** Mutual surjections force equal cardinality: `#A = #B`. -/
theorem cardinal_eq_of_surjective₂ {A B : Type u}
    {f : A → B} (hf : Surjective f) {g : B → A} (hg : Surjective g) :
    Cardinal.mk A = Cardinal.mk B :=
  Cardinal.eq.mpr (nonempty_equiv_of_surjective₂ hf hg)

/-- Sanity check: the produced equivalence really is a bijective map. -/
theorem equivOfSurjective₂_bijective
    {f : A → B} (hf : Surjective f) {g : B → A} (hg : Surjective g) :
    Bijective (equivOfSurjective₂ hf hg) :=
  (equivOfSurjective₂ hf hg).bijective

end SchroederBernsteinOQ05
