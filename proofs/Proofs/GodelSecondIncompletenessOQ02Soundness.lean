import Proofs.GodelSecondIncompletenessOQ02Translate

/-!
# Gödel's Second Incompleteness — S16 ACT: arithmetical soundness of GL (rule cases)

This companion file is the **S16 ACT** for the
`godel-second-incompleteness-oq02-oq-02` research slug (Solovay's arithmetical
completeness for GL). It is the soundness direction:

> if `GL ⊢ φ` then for every realization `ρ`, `PA ⊢ translate ρ φ`.

building on the realization function `translate` (S15 ACT
`Proofs.GodelSecondIncompletenessOQ02Translate`), the GL syntax
(`Proofs.GodelSecondIncompletenessOQ02GLSyntax`), and the HBL infrastructure
(`Proofs.GodelSecondIncompletenessOQ02Companion`).

## What is proved here — and the axiom-integrity decision

The five `GL_proves` constructors split into two kinds:

* **Inference rules** (`mp`, `nec`): these are discharged by *genuine theorems*,
  with **0 new axioms**, from the existing infrastructure:
  - `nec`  ⟶ `GodelFirst.d1_representability` (D1):
    `⊢ translate ρ p → ⊢ Prov ⌜translate ρ p⌝ = ⊢ translate ρ (□p)`.
  - `mp`   ⟶ `GodelSecond.impl_mp` (meta-level modus ponens for `impl_formula`).
  These are exported as the standalone lemmas `arith_sound_nec` / `arith_sound_mp`.

* **Axiom schemas** (`taut`, `k`, `lob`): these assert that *specific PA formulas
  are PA-provable*. Under the gallery's **opaque** `Provable` predicate
  (`GodelFirst.axiom Provable`), such facts cannot be derived — there is no
  object-level deduction theorem and no concrete Σ₁ proof predicate to compute
  with (see S6 PREP #18497). They are exactly the HBL/derivability facts:
  - `taut` — PA proves every propositional-tautology translation;
  - `k`    — PA proves the internal **K** formula `Prov⌜a→b⌝ → (Prov⌜a⌝ → Prov⌜b⌝)`;
  - `lob`  — PA proves the internal **Löb** formula `Prov⌜Prov⌜a⌝→a⌝ → Prov⌜a⌝`.

Rather than introduce three fresh axioms, this file takes them as **explicit
hypotheses** of `arithmetical_soundness_of`. The result is a fully
build-verified, **0-new-axiom** soundness theorem whose only assumptions are the
three named derivability facts — which future stages can discharge:

* `k`   is dischargeable once an internal deduction theorem lifts the meta-level
  `GodelSecond.internal_K` to the object level;
* `lob` is dischargeable by S4 ACT (Löb's theorem, `lob_henkin_fixed_point`);
* `taut` is dischargeable by a Łukasiewicz/Kalmár CPL-completeness lift.

This keeps the proven mathematical content (rule-preservation by induction)
honest and separate from the assumed content (the GL axioms are PA-sound).

## Status
- **0 sorries**
- **0 new axioms** (the three derivability facts are hypotheses, not axioms)
- **3 theorems** (`arith_sound_nec`, `arith_sound_mp`, `arithmetical_soundness_of`)

## References
- Boolos, G. (1993). *The Logic of Provability*. Cambridge University Press, §3.
- Solovay, R. (1976). "Provability interpretations of modal logic". *Israel J. Math.*
- S10 PREP #18678 §3.4 — the proposed five-case induction over `GL_proves`.
-/

open GodelFirst GodelSecond GodelSecondGLSyntax GodelSecondTranslate

namespace GodelSecondSoundness

-- ============================================================
-- PART 1: Inference rules are sound (genuine theorems, 0 axioms)
-- ============================================================

/-- **`nec` is arithmetically sound.** If PA proves `translate ρ p`, then PA proves
    `translate ρ (□p) = Prov ⌜translate ρ p⌝`. This is exactly the D1 derivability
    condition (`GodelFirst.d1_representability`). -/
theorem arith_sound_nec (ρ : PropAtom → Formula) (p : GLFormula)
    (hp : ⊢ translate ρ p) : ⊢ translate ρ (.box p) := by
  rw [translate_box]
  exact d1_representability _ hp

/-- **`mp` is arithmetically sound.** If PA proves `translate ρ (p → q)` and PA
    proves `translate ρ p`, then PA proves `translate ρ q`. This is exactly the
    meta-level modus-ponens rule for `impl_formula` (`GodelSecond.impl_mp`). -/
theorem arith_sound_mp (ρ : PropAtom → Formula) (p q : GLFormula)
    (hpq : ⊢ translate ρ (.impl p q)) (hp : ⊢ translate ρ p) :
    ⊢ translate ρ q := by
  rw [translate_impl] at hpq
  exact impl_mp _ _ hpq hp

-- ============================================================
-- PART 2: Arithmetical soundness of GL (conditional on the axiom-case facts)
-- ============================================================

/-- **Arithmetical soundness of GL (rule-verified form).**

    For every realization `ρ`, if `GL ⊢ φ` then `PA ⊢ translate ρ φ`, provided the
    three GL-axiom translations are PA-provable:

    * `Htaut` — every propositional-axiom translation is provable;
    * `Hk`    — the internal **K** formula is provable;
    * `Hlob`  — the internal **Löb** formula is provable.

    The `mp` and `nec` cases are discharged unconditionally (D1 + `impl_mp`); the
    three axiom cases consume the corresponding hypothesis. See the file docstring
    for why `Htaut`/`Hk`/`Hlob` are hypotheses rather than axioms. -/
theorem arithmetical_soundness_of
    (ρ : PropAtom → Formula)
    (Htaut : ∀ t : GLFormula, PropAxiom t → ⊢ translate ρ t)
    (Hk : ∀ a b : Formula,
      ⊢ (Prov (godelNum (a →ᶠ b)) →ᶠ (Prov (godelNum a) →ᶠ Prov (godelNum b))))
    (Hlob : ∀ a : Formula,
      ⊢ (Prov (godelNum (Prov (godelNum a) →ᶠ a)) →ᶠ Prov (godelNum a)))
    {φ : GLFormula} (h : GL_proves φ) : ⊢ translate ρ φ := by
  induction h with
  | taut hax => exact Htaut _ hax
  | k p q =>
      simp only [translate_impl, translate_box]
      exact Hk (translate ρ p) (translate ρ q)
  | lob p =>
      simp only [translate_impl, translate_box]
      exact Hlob (translate ρ p)
  | mp h₁ h₂ ih₁ ih₂ =>
      rw [translate_impl] at ih₁
      exact impl_mp _ _ ih₁ ih₂
  | nec h ih =>
      rw [translate_box]
      exact d1_representability _ ih

#check @arith_sound_nec
#check @arith_sound_mp
#check @arithmetical_soundness_of

end GodelSecondSoundness
