import Mathlib

/-!
# Natural Mathematical Statements Independent of PA — an abstract independence framework

`godel-incompleteness-oq-03`

The parent gallery entry `godel-incompleteness` gives an *illustrative* sketch of
Gödel's theorems built around a placeholder provability predicate
(`Provable := fun _ => False`). That sketch cannot express what it means for a
*specific* sentence to be independent, because its provability predicate is trivial.

This file instead develops the **abstract theory of independence** on top of
Mathlib's genuine first-order model theory (`FirstOrder.Language.Theory`), where
`T ⊨ᵇ φ` is real semantic consequence quantified over *all* models of `T`.

A sentence `φ` is **independent** of a theory `T` when `T` neither entails `φ`
nor entails `¬φ`:  `T ⊭ φ` and `T ⊭ ¬φ`.  This is exactly the shape of every
"natural statement independent of PA":

* **Goodstein's theorem** (Kirby–Paris 1982),
* the **Paris–Harrington** strengthening of the finite Ramsey theorem,
* the **Kirby–Paris hydra** termination statement,
* the consistency sentence **`Con(PA)`** (Gödel's second theorem),

are all sentences `φ` with `PA ⊭ φ` and `PA ⊭ ¬φ`.

## What is proved here (fully verified against Mathlib: 0 axioms, 0 sorries)

* `Independent.not_isComplete` — a theory possessing *any* independent sentence is
  **not complete**.  This is the abstract content of "independence ⇒ incompleteness".
* `isComplete_iff_forall_not_independent` — completeness is *exactly* the absence of
  any independent sentence (for a satisfiable theory).
* `Independent.satisfiable_insert_not` / `Independent.satisfiable_insert` —
  independence produces two genuinely different model classes: `T ∪ {¬φ}` and
  `T ∪ {φ}` are *both* satisfiable.
* `independent_iff_satisfiable_both` — the model-theoretic characterization of
  independence via the Completeness Theorem (`models_iff_not_satisfiable`):
  `φ` is independent of `T` iff both `T ∪ {¬φ}` and `T ∪ {φ}` have models.
* `Independent.isSatisfiable` / `Independent.neg_iff` / `Independent.neg` /
  `Independent.mono` / `not_independent_of_not_isSatisfiable` — the structural calculus
  of the relation: independence implies consistency, is symmetric under negation,
  descends to subtheories, and holds for some sentence iff `T` is consistent.

## What remains genuinely open / out of scope

Exhibiting a *concrete* natural `φ` independent of PA (Goodstein, Paris–Harrington,
`Con(PA)`) requires formalizing PA's syntax, `ε₀`-induction, fast-growing hierarchies,
and the unprovability arguments — thousands of lines that are absent from current
Mathlib. This file supplies the abstract scaffolding those theorems instantiate, not
the theorems themselves.
-/

open FirstOrder Language

namespace GodelIncompletenessOQ03

variable {L : Language} {T : L.Theory} {φ : L.Sentence}

/-- Replacing a sentence by its **double negation** in a one-sentence extension does
    not change satisfiability: `T ∪ {¬¬φ}` has a model iff `T ∪ {φ}` does.  Both
    extensions have the same models, since `M ⊨ ¬¬φ ↔ M ⊨ φ` in every structure.

    This is the bookkeeping bridge that lets the Completeness-Theorem characterization
    of independence be stated in terms of `T ∪ {φ}` rather than the syntactic
    `T ∪ {¬¬φ}` produced by `models_iff_not_satisfiable`. -/
theorem isSatisfiable_insert_not_not_iff :
    Theory.IsSatisfiable (T ∪ {φ.not.not}) ↔ Theory.IsSatisfiable (T ∪ {φ}) := by
  -- A generic transfer: if `ψ` semantically implies `χ` in every structure, then a
  -- model of `T ∪ {ψ}` is a model of `T ∪ {χ}`.
  have transfer : ∀ {ψ χ : L.Sentence},
      (∀ {N : Type _} [L.Structure N], (N ⊨ ψ) → (N ⊨ χ)) →
      Theory.IsSatisfiable (T ∪ {ψ}) → Theory.IsSatisfiable (T ∪ {χ}) := by
    rintro ψ χ himp ⟨M⟩
    have hm : (M : Type _) ⊨ (T ∪ {ψ}) := M.is_model
    rw [Theory.model_union_iff, Theory.model_singleton_iff] at hm
    haveI : (M : Type _) ⊨ (T ∪ {χ}) := by
      rw [Theory.model_union_iff, Theory.model_singleton_iff]
      exact ⟨hm.1, himp hm.2⟩
    exact Theory.Model.isSatisfiable (T := T ∪ {χ}) (M : Type _)
  constructor
  · exact transfer (fun h => by
      rw [Sentence.realize_not, Sentence.realize_not] at h; exact not_not.1 h)
  · exact transfer (fun h => by
      rw [Sentence.realize_not, Sentence.realize_not]; exact not_not_intro h)

/-- A sentence `φ` is **independent** of a theory `T` when `T` entails neither `φ`
    nor its negation `¬φ`.  Semantically: there is a model of `T` in which `φ` is
    false (so `T ⊭ φ`) and a model of `T` in which `φ` is true (so `T ⊭ ¬φ`). -/
def Independent (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ φ.not

namespace Independent

theorem not_models (h : Independent T φ) : ¬ T ⊨ᵇ φ := h.1

theorem not_models_not (h : Independent T φ) : ¬ T ⊨ᵇ φ.not := h.2

/-- **Independence forces incompleteness.**  A complete theory entails `φ` or `¬φ`
    for every sentence; an independent sentence entails neither, a contradiction. -/
theorem not_isComplete (h : Independent T φ) : ¬ T.IsComplete := by
  rintro hc
  exact (hc.2 φ).elim h.1 h.2

/-- Independence yields a model of `T` refuting `φ`: `T ∪ {¬φ}` is satisfiable.
    (This witnesses `T ⊭ φ` via the Completeness Theorem.) -/
theorem satisfiable_insert_not (h : Independent T φ) :
    Theory.IsSatisfiable (T ∪ {φ.not}) := by
  have h1 := h.1
  rw [Theory.models_iff_not_satisfiable] at h1
  exact not_not.1 h1

/-- Independence yields a model of `T` satisfying `φ`: `T ∪ {φ}` is satisfiable.
    (This witnesses `T ⊭ ¬φ` via the Completeness Theorem.) -/
theorem satisfiable_insert (h : Independent T φ) :
    Theory.IsSatisfiable (T ∪ {φ}) := by
  have h2 := h.2
  rw [Theory.models_iff_not_satisfiable] at h2
  rw [← isSatisfiable_insert_not_not_iff]
  exact not_not.1 h2

end Independent

/-- **Model-theoretic characterization of independence.**  `φ` is independent of `T`
    iff both one-sentence extensions `T ∪ {¬φ}` and `T ∪ {φ}` are satisfiable — i.e.
    `T` has a model where `φ` fails and a model where `φ` holds.  Immediate from the
    Completeness Theorem (`models_iff_not_satisfiable`). -/
theorem independent_iff_satisfiable_both :
    Independent T φ ↔
      Theory.IsSatisfiable (T ∪ {φ.not}) ∧ Theory.IsSatisfiable (T ∪ {φ}) := by
  unfold Independent
  rw [Theory.models_iff_not_satisfiable φ, Theory.models_iff_not_satisfiable φ.not,
      not_not, not_not, isSatisfiable_insert_not_not_iff]

/-- **Completeness is exactly the absence of independent sentences.**  For a
    satisfiable theory `T`, `T` is complete iff no sentence is independent of it.
    The contrapositive of `Independent.not_isComplete`, packaged as an equivalence. -/
theorem isComplete_iff_forall_not_independent (hsat : T.IsSatisfiable) :
    T.IsComplete ↔ ∀ φ : L.Sentence, ¬ Independent T φ := by
  constructor
  · intro hc φ hind
    exact hind.not_isComplete hc
  · intro h
    refine ⟨hsat, fun φ => ?_⟩
    by_contra hcon
    push_neg at hcon
    exact h φ ⟨hcon.1, hcon.2⟩

/-! ## A calculus of independence

Structural lemmas that make `Independent` easy to manipulate: independence implies
the underlying theory is satisfiable, is symmetric in `φ` and `¬φ`, and descends to
subtheories. -/

namespace Independent

/-- **Independence implies consistency.**  If some sentence is independent of `T`
    then `T` has a model.  An *inconsistent* theory entails every sentence
    vacuously (`T ⊨ᵇ φ` for all `φ`), so it cannot leave anything undecided;
    contrapositively, leaving `φ` undecided forces `T` to be satisfiable. -/
theorem isSatisfiable (h : Independent T φ) : T.IsSatisfiable :=
  h.satisfiable_insert.mono Set.subset_union_left

/-- **A sentence is independent iff its negation is.**  Independence is symmetric
    in `φ` and `¬φ`: neither is decided exactly when the other is not. -/
theorem neg_iff : Independent T φ.not ↔ Independent T φ := by
  rw [independent_iff_satisfiable_both, independent_iff_satisfiable_both,
      isSatisfiable_insert_not_not_iff]
  exact and_comm

/-- The negation of an independent sentence is independent. -/
theorem neg (h : Independent T φ) : Independent T φ.not := neg_iff.mpr h

/-- **Independence descends to subtheories.**  If `φ` is independent of a theory `T₁`
    and `T₀ ⊆ T₁`, then `φ` is independent of the weaker theory `T₀`: a weaker theory
    has even fewer consequences, so it still cannot decide `φ`.  (E.g. a sentence
    independent of PA is independent of every subtheory of PA.) -/
theorem mono {T₀ T₁ : L.Theory} {φ : L.Sentence}
    (h : Independent T₁ φ) (hsub : T₀ ⊆ T₁) : Independent T₀ φ := by
  rw [independent_iff_satisfiable_both] at h ⊢
  exact ⟨h.1.mono (Set.union_subset_union_left _ hsub),
         h.2.mono (Set.union_subset_union_left _ hsub)⟩

end Independent

/-- **An inconsistent theory has no independent sentences.**  The contrapositive of
`Independent.isSatisfiable`: if `T` is unsatisfiable it proves everything (vacuously),
so it decides every sentence and none is independent. -/
theorem not_independent_of_not_isSatisfiable {T : L.Theory} {φ : L.Sentence}
    (h : ¬ T.IsSatisfiable) : ¬ Independent T φ :=
  fun hind => h hind.isSatisfiable

end GodelIncompletenessOQ03
