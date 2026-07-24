import Proofs.GodelSecondIncompletenessOQ02GLSyntax
import Proofs.GodelSecondIncompletenessOQ02GLFour
import Proofs.GodelSecondIncompletenessOQ02Kalmar
import Proofs.GodelSecondIncompletenessOQ02Lindenbaum

/-!
# GL modal engine — S22b: boxed-context necessitation and the Löb-trick seed

S22b of `godel-second-incompleteness-oq02-oq-02` (Solovay's arithmetical
completeness for GL). S22a (`Lindenbaum.lean`) built the world-construction
layer for the finite model property; this file builds the **modal engine**
that the box case of the canonical-model truth lemma runs on. Everything is
purely syntactic — no frames, no semantics — and Mathlib-free like the rest
of the S8 stack.

## Contents

* **Cut for `PDeriv`** (`deriv_cut`): derivability composes through a
  context-for-context substitution.
* **List conjunction** (`conjList`, over the S18 binary `conj`):
  projections (`conjList_elim`), introduction under a context
  (`deriv_conjList`), and the closure bridge `gl_conjList_imp`
  (`Γ ⊢ θ` gives `⊢ ⋀Γ → θ` as a GL theorem, via cut + deduction).
* **Box distribution over conjunctions** (`box_conj_intro`,
  `deriv_box_conjList`): `□` commutes with `⋀` using `K` and
  necessitation.
* **Boxed content of a context** (`boxes`, `boxContent`): for each
  `□χ ∈ Δ`, the list `boxContent Δ` holds both `χ` and `□χ` — Boolos'
  `w⁺`. Every element is `□`-derivable from `Δ` itself
  (`boxContent_all_boxed`, the `□χ` copies via the S18 `four` schema).
* **Boxed-context necessitation** (`deriv_box_of_boxContent`): the derived
  modal rule
  `boxContent Δ ⊢ φ  ⟹  Δ ⊢ □φ` —
  necessitation relative to a boxed context, the engine of every
  canonical-model argument for transitive provability logics.
* **Löb's rule** (`lob_rule`): `⊢ □φ → φ` implies `⊢ φ` — the classic
  admissible rule, one line from the `L` axiom + necessitation.
* **The Löb-trick seed lemma** (`lob_seed_consistent`,
  `lob_seed_consistent_of_maximal`) — the mathematical heart of the box
  case of the future truth lemma: if `Δ ⊬ □ψ` then
  `{¬ψ, □ψ} ∪ boxContent Δ` is **consistent**.
  Contrapositive: a refutation of the seed closes (deduction theorem +
  double negation) to `boxContent Δ ⊢ □ψ → ψ`, boxed-context
  necessitation turns this into `Δ ⊢ □(□ψ → ψ)`, and **Löb's axiom**
  collapses that to `Δ ⊢ □ψ`. The `□ψ` member of the seed is what will
  make the canonical accessibility relation strictly increase the boxed
  stock (irreflexivity/converse well-foundedness witness) in S22c.

## What this is NOT

The canonical frame itself (worlds, accessibility, truth lemma, Segerberg
completeness, FMP, decidability) is *not* built here — that is S22c, which
consumes exactly `lindenbaum` (S22a) + `lob_seed_consistent` (this file).

## Design notes

* Mathlib-free; only Lean-core list lemmas (`mem_cons`, `mem_append`,
  `mem_map`) and the S8/S18/S19/S22a stack. 0 sorries, 0 `axiom`
  declarations; classical content is inherited from `Lindenbaum.lean`'s
  `Consistent` reasoning only (this file's own derivations are
  constructive).

## References

- Boolos, G. (1993). *The Logic of Provability*. Cambridge University
  Press, Ch. 5 (the `w⁺` construction and the completeness box case).
- Segerberg, K. (1971). *An Essay in Classical Modal Logic*. Uppsala.
- Löb, M. H. (1955). Solution of a problem of Leon Henkin. *JSL* 20.
-/

namespace GodelSecondLobSeed

open GodelSecondGLSyntax GodelSecondGLFour GodelSecondKalmar GodelSecondLindenbaum

local infixr:55 " ⟶ " => GLFormula.impl
local prefix:75 "□" => GLFormula.box
local notation "⊥ₘ" => GLFormula.falsum

-- ============================================================
-- PART 1: cut and list conjunction
-- ============================================================

/-- Cut: a derivation from context `Δ` composes with derivations of all of
`Δ` from `Γ`. -/
theorem deriv_cut {Γ : List GLFormula} : ∀ {Δ : List GLFormula} {θ : GLFormula},
    PDeriv Δ θ → (∀ x ∈ Δ, PDeriv Γ x) → PDeriv Γ θ := by
  intro Δ θ h
  induction h with
  | hyp h => exact fun hall => hall _ h
  | thm h => exact fun _ => .thm h
  | mp _ _ ih₁ ih₂ => exact fun hall => .mp (ih₁ hall) (ih₂ hall)

/-- Conjunction of a list of formulas (empty list ↦ the S18 verum
`⊥ → ⊥`), folded with the S18 binary `conj`. -/
def conjList : List GLFormula → GLFormula
  | [] => ⊥ₘ ⟶ ⊥ₘ
  | x :: L => conj x (conjList L)

/-- Projection: the list conjunction implies each of its members. -/
theorem conjList_elim : ∀ {Δ : List GLFormula} {x : GLFormula}, x ∈ Δ →
    GL_proves (conjList Δ ⟶ x) := by
  intro Δ
  induction Δ with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons y L ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxL
    · exact conj_elim_left x (conjList L)
    · exact imp_trans (conj_elim_right y (conjList L)) (ih hxL)

/-- Introduction: a context deriving every member derives the conjunction. -/
theorem deriv_conjList {Γ : List GLFormula} : ∀ (Δ : List GLFormula),
    (∀ x ∈ Δ, PDeriv Γ x) → PDeriv Γ (conjList Δ) := by
  intro Δ
  induction Δ with
  | nil => intro _; exact .thm (imp_id ⊥ₘ)
  | cons y L ih =>
    intro h
    exact .mp (.mp (.thm (conj_intro y (conjList L)))
        (h y (List.mem_cons.mpr (Or.inl rfl))))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Closure bridge: `Δ ⊢ θ` yields the **GL theorem** `⊢ ⋀Δ → θ`
(cut against the projections, then the deduction theorem). -/
theorem gl_conjList_imp {Δ : List GLFormula} {θ : GLFormula}
    (h : PDeriv Δ θ) : GL_proves (conjList Δ ⟶ θ) :=
  (deriv_cut h fun _ hx =>
    .mp (.thm (conjList_elim hx)) (.hyp (List.mem_cons.mpr (Or.inl rfl)))
    : PDeriv [conjList Δ] θ).deduction.toGL

-- ============================================================
-- PART 2: box distribution over conjunctions
-- ============================================================

/-- `□` distributes into a binary conjunction: `⊢ □p → (□q → □(p ∧ q))`
(box-monotone `conj_intro`, then `K`). -/
theorem box_conj_intro (p q : GLFormula) :
    GL_proves (□p ⟶ □q ⟶ □(conj p q)) :=
  imp_trans (box_mono (conj_intro p q)) (GL_proves.k q (conj p q))

/-- A context deriving `□x` for every member of `Δ` derives `□⋀Δ`. -/
theorem deriv_box_conjList {Γ : List GLFormula} : ∀ (Δ : List GLFormula),
    (∀ x ∈ Δ, PDeriv Γ (□x)) → PDeriv Γ (□(conjList Δ)) := by
  intro Δ
  induction Δ with
  | nil => intro _; exact .thm (.nec (imp_id ⊥ₘ))
  | cons y L ih =>
    intro h
    exact .mp (.mp (.thm (box_conj_intro y (conjList L)))
        (h y (List.mem_cons.mpr (Or.inl rfl))))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

-- ============================================================
-- PART 3: the boxed content of a context (Boolos' w⁺)
-- ============================================================

/-- The list of formulas under a top-level `□` in `Δ`. -/
def boxes : List GLFormula → List GLFormula
  | [] => []
  | .box χ :: Δ => χ :: boxes Δ
  | _ :: Δ => boxes Δ

theorem box_mem_of_mem_boxes : ∀ {Δ : List GLFormula} {χ : GLFormula},
    χ ∈ boxes Δ → □χ ∈ Δ := by
  intro Δ
  induction Δ with
  | nil => intro χ h; exact absurd h (by simp [boxes])
  | cons y Δ ih =>
    intro χ h
    cases y with
    | box χ' =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (ih h')
    | atom p => exact List.mem_cons_of_mem _ (ih h)
    | falsum => exact List.mem_cons_of_mem _ (ih h)
    | impl p q => exact List.mem_cons_of_mem _ (ih h)

theorem mem_boxes_of_box_mem : ∀ {Δ : List GLFormula} {χ : GLFormula},
    □χ ∈ Δ → χ ∈ boxes Δ := by
  intro Δ
  induction Δ with
  | nil => intro χ h; exact absurd h (by simp)
  | cons y Δ ih =>
    intro χ h
    rcases List.mem_cons.mp h with heq | h'
    · subst heq
      exact List.mem_cons.mpr (Or.inl rfl)
    · cases y with
      | box χ' => exact List.mem_cons_of_mem _ (ih h')
      | atom p => exact ih h'
      | falsum => exact ih h'
      | impl p q => exact ih h'

/-- Boolos' `w⁺`: for each `□χ ∈ Δ`, both `χ` and `□χ`. This is the
context every canonical `R`-successor of the world `Δ` must absorb —
the `□χ` copies are what make the canonical relation transitive. -/
def boxContent (Δ : List GLFormula) : List GLFormula :=
  boxes Δ ++ (boxes Δ).map GLFormula.box

/-- Every element of `boxContent Δ` is `□`-derivable from `Δ` itself:
`χ`-copies because `□χ` is literally a hypothesis, `□χ`-copies via the
S18 `four` schema (`⊢ □χ → □□χ`). -/
theorem boxContent_all_boxed {Δ : List GLFormula} :
    ∀ x ∈ boxContent Δ, PDeriv Δ (□x) := by
  intro x hx
  rcases List.mem_append.mp hx with hxb | hxm
  · exact .hyp (box_mem_of_mem_boxes hxb)
  · rcases List.mem_map.mp hxm with ⟨χ, hχ, rfl⟩
    exact .mp (.thm (four χ)) (.hyp (box_mem_of_mem_boxes hχ))

/-- **Boxed-context necessitation** — the derived modal rule
`boxContent Δ ⊢ φ ⟹ Δ ⊢ □φ`. Close the hypothesis to the GL theorem
`⊢ ⋀(boxContent Δ) → φ`, box-monotonize, and discharge `□⋀(boxContent Δ)`
from `Δ` by box-distribution + `four`. This is the admissible rule that
replaces (forbidden) necessitation under hypotheses in every
canonical-model argument for GL. -/
theorem deriv_box_of_boxContent {Δ : List GLFormula} {φ : GLFormula}
    (h : PDeriv (boxContent Δ) φ) : PDeriv Δ (□φ) :=
  .mp (.thm (box_mono (gl_conjList_imp h)))
    (deriv_box_conjList _ boxContent_all_boxed)

-- ============================================================
-- PART 4: Löb's rule and the Löb-trick seed lemma
-- ============================================================

/-- **Löb's rule**: if `⊢ □φ → φ` then `⊢ φ`. (Necessitate the
hypothesis, collapse with the `L` axiom, and apply the hypothesis.) -/
theorem lob_rule {φ : GLFormula} (h : GL_proves (□φ ⟶ φ)) : GL_proves φ :=
  h.mp ((GL_proves.lob φ).mp (.nec h))

/-- **The Löb-trick seed lemma** — the box case of the future truth
lemma: if `Δ ⊬ □ψ`, then the successor seed `{¬ψ, □ψ} ∪ boxContent Δ`
is consistent.

Contrapositive: a refutation of the seed closes under the deduction
theorem + double-negation elimination to `boxContent Δ ⊢ □ψ → ψ`;
boxed-context necessitation gives `Δ ⊢ □(□ψ → ψ)`; **Löb's axiom**
collapses this to `Δ ⊢ □ψ`, contradiction. The `□ψ` conjunct in the
seed costs nothing here but is what forces the canonical relation to
strictly grow the boxed stock in S22c (converse well-foundedness). -/
theorem lob_seed_consistent {Δ : List GLFormula} {ψ : GLFormula}
    (hnb : ¬ PDeriv Δ (□ψ)) :
    Consistent ((ψ ⟶ ⊥ₘ) :: □ψ :: boxContent Δ) := by
  intro hbot
  apply hnb
  have h3 : PDeriv (boxContent Δ) (□ψ ⟶ ψ) :=
    (PDeriv.mp (.thm (dne ψ)) hbot.deduction).deduction
  exact .mp (.thm (GL_proves.lob ψ)) (deriv_box_of_boxContent h3)

/-- The seed lemma in world form: a maximal consistent subset of a
closure `L` that omits `□ψ ∈ L` has a consistent successor seed. -/
theorem lob_seed_consistent_of_maximal {L Δ : List GLFormula}
    (h : MaximalIn L Δ) {ψ : GLFormula} (hψL : □ψ ∈ L) (hnb : □ψ ∉ Δ) :
    Consistent ((ψ ⟶ ⊥ₘ) :: □ψ :: boxContent Δ) :=
  lob_seed_consistent fun hd => hnb (h.mem_of_deriv hψL hd)

#check @deriv_box_of_boxContent
#check @lob_rule
#check @lob_seed_consistent

end GodelSecondLobSeed
