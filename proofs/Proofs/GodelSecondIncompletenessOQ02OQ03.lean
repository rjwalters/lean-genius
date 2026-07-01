/-
# The Löb Boundary: which provability-sentences GL proves about itself

Open Question (godel-second-incompleteness-oq02-oq-03):
"Löb's theorem characterizes when F ⊢ A from F ⊢ (□A → A). Is there a similar
'Löb boundary' theorem: a precise characterization of which sentences about F's
provability are provable in F itself?"

Answer: YES, and it is exactly **Löb's theorem in derived-rule form**. Working in
the Hilbert system `GL_proves` for the provability logic GL (Gödel–Löb), this file
proves the sharp characterization

    GL ⊢ (□A → A)   ↔   GL ⊢ A          (`reflection_iff_provable`)

i.e. the local reflection principle `□A → A` is provable *exactly* for the
sentences `A` that GL already proves outright. This is the "Löb boundary": GL never
proves a reflection sentence beyond the boundary of its own theorems.

Specialising to `A = ⊥` recovers **Gödel's Second Incompleteness theorem** as a
one-line corollary, since the consistency statement is `Con := ¬□⊥ = (□⊥ → ⊥)`:

    GL ⊢ Con   ↔   GL ⊢ ⊥            (`consistency_boundary`)
    GL consistent  ⟹  GL ⊬ Con       (`second_incompleteness`)

Everything is purely syntactic and rests only on the `GL_proves` constructors
(`taut`, `lob`, `mp`, `nec`) from the companion `GodelSecondIncompletenessOQ02GLSyntax`.
No arithmetic, no Kripke semantics, no axioms, no sorries.

References:
- Löb, M.H. (1955). "Solution of a problem of Leon Henkin." JSL 20, 115–118.
- Boolos, G. (1993). *The Logic of Provability*. Cambridge University Press, Ch. 1–2.
- Smoryński, C. (1985). *Self-Reference and Modal Logic*. Springer, §1.
-/

import Proofs.GodelSecondIncompletenessOQ02GLSyntax

namespace GodelSecondIncompletenessOQ02OQ03

open GodelSecondGLSyntax

-- ============================================================
-- PART I: Löb's theorem (derived rule) and the reflection boundary
-- ============================================================

/-- **Löb's theorem (derived-rule form).** If GL proves the reflection principle
    `□A → A`, then GL proves `A` outright. Derivation: necessitate the hypothesis to
    get `□(□A → A)`; Löb's axiom `□(□A → A) → □A` then yields `□A`; one more modus
    ponens with the hypothesis `□A → A` gives `A`. -/
theorem lob_theorem (A : GLFormula) (h : GL_proves (.impl (.box A) A)) :
    GL_proves A := by
  have h1 : GL_proves (.box (.impl (.box A) A)) := GL_proves.nec h
  have h2 : GL_proves (.impl (.box (.impl (.box A) A)) (.box A)) := GL_proves.lob A
  have h3 : GL_proves (.box A) := GL_proves.mp h2 h1
  exact GL_proves.mp h h3

/-- The easy converse: if GL proves `A`, it proves the reflection principle `□A → A`.
    Immediate from the propositional axiom `k1 : A → (□A → A)` and modus ponens. -/
theorem provable_imp_reflection (A : GLFormula) (h : GL_proves A) :
    GL_proves (.impl (.box A) A) :=
  GL_proves.mp (GL_proves.taut (PropAxiom.k1 A (.box A))) h

/-- **The Löb boundary.** The reflection sentence `□A → A` is GL-provable if and only
    if `A` itself is GL-provable. This is the precise characterization the open
    question asks for: GL proves a "reflection fact about its own provability" exactly
    at — and never beyond — the boundary of its own theorems. -/
theorem reflection_iff_provable (A : GLFormula) :
    GL_proves (.impl (.box A) A) ↔ GL_proves A :=
  ⟨lob_theorem A, provable_imp_reflection A⟩

-- ============================================================
-- PART II: Gödel's Second Incompleteness as the boundary at ⊥
-- ============================================================

/-- The internal consistency statement of GL: `Con := ¬□⊥`, i.e. `□⊥ → ⊥`. -/
def consistencyGL : GLFormula := (GLFormula.box GLFormula.falsum).not

/-- **The consistency boundary (Gödel's Second Incompleteness, modal form).**
    GL proves its own consistency statement `Con = ¬□⊥` if and only if GL is
    inconsistent (proves `⊥`). This is the `A = ⊥` instance of the Löb boundary,
    since `Con = (□⊥ → ⊥)` is exactly the reflection sentence for `⊥`. -/
theorem consistency_boundary :
    GL_proves consistencyGL ↔ GL_proves GLFormula.falsum := by
  unfold consistencyGL GLFormula.not
  exact reflection_iff_provable GLFormula.falsum

/-- **Gödel's Second Incompleteness theorem (contrapositive form).** If GL is
    consistent — it does not prove `⊥` — then GL does not prove its own consistency
    statement `Con = ¬□⊥`. A consistent provability logic cannot certify its own
    consistency. -/
theorem second_incompleteness (hcon : ¬ GL_proves GLFormula.falsum) :
    ¬ GL_proves consistencyGL :=
  fun h => hcon (consistency_boundary.mp h)

-- ============================================================
-- PART III: The internalized (box-level) Löb boundary
-- ============================================================

/-! The boundary of Part I is *external*: it characterizes which reflection
sentences GL proves about itself, viewed from the meta-level. A sharper question
is whether GL *certifies that boundary internally* — i.e. whether the equivalence
"`□A → A` is necessary ⟺ `A` is necessary" is itself a GL theorem. The answer is
yes, at the box level: GL proves `□(□A → A) → □A` (its defining Löb axiom) and the
converse `□A → □(□A → A)`, so it internalizes the boundary one box deep. The
external `lob_theorem` then factors through this internal equivalence: necessitate
the hypothesis, apply the box-level boundary to land on `□A`, and discharge with the
hypothesis. -/

/-- **GL internally certifies "provable ⟹ reflection".** GL proves
    `□A → □(□A → A)`: whenever `A` is necessary, the reflection principle `□A → A`
    is itself necessary. Derivation: `A → (□A → A)` is the propositional axiom `k1`;
    necessitate it (`nec`) and distribute the box with the modal `K` axiom, then
    modus ponens. This direction needs **no Löb axiom** — it holds already in `K`. -/
theorem box_provable_imp_box_reflection (A : GLFormula) :
    GL_proves (.impl (.box A) (.box (.impl (.box A) A))) :=
  GL_proves.mp (GL_proves.k A (.impl (.box A) A))
    (GL_proves.nec (GL_proves.taut (PropAxiom.k1 A (.box A))))

/-- **GL internally certifies "reflection ⟹ provable".** GL proves
    `□(□A → A) → □A`. This is exactly Löb's axiom `lob`; it is named here as the
    converse of `box_provable_imp_box_reflection`, making the box-level boundary
    symmetric. The fact that *this* direction is the one requiring the Löb axiom
    (while the other holds in plain `K`) is precisely what makes GL the logic of
    provability. -/
theorem box_reflection_imp_box_provable (A : GLFormula) :
    GL_proves (.impl (.box (.impl (.box A) A)) (.box A)) :=
  GL_proves.lob A

/-- **The internalized Löb boundary.** GL proves `□(□A → A)` if and only if GL
    proves `□A`. This is the *necessitated* form of `reflection_iff_provable`: GL
    certifies the necessity of the reflection principle exactly when it certifies the
    necessity of `A`. Forward is Löb's axiom; backward is
    `box_provable_imp_box_reflection`. Unlike the external boundary, both directions
    here live one box deep, so this is a statement GL makes about its own provability
    predicate rather than a meta-level observation about GL. -/
theorem box_reflection_iff_box_provable (A : GLFormula) :
    GL_proves (.box (.impl (.box A) A)) ↔ GL_proves (.box A) :=
  ⟨fun h => GL_proves.mp (box_reflection_imp_box_provable A) h,
   fun h => GL_proves.mp (box_provable_imp_box_reflection A) h⟩

/-- **Internal form of Gödel's Second Incompleteness.** The `A = ⊥` instance of the
    internalized boundary: GL proves `□Con = □(□⊥ → ⊥)` if and only if GL proves
    `□⊥`. In words, GL *provably-proves* its own consistency exactly when it
    *provably-proves* `⊥` — the box-level analogue of `consistency_boundary`. -/
theorem box_consistency_boundary :
    GL_proves (.box consistencyGL) ↔ GL_proves (.box GLFormula.falsum) := by
  unfold consistencyGL GLFormula.not
  exact box_reflection_iff_box_provable GLFormula.falsum

-- ============================================================
-- PART IV: Summary
-- ============================================================

/-- **Summary.** The Löb boundary, formalized end to end: GL proves `□A → A` iff it
    proves `A`; specialised to `⊥`, GL proves its consistency iff it is inconsistent;
    hence a consistent GL cannot prove its own consistency. 0 axioms, 0 sorries. -/
theorem lob_boundary_verified :
    (∀ A : GLFormula, GL_proves (.impl (.box A) A) ↔ GL_proves A) ∧
    (GL_proves consistencyGL ↔ GL_proves GLFormula.falsum) ∧
    (¬ GL_proves GLFormula.falsum → ¬ GL_proves consistencyGL) :=
  ⟨reflection_iff_provable, consistency_boundary, second_incompleteness⟩

/-- **Summary (internalized boundary).** The box-level Löb boundary, formalized end
    to end: GL proves both implications of `□(□A → A) ↔ □A`, so GL proves
    `□(□A → A)` iff it proves `□A`; specialised to `⊥`, GL proves `□Con` iff it
    proves `□⊥`. GL therefore certifies its own Löb boundary internally, one box
    deep. 0 axioms, 0 sorries. -/
theorem internal_lob_boundary_verified :
    (∀ A : GLFormula, GL_proves (.impl (.box A) (.box (.impl (.box A) A)))) ∧
    (∀ A : GLFormula, GL_proves (.impl (.box (.impl (.box A) A)) (.box A))) ∧
    (∀ A : GLFormula, GL_proves (.box (.impl (.box A) A)) ↔ GL_proves (.box A)) ∧
    (GL_proves (.box consistencyGL) ↔ GL_proves (.box GLFormula.falsum)) :=
  ⟨box_provable_imp_box_reflection, box_reflection_imp_box_provable,
   box_reflection_iff_box_provable, box_consistency_boundary⟩

end GodelSecondIncompletenessOQ02OQ03
