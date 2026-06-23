import Proofs.TractatusOntology

/-
# Tractatus Logico-Philosophicus: Quantifiers and the General
  Propositional Form (TLP 5.52, 5.521, 5.526, 6)

Companion to `TractatusOntology.lean`.  We extend the propositional
calculus with first-order quantifiers, define evaluation over an
arbitrary domain, and prove truth-functional compositionality for the
extended language.

TLP 5.52: "If the values of ξ are the total values of a function
           f(x) for all values of x, then N(ξ̄) = ∼(∃x).f(x)."

The Tractatus claims that quantifiers are applications of the
N-operator to all values of a propositional function.  For *finite*
domains this is unproblematic; for infinite domains the claim is
philosophically contentious (Geach 1981, Soames 1983).

We formalize the first-order extension, prove key structural
theorems, and leave the N-operator connection to a follow-up that
depends on the N-operator formalization (#10723).
-/

namespace Tractatus

-- ═══════════════════════════════════════════════════════════════
-- SECTION 1: TLP 5.52: First-Order Propositions (FOProp)
-- ═══════════════════════════════════════════════════════════════

/-
We extend `Proposition S` (propositional, no quantifiers) to
`FOProp S D` — first-order propositions parameterized by:
  • `S` — the type of states of affairs (Sachverhalte)
  • `D` — the domain of quantification (individuals)

We use higher-order abstract syntax (HOAS): the binding in
`∀ x, P(x)` is represented by a Lean function `D → FOProp S D`.
This avoids variable-name bookkeeping and substitution machinery
but creates challenges for induction (see the compositionality
proof below).

Design note: `FOProp` embeds propositional `Proposition S` via
`lift` rather than duplicating the constructors.  This keeps the
extension modular and makes the relationship to the base calculus
explicit.
-/

inductive FOProp (S : Type) (D : Type) : Type where
  | lift     : Proposition S → FOProp S D
  | negFO    : FOProp S D → FOProp S D
  | conjFO   : FOProp S D → FOProp S D → FOProp S D
  | forall_  : (D → FOProp S D) → FOProp S D
  | exists_  : (D → FOProp S D) → FOProp S D

-- ═══════════════════════════════════════════════════════════════
-- SECTION 2: TLP 5.52: Evaluation (Extended to First-Order)
-- ═══════════════════════════════════════════════════════════════

/-
Evaluation extends `Proposition.eval` to handle quantifiers.
Universal quantification is standard: `∀ d : D, (f d).eval w`.
Existential quantification is dual: `∃ d : D, (f d).eval w`.

Lean accepts this definition by structural recursion: in each
recursive call, the argument is structurally smaller.  For the
quantifier cases, `f d` is recognized as structurally smaller
than `forall_ f` (respectively `exists_ f`), because the
recursor for HOAS inductives tracks this dependency.
-/

def FOProp.eval (p : FOProp S D) (w : World S) : Prop :=
  match p with
  | .lift q      => q.eval w
  | .negFO q     => ¬ q.eval w
  | .conjFO q r  => q.eval w ∧ r.eval w
  | .forall_ f   => ∀ d : D, (f d).eval w
  | .exists_ f   => ∃ d : D, (f d).eval w

-- ═══════════════════════════════════════════════════════════════
-- SECTION 3: TLP 5.1: Derived Connectives (First-Order Level)
-- ═══════════════════════════════════════════════════════════════

/-
We define disjunction and implication at the first-order level,
mirroring the definitions in `TractatusOntology.lean`.
-/

namespace FOProp

def disjFO (p q : FOProp S D) : FOProp S D :=
  .negFO (.conjFO (.negFO p) (.negFO q))

def implFO (p q : FOProp S D) : FOProp S D :=
  .negFO (.conjFO p (.negFO q))

end FOProp

-- ═══════════════════════════════════════════════════════════════
-- SECTION 4: TLP 5.1-5.14: Core Theorems (First-Order)
-- ═══════════════════════════════════════════════════════════════

-- ---------------------------------------------------------------
-- Theorem 1: Compositionality for FOProp (TLP 5, extended)
-- ---------------------------------------------------------------

/-
The central theorem, extended to first-order propositions:
if two worlds agree on every elementary state of affairs,
they agree on every FOProp — including quantified formulas.

The proof uses the FOProp recursor.  For the quantifier cases,
the induction hypothesis applies pointwise to each `f d`.
We use `funext` and `propext` to handle extensionality under
binders.
-/

theorem truth_functional_compositionality_fo (p : FOProp S D)
    (w₁ w₂ : World S) (h : ∀ s : S, w₁ s ↔ w₂ s) :
    p.eval w₁ ↔ p.eval w₂ := by
  induction p with
  | lift q =>
    simp only [FOProp.eval]
    exact truth_functional_compositionality q w₁ w₂ h
  | negFO q ih =>
    simp only [FOProp.eval]
    exact ih.not
  | conjFO q r ihq ihr =>
    simp only [FOProp.eval]
    exact ihq.and ihr
  | forall_ f ih =>
    simp only [FOProp.eval]
    constructor
    · intro hf d
      exact (ih d).mp (hf d)
    · intro hf d
      exact (ih d).mpr (hf d)
  | exists_ f ih =>
    simp only [FOProp.eval]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, (ih d).mp hd⟩
    · rintro ⟨d, hd⟩
      exact ⟨d, (ih d).mpr hd⟩

-- ---------------------------------------------------------------
-- Theorem 2: Universal–existential duality (TLP 5.52)
-- ---------------------------------------------------------------

/-
TLP 5.52 treats ∃x as ∼∀x∼.  We prove the standard duality:
¬(∀ x, P x) ↔ ∃ x, ¬P x (using classical logic).
-/

theorem forall_exists_duality (f : D → FOProp S D) (w : World S) :
    (FOProp.negFO (FOProp.forall_ (fun d => FOProp.negFO (f d)))).eval w ↔
    (FOProp.exists_ f).eval w := by
  simp only [FOProp.eval, not_forall, not_not]

-- ---------------------------------------------------------------
-- Theorem 3: Universal distribution over conjunction
-- ---------------------------------------------------------------

/-
For all x, (P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x).
-/

theorem forall_distrib_conj (f g : D → FOProp S D) (w : World S) :
    (FOProp.forall_ (fun d => FOProp.conjFO (f d) (g d))).eval w ↔
    (FOProp.conjFO (FOProp.forall_ f) (FOProp.forall_ g)).eval w := by
  simp only [FOProp.eval]
  constructor
  · intro h
    exact ⟨fun d => (h d).1, fun d => (h d).2⟩
  · rintro ⟨hf, hg⟩ d
    exact ⟨hf d, hg d⟩

-- ---------------------------------------------------------------
-- Theorem 4: Existential distribution over disjunction
-- ---------------------------------------------------------------

/-
(∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) requires only
the forward direction in general; the reverse always holds.
We prove the reverse direction (no classical logic needed).
-/

theorem exists_distrib_disj_reverse (f g : D → FOProp S D)
    (w : World S) :
    (FOProp.disjFO (FOProp.exists_ f) (FOProp.exists_ g)).eval w →
    (FOProp.exists_ (fun d => FOProp.disjFO (f d) (g d))).eval w := by
  simp only [FOProp.eval, FOProp.disjFO, not_and_or, not_not]
  rintro (⟨d, hd⟩ | ⟨d, hd⟩)
  · exact ⟨d, Or.inl hd⟩
  · exact ⟨d, Or.inr hd⟩

-- ---------------------------------------------------------------
-- Theorem 5: Lift preserves evaluation
-- ---------------------------------------------------------------

/-
A lifted propositional formula evaluates the same way as the
original — the embedding is truth-preserving.
-/

theorem lift_eval (q : Proposition S) (w : World S) :
    (FOProp.lift q : FOProp S D).eval w ↔ q.eval w := by
  simp [FOProp.eval]

-- ---------------------------------------------------------------
-- Theorem 6: Vacuous quantifier elimination
-- ---------------------------------------------------------------

/-
If the body of a universal quantifier does not depend on the
bound variable, the quantifier is vacuous: (∀ x, P) ↔ P.
This requires `Nonempty D` to go from right to left.
-/

theorem forall_vacuous [Nonempty D] (p : FOProp S D) (w : World S) :
    (FOProp.forall_ (fun _ => p)).eval w ↔ p.eval w := by
  simp [FOProp.eval]
  constructor
  · intro h
    exact h (Classical.arbitrary D)
  · intro h _
    exact h

-- ---------------------------------------------------------------
-- Theorem 7: Double negation (first-order level)
-- ---------------------------------------------------------------

theorem double_negation_fo (p : FOProp S D) (w : World S) :
    (FOProp.negFO (FOProp.negFO p)).eval w ↔ p.eval w := by
  simp [FOProp.eval, not_not]

-- ---------------------------------------------------------------
-- Theorem 8: De Morgan for quantifiers (classical)
-- ---------------------------------------------------------------

/-
The classical De Morgan duality for quantifiers:
¬(∃ x, P x) ↔ ∀ x, ¬P x
-/

theorem not_exists_forall_not (f : D → FOProp S D) (w : World S) :
    (FOProp.negFO (FOProp.exists_ f)).eval w ↔
    (FOProp.forall_ (fun d => FOProp.negFO (f d))).eval w := by
  simp only [FOProp.eval, not_exists]

-- ---------------------------------------------------------------
-- Theorem 9: Elementary bivalence lifts to FOProp
-- ---------------------------------------------------------------

/-
For any FOProp and any world, the proposition either holds or
it does not (classical excluded middle).
-/

theorem fo_bivalence (p : FOProp S D) (w : World S) :
    p.eval w ∨ ¬ (p.eval w) :=
  Classical.em (p.eval w)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 5: TLP 5.502/6.54: Philosophical Limits — Infinite Domains
-- ═══════════════════════════════════════════════════════════════

/-
TLP 5.52 claims that quantifiers are N-operator applications:
  ∀x.f(x) = N(∼f(a), ∼f(b), ∼f(c), ...)
  ∃x.f(x) = ∼N(f(a), f(b), f(c), ...)

For finite domains [Fintype D], this is literally correct — the
universal quantifier is a finite conjunction.  For infinite
domains, Wittgenstein's claim is ungrounded: the N-operator is a
finitary syntactic operation and cannot be applied to infinitely
many arguments.

Geach (1981) argues this is a fundamental gap in the Tractatus;
Soames (1983) shows it undermines the claim that all of logic
reduces to truth-functional operations on elementary propositions.

The finite-domain connection theorem (quantifier_as_nOp_finite)
depends on the N-operator formalization (#10723) and will be
added when that is merged.
-/

end Tractatus
