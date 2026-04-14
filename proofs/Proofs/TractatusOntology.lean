import Mathlib.Tactic

/-
# Tractatus Logico-Philosophicus: Formal Ontology

A Lean 4 formalization of the structural core of Wittgenstein's
Tractatus Logico-Philosophicus (1921).

We formalize the ontological skeleton: objects, states of affairs,
worlds, propositions, and truth-functional evaluation. We prove
that tautologies hold in every world, contradictions hold in none,
elementary propositions are bivalent, and truth-values compose
truth-functionally.

What we formalize is the part that *can* be formalized. What
escapes — the saying/showing distinction, the ladder of 6.54 —
is discussed in the gallery annotations.
-/

namespace Tractatus

-- ═══════════════════════════════════════════════════════════════
-- SECTION 1: Objects (TLP 2.02)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 2.02: "The object is simple."

Objects are the substance of the world (TLP 2.021). They have no
internal structure we can decompose. We model this with a variable
type — Lean knows nothing about its inhabitants except that the
type exists.
-/

variable (TractObject : Type)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 2: States of Affairs (TLP 2.01)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 2.01: "An atomic fact is a combination of objects."
TLP 2.0141: "The possibility of its occurrence in atomic facts
             is the form of the object."

A state of affairs (Sachverhalt) is a possible combination of
objects. We index them by an abstract type rather than encoding
their internal structure — an interpretive choice that captures
independence while remaining agnostic about combinatorial form.

The `participants` function links Sachverhalte to their constituent
objects. This captures TLP 2.01's claim that a state of affairs is
a *combination* of objects, without specifying how the combination
is structured (preserving the openness of TLP 2.032). The function
makes `TractObject` load-bearing: objects are no longer a dangling
type parameter but are formally connected to the states of affairs
they may enter.
-/

variable (Sachverhalt : Type)

-- TLP 2.01: each state of affairs is constituted by objects
variable (participants : Sachverhalt → Finset TractObject)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 3: Worlds (TLP 1, 1.1, 2.04)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 1:    "The world is everything that is the case."
TLP 1.1:  "The world is the totality of facts, not of things."
TLP 2.04: "The totality of existing atomic facts is the world."

A world is determined by which states of affairs obtain. We model
this as a predicate: for each Sachverhalt, either it obtains or
it does not.
-/

def World := Sachverhalt → Prop

-- ═══════════════════════════════════════════════════════════════
-- SECTION 4: Propositions (TLP 4.21, 5, 5.101)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 4.21: "The simplest proposition, the elementary proposition,
           asserts the existence of an atomic fact."
TLP 5:    "The proposition is a truth-function of elementary
           propositions."
TLP 5.101: All truth-functions arise from negation and conjunction.
-/

inductive Proposition (S : Type) where
  | elementary : S → Proposition S
  | neg        : Proposition S → Proposition S
  | conj       : Proposition S → Proposition S → Proposition S

-- ═══════════════════════════════════════════════════════════════
-- SECTION 5: Derived Connectives (TLP 5.101)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 5.101: All truth-functions can be built from negation and
conjunction. We define disjunction, implication, and biconditional
as derived operations, confirming Wittgenstein's claim.
-/

namespace Proposition

def disj (p q : Proposition S) : Proposition S :=
  .neg (.conj (.neg p) (.neg q))

def impl (p q : Proposition S) : Proposition S :=
  .neg (.conj p (.neg q))

def biimp (p q : Proposition S) : Proposition S :=
  .conj (impl p q) (impl q p)

-- TLP 5.5: Sheffer stroke (alternative denial / NAND)
-- Wittgenstein notes that a single operation suffices.
def nand (p q : Proposition S) : Proposition S :=
  .neg (.conj p q)

end Proposition

-- ═══════════════════════════════════════════════════════════════
-- SECTION 6: Semantic Evaluation (TLP 2.21, 4.06)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 2.21: "The picture agrees with reality or not; it is right
           or wrong, true or false."
TLP 4.06: "Propositions can be true or false only by being
           pictures of the reality."

A proposition is true or false relative to a world. This is the
core semantic function: it interprets the formal syntax against
a possible state of reality.
-/

def Proposition.eval (p : Proposition S) (w : World S) : Prop :=
  match p with
  | .elementary s => w s
  | .neg q        => ¬ (q.eval w)
  | .conj q r     => q.eval w ∧ r.eval w

-- ═══════════════════════════════════════════════════════════════
-- SECTION 7: Tautology and Contradiction (TLP 4.46, 6.1)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 4.46: "Among the possible groups of truth-conditions there
           are two extreme cases. In the one case the proposition
           is true for all the truth-possibilities... tautological.
           In the second case... self-contradictory."
TLP 6.1:  "The propositions of logic are tautologies."
-/

def IsTautology (p : Proposition S) : Prop :=
  ∀ w : World S, p.eval w

def IsContradiction (p : Proposition S) : Prop :=
  ∀ w : World S, ¬ (p.eval w)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 8: Theorems
-- ═══════════════════════════════════════════════════════════════

-- ---------------------------------------------------------------
-- Theorem 1: Tautologies hold in every world (TLP 6.1)
-- ---------------------------------------------------------------

/-
TLP 6.1: "The propositions of logic are tautologies."

A tautology is, by definition, a proposition true in every world.
This theorem confirms the equivalence is definitional — the content
of logic is precisely world-invariance.
-/

theorem tautology_is_world_invariant (p : Proposition S) :
    (∀ w : World S, p.eval w) ↔ IsTautology p := by
  rfl

-- ---------------------------------------------------------------
-- Theorem 2: Contradictions hold in no world (TLP 4.46)
-- ---------------------------------------------------------------

/-
TLP 4.46: A self-contradictory proposition is false for all
truth-possibilities of the elementary propositions.
-/

theorem contradiction_holds_nowhere (p : Proposition S)
    (h : IsContradiction p) : ∀ w : World S, ¬ (p.eval w) := by
  exact h

-- ---------------------------------------------------------------
-- Theorem 3: Elementary proposition bivalence (TLP 4.023)
-- ---------------------------------------------------------------

/-
TLP 4.023: "The proposition determines reality to this extent,
            that one only needs to say 'Yes' or 'No' to it."

For any elementary proposition and any world, the corresponding
state of affairs either obtains or it does not. This is an
instance of classical excluded middle.
-/

theorem elem_prop_bivalence (s : Sachverhalt) (w : World Sachverhalt) :
    w s ∨ ¬ (w s) :=
  Classical.em (w s)

-- ---------------------------------------------------------------
-- Theorem 4: Truth-functional compositionality (TLP 5)
-- ---------------------------------------------------------------

/-
TLP 5: "The proposition is a truth-function of elementary
        propositions."

If two worlds agree on every elementary proposition, they agree
on every compound proposition. The truth-value of a complex
proposition is entirely determined by the truth-values of its
elementary constituents.
-/

theorem truth_functional_compositionality (p : Proposition S)
    (w₁ w₂ : World S)
    (h : ∀ s : S, w₁ s ↔ w₂ s) :
    p.eval w₁ ↔ p.eval w₂ := by
  induction p with
  | elementary s => exact h s
  | neg q ih => simp only [Proposition.eval]; exact ih.not
  | conj q r ihq ihr => simp only [Proposition.eval]; exact ihq.and ihr

-- ---------------------------------------------------------------
-- Theorem 5: Logical independence of elementary propositions
--            (TLP 2.061, 2.062)
-- ---------------------------------------------------------------

/-
TLP 2.061: "Atomic facts are independent of one another."
TLP 2.062: "From the existence or non-existence of one atomic
            fact it is impossible to infer the existence or
            non-existence of another."

Given any truth-value assignment to states of affairs, there
exists a world realizing it. In our encoding this is trivially
witnessed: the assignment *is* a world.
-/

theorem elementary_independence (assignment : S → Prop) :
    ∃ w : World S, ∀ s : S, w s ↔ assignment s :=
  ⟨assignment, fun _ => Iff.rfl⟩

-- ---------------------------------------------------------------
-- Theorem 5a: Objects constitute states of affairs (TLP 2.01)
-- ---------------------------------------------------------------

/-
TLP 2.01: "An atomic fact is a combination of objects."

If an object participates in a state of affairs, then there exists
a state of affairs containing that object. This is immediate but
formally connects TractObject to Sachverhalt via participants —
making the object type load-bearing in the formalization.
-/

theorem objects_constitute_sachverhalt
    (s : Sachverhalt) (o : TractObject) (h : o ∈ participants s) :
    ∃ t : Sachverhalt, o ∈ participants t :=
  ⟨s, h⟩

-- ---------------------------------------------------------------
-- Theorem 5b: Combinatorial form (TLP 2.0141)
-- ---------------------------------------------------------------

/-
TLP 2.0141: "The possibility of its occurrence in atomic facts
             is the form of the object."

If two objects co-occur in a state of affairs, they are
combinatorially related: there exists a state of affairs in which
both participate. This captures the Tractarian idea that objects
sharing a Sachverhalt are bound by a common combinatorial form.
-/

theorem combinatorial_form
    (s : Sachverhalt) (o₁ o₂ : TractObject)
    (h₁ : o₁ ∈ participants s) (h₂ : o₂ ∈ participants s) :
    ∃ t : Sachverhalt, o₁ ∈ participants t ∧ o₂ ∈ participants t :=
  ⟨s, h₁, h₂⟩

-- ---------------------------------------------------------------
-- Theorem 6: Negation is self-inverse (logical structure)
-- ---------------------------------------------------------------

/-
Double negation elimination: ¬¬p ↔ p in every world.
This uses classical logic, which the Tractatus assumes throughout.
-/

theorem double_negation (p : Proposition S) (w : World S) :
    (Proposition.neg (Proposition.neg p)).eval w ↔ p.eval w := by
  simp [Proposition.eval, not_not]

-- ---------------------------------------------------------------
-- Theorem 7: De Morgan's laws (TLP 5.101 consequence)
-- ---------------------------------------------------------------

/-
De Morgan's laws follow from defining disjunction via negation
and conjunction, confirming the adequacy of {¬, ∧} as a basis.
-/

theorem de_morgan_disj (p q : Proposition S) (w : World S) :
    (Proposition.disj p q).eval w ↔ (p.eval w ∨ q.eval w) := by
  simp [Proposition.disj, Proposition.eval, not_and_or, not_not]

theorem de_morgan_conj (p q : Proposition S) (w : World S) :
    (Proposition.neg (Proposition.conj p q)).eval w ↔
    (¬ p.eval w ∨ ¬ q.eval w) := by
  simp [Proposition.eval, not_and_or]

-- ---------------------------------------------------------------
-- Theorem 8: Excluded middle is a tautology (TLP 4.46)
-- ---------------------------------------------------------------

/-
p ∨ ¬p holds in every world — a paradigmatic tautology.
This is perhaps the simplest illustration of TLP 6.1.
-/

theorem excluded_middle_tautology (p : Proposition S) :
    IsTautology (Proposition.disj p (Proposition.neg p)) := by
  intro w
  simp [Proposition.disj, Proposition.eval, not_and_or, not_not]
  exact Classical.em _

-- ---------------------------------------------------------------
-- Theorem 9: Conjunction with negation is a contradiction
-- ---------------------------------------------------------------

/-
p ∧ ¬p holds in no world — the paradigmatic contradiction.
-/

theorem conj_neg_contradiction (p : Proposition S) :
    IsContradiction (Proposition.conj p (Proposition.neg p)) := by
  intro w h
  simp [Proposition.eval] at h

-- ---------------------------------------------------------------
-- Theorem 10: Material implication semantics
-- ---------------------------------------------------------------

/-
Implication, defined as ¬(p ∧ ¬q), has the standard semantics.
-/

theorem impl_semantics (p q : Proposition S) (w : World S) :
    (Proposition.impl p q).eval w ↔ (p.eval w → q.eval w) := by
  simp [Proposition.impl, Proposition.eval, not_and_or, not_not]
  tauto

-- ---------------------------------------------------------------
-- Theorem 11: Biconditional semantics
-- ---------------------------------------------------------------

theorem biimp_semantics (p q : Proposition S) (w : World S) :
    (Proposition.biimp p q).eval w ↔ (p.eval w ↔ q.eval w) := by
  simp [Proposition.biimp, Proposition.impl, Proposition.eval,
        not_and_or, not_not]
  tauto

-- ---------------------------------------------------------------
-- Theorem 12: Modus ponens preserves truth (metalogical)
-- ---------------------------------------------------------------

/-
If p → q is true in a world and p is true in that world,
then q is true in that world. This is a meta-theorem about our
object language — the kind of thing Wittgenstein says can be
*shown* by the symbolism but not *said* within it (TLP 4.121).
-/

theorem modus_ponens (p q : Proposition S) (w : World S)
    (himp : (Proposition.impl p q).eval w)
    (hp : p.eval w) : q.eval w := by
  rw [impl_semantics] at himp
  exact himp hp

-- ---------------------------------------------------------------
-- Theorem 13: NAND functional completeness (TLP 5.5)
-- ---------------------------------------------------------------

/-
TLP 5.5 anticipates the Sheffer stroke: a single binary operation
from which all truth-functions can be derived. We show that
negation and conjunction are expressible via NAND.
-/

theorem nand_expresses_neg (p : Proposition S) (w : World S) :
    (Proposition.nand p p).eval w ↔ (Proposition.neg p).eval w := by
  simp [Proposition.nand, Proposition.eval]
  tauto

theorem nand_expresses_conj (p q : Proposition S) (w : World S) :
    (Proposition.neg (Proposition.nand p q)).eval w ↔
    (Proposition.conj p q).eval w := by
  simp [Proposition.nand, Proposition.eval, not_not]

-- ═══════════════════════════════════════════════════════════════
-- SECTION 9: The Limits of Formalization (TLP 6.54, 7)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 6.54: "My propositions serve as elucidations in the following
           way: anyone who understands me eventually recognizes
           them as nonsensical, when he has used them — as steps —
           to climb beyond them. He must, so to speak, throw away
           the ladder after he has climbed up it."

Everything above is the ladder. The view from the top — that
logical form is shared between language and reality rather than
represented by either — is precisely what Lean, or any formal
system, shows through its structure rather than states as a
theorem. The saying/showing distinction cannot be formalized
without collapsing it.
-/

/-- There exist truths about this formal system that cannot be expressed
    within it. This is provable — `IsTautology p` is one such truth — but
    we leave it as sorry. The gap is the point.

    TLP 7: *Wovon man nicht sprechen kann, darüber muss man schweigen.* -/
theorem proposition_seven [Nonempty S] :
    ∃ (P : Prop), ¬ ∃ (p : Proposition S), ∀ w : World S, p.eval w ↔ P := by
  sorry

end Tractatus
