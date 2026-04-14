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
-/

variable (Sachverhalt : Type)

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

/-- Bool-valued evaluator for decidable computation.
    Takes a `Bool`-valued world assignment (computable) instead of `Prop`-valued. -/
def Proposition.evalBool (p : Proposition S) (w : S → Bool) : Bool :=
  match p with
  | .elementary s => w s
  | .neg q        => !(q.evalBool w)
  | .conj q r     => q.evalBool w && r.evalBool w

/-- `evalBool` agrees with `eval` when the world is derived from a Bool assignment.
    This bridges computable Bool-valued evaluation to the Prop-valued semantics. -/
theorem Proposition.evalBool_correct (p : Proposition S) (w : S → Bool) :
    (p.evalBool w = true) ↔ p.eval (fun s => w s = true) := by
  induction p with
  | elementary s => simp [evalBool, eval]
  | neg q ih     => simp [evalBool, eval, ih]
  | conj q r ihq ihr => simp [evalBool, eval, Bool.and_eq_true, ihq, ihr]

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
-- SECTION 9: Concrete Examples
-- ═══════════════════════════════════════════════════════════════

/-
To see the Tractarian machinery in action, we instantiate the
abstract Sachverhalt with a concrete type. Two states of affairs
suffice: rain and snow. This lets us construct particular worlds,
evaluate propositions in them, and — via `evalBool` — run the
evaluator with `#eval`.
-/

inductive TwoFacts where
  | rain
  | snow
  deriving DecidableEq, Repr

instance : Fintype TwoFacts where
  elems := {.rain, .snow}
  complete := fun x => by cases x <;> simp [Finset.mem_insert, Finset.mem_singleton]

/-- A world where it rains but does not snow. -/
def rainyWorld : World TwoFacts
  | .rain => True
  | .snow => False

/-- Named propositions for readability. -/
def itRains : Proposition TwoFacts := .elementary .rain
def itSnows : Proposition TwoFacts := .elementary .snow

-- Prop-valued evaluation examples
example : itRains.eval rainyWorld := trivial
example : ¬ itSnows.eval rainyWorld := id
example : (Proposition.disj itRains itSnows).eval rainyWorld := by
  simp [Proposition.disj, Proposition.eval, rainyWorld, itRains, itSnows]
example : ¬ (Proposition.conj itRains itSnows).eval rainyWorld := by
  simp [Proposition.eval, rainyWorld, itRains, itSnows]

/-- A Bool-valued world: rain obtains, snow does not. -/
def rainyWorldBool : TwoFacts → Bool
  | .rain => true
  | .snow => false

-- #eval demonstrations — computable truth values
#eval itRains.evalBool rainyWorldBool                              -- true
#eval itSnows.evalBool rainyWorldBool                              -- false
#eval (Proposition.disj itRains itSnows).evalBool rainyWorldBool   -- true
#eval (Proposition.conj itRains itSnows).evalBool rainyWorldBool   -- false
#eval (Proposition.neg itSnows).evalBool rainyWorldBool            -- true

-- ═══════════════════════════════════════════════════════════════
-- SECTION 10: The Limits of Formalization (TLP 6.54, 7)
-- ═══════════════════════════════════════════════════════════════

-- ---------------------------------------------------------------
-- Lemma: World-constant propositions are trivial (TLP 4.46)
-- ---------------------------------------------------------------

/-- A proposition whose truth value is the same in all worlds
    must be a tautology or a contradiction. -/
lemma world_constant_taut_or_contra (q : Proposition S) [Nonempty S]
    (h : ∀ w₁ w₂ : World S, q.eval w₁ ↔ q.eval w₂) :
    IsTautology q ∨ IsContradiction q := by
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  set w₀ : World S := fun _ => True with hw₀
  by_cases hq : q.eval w₀
  · left
    intro w
    exact (h w₀ w).mp hq
  · right
    intro w hqw
    exact hq ((h w w₀).mp hqw)

-- ---------------------------------------------------------------
-- Theorem: World-independent facts collapse to triviality
--          (TLP 4.12, 4.1212)
-- ---------------------------------------------------------------

/-- Any proposition expressing a world-independent property
    must be a tautology or a contradiction. -/
theorem saying_showing_triviality (q : Proposition S) (P : Prop) [Nonempty S]
    (h : ∀ w : World S, q.eval w ↔ P) :
    IsTautology q ∨ IsContradiction q := by
  apply world_constant_taut_or_contra
  intro w₁ w₂
  exact (h w₁).trans (h w₂).symm

/-- A non-trivial proposition must have different truth values
    in some pair of worlds. -/
theorem contingent_propositions_vary (q : Proposition S) [Nonempty S]
    (h_not_taut : ¬ IsTautology q)
    (h_not_contra : ¬ IsContradiction q) :
    ∃ w₁ w₂ : World S, q.eval w₁ ∧ ¬ q.eval w₂ := by
  push_neg at h_not_contra
  obtain ⟨w₁, hw₁⟩ := h_not_contra
  unfold IsTautology at h_not_taut
  push_neg at h_not_taut
  obtain ⟨w₂, hw₂⟩ := h_not_taut
  exact ⟨w₁, w₂, hw₁, hw₂⟩

-- ═══════════════════════════════════════════════════════════════
-- SECTION: The Limits of Formalization (TLP 6.54, 7)
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

TLP 7: "Wovon man nicht sprechen kann, darueber muss man schweigen."

The object language can formally match any world-independent
truth P — a tautology matches True, a contradiction matches
False. But this matching is trivial: the same tautology would
match ANY true P, and the same contradiction would match ANY
false P. The proposition does not "say" P in any meaningful
sense; it merely shares its truth value by accident of logic.
-/

/-- Proposition 7: expressing a world-independent truth in the
    object language necessarily produces a trivial proposition.
    This is the formal content of TLP 7 — what cannot be said
    (non-trivially) in the object language can only be shown
    by the structure of the metalanguage. -/
theorem proposition_seven (q : Proposition S) (P : Prop) [Nonempty S]
    (h : ∀ w : World S, q.eval w ↔ P) :
    IsTautology q ∨ IsContradiction q :=
  saying_showing_triviality q P h

/-- TLP 7: *Wovon man nicht sprechen kann, darüber muss man schweigen.*

    This axiom marks the boundary of formalization itself. The theorems
    above prove that metalogical content can only be expressed trivially;
    this declaration enacts Wittgenstein's silence — a deliberate gap
    in an otherwise complete formalization. -/
axiom silence : True

end Tractatus
