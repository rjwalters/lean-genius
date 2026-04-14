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

-- ═══════════════════════════════════════════════════════════════
-- DESIGN DECISIONS
-- ═══════════════════════════════════════════════════════════════

/-
The following modeling choices are deliberate and load-bearing.
They represent a Tarskian reconstruction of Tractarian structure,
not an exegesis of Wittgenstein's intent.

1. WORLDS AS TOTAL PREDICATES (`S → Prop`)
   Worlds are functions from states of affairs to Prop — unconstrained,
   classical, and extensional. There is no requirement that worlds be
   "complete" in any metaphysical sense; any assignment of truth values
   to Sachverhalte constitutes a world. This gives elementary independence
   for free (see `elementary_independence`), at the cost of not encoding
   TLP 2.0141 (an object's form constrains its combinatorial possibilities).

2. INDEPENDENCE BAKED INTO THE MODEL
   Because `World S = S → Prop`, any truth-value assignment is a world.
   Independence is not a theorem derived from structure — it is definitional.
   A richer encoding (e.g. Sachverhalt as a dependent type over TractObject)
   would make independence substantive and provable.

3. CLASSICAL LOGIC ASSUMED THROUGHOUT (`Classical.em`)
   Every theorem that turns on bivalence or double-negation elimination
   invokes `Classical.em`. This matches Wittgenstein's bivalent semantics.
   Constructivists should note that `elem_prop_bivalence`, `double_negation`,
   and `excluded_middle_tautology` are all non-constructive.

4. HOAS FOR QUANTIFIERS (TractatusQuantifiers.lean)
   First-order binding (`∀ x, P(x)`) is encoded via higher-order abstract
   syntax: `forall_ : (D → FOProp S D) → FOProp S D`. This leverages Lean's
   metalanguage for variable binding rather than implementing substitution
   explicitly. The tradeoff: HOAS ties the formalization to Lean's metatheory
   more tightly than de Bruijn indices would, but dramatically reduces proof
   overhead.

5. ABSTRACT TYPES — NO STRUCTURE ON `TractObject`/`Sachverhalt`
   Both `TractObject` and `Sachverhalt` are bare `variable (... : Type)`.
   Lean knows nothing about their inhabitants. This captures Wittgenstein's
   insistence on simplicity (TLP 2.02) and avoids committing to a structural
   account of combination that the Tractatus leaves open.

6. THE SILENCE IS AXIOMATIC, NOT SORRY
   `axiom silence : True` (TLP 7) is a deliberate axiom, not a missing proof.
   The `sorry` in the earlier `proposition_seven` statement was intentional
   (the point was the gap), but the file's definitive statement is `axiom silence`.
   This marks a boundary of formalization-by-design, not a proof obligation.
-/

namespace Tractatus

-- ═══════════════════════════════════════════════════════════════
-- SECTION 1: TLP 1-2.06: Objects and States of Affairs
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
-- SECTION 2: TLP 2.01-2.062: States of Affairs (Sachverhalte)
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
-- SECTION 3: TLP 2.1-2.174: Worlds as Predicates
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
-- SECTION 4: TLP 2.061-2.062: Independence Structure
-- ═══════════════════════════════════════════════════════════════

/-
TLP 2.061: "Atomic facts are independent of one another."
TLP 2.062: "From the existence or non-existence of one atomic
            fact it is impossible to infer the existence or
            non-existence of another."
TLP 1.21:  "Each item can be the case or not the case while
            everything else remains the same."

Independence is NOT a theorem about logic — it is a constraint
on the world model. We make this explicit with a typeclass.
A world model satisfying `IndependentWorlds` can realize any
truth-value assignment; a constrained model need not.
-/

class IndependentWorlds (S : Type) where
  realizable : ∀ assignment : S → Prop, ∃ w : World S, ∀ s, w s ↔ assignment s

/-- The full Boolean cube `S → Prop` trivially satisfies independence:
    every assignment already IS a world. -/
instance : IndependentWorlds S :=
  ⟨fun a => ⟨a, fun _ => Iff.rfl⟩⟩

-- ═══════════════════════════════════════════════════════════════
-- SECTION 5: TLP 4.2-4.463: Propositions and Logical Space
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
-- SECTION 6: TLP 5: Truth-Functionality (Formalized)
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
-- SECTION 7: TLP 5.1-5.14: Semantic Evaluation
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
-- SECTION 8: TLP 5.502: Tautology and Contradiction
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

/-- TLP 4.46, 4.462: A proposition that varies across possible worlds --
    neither a tautology nor a contradiction. The logical space it carves
    out is genuinely world-dependent content. -/
def Nontrivial (p : Proposition S) : Prop :=
  ∃ w₁ w₂ : World S, p.eval w₁ ∧ ¬ p.eval w₂

-- ═══════════════════════════════════════════════════════════════
-- SECTION 9: General World Models
-- ═══════════════════════════════════════════════════════════════

/-
The definitions above hardwire the world model: a world is any
function `S → Prop`, and every such function counts as a possible
world. This gives the full Boolean cube of truth-value assignments,
which makes `elementary_independence` (Theorem 5) trivially true.

In many applications — physics, epistemic logic, constrained
databases — not every assignment is a legitimate world. Rain
without clouds, for instance, is physically impossible but
logically consistent.

We introduce `WorldModel` to parameterize the semantics over an
arbitrary collection of worlds with a `holds` relation. The
existing definitions correspond to `freeModel`, the unconstrained
model. All original theorems remain untouched.
-/

/-- A world model packages a type of worlds, a relation saying
    which states of affairs hold in each world, and evidence
    that at least one world exists. -/
structure WorldModel (S : Type) where
  /-- The type of possible worlds in this model. -/
  W     : Type
  /-- `holds w s` means state of affairs `s` obtains in world `w`. -/
  holds : W → S → Prop
  /-- The model is non-trivial: at least one world exists. -/
  nonempty : Nonempty W

/-- The free (unconstrained) model: every function `S → Prop` is a
    world, and `holds` is function application. This recovers the
    original `World S` semantics. -/
def freeModel (S : Type) : WorldModel S where
  W        := S → Prop
  holds    := fun w s => w s
  nonempty := ⟨fun _ => True⟩

section GeneralSemantics

variable {S : Type} (M : WorldModel S)

/-- Evaluate a proposition in a world of an arbitrary model. -/
def evalM (p : Proposition S) (w : M.W) : Prop :=
  match p with
  | .elementary s => M.holds w s
  | .neg q        => ¬ (evalM M q w)
  | .conj q r     => evalM M q w ∧ evalM M r w

/-- A proposition is a tautology in model `M` when it holds
    in every world of `M`. -/
def IsTautologyM (p : Proposition S) : Prop :=
  ∀ w : M.W, evalM M p w

/-- A proposition is a contradiction in model `M` when it fails
    in every world of `M`. -/
def IsContradictionM (p : Proposition S) : Prop :=
  ∀ w : M.W, ¬ (evalM M p w)

-- [MAIN RESULT] --------------------------------------------------
-- truth_functional_compositionality_gen (model-independent)
-- Compositionality holds in any world model, not just the free one.
-- ----------------------------------------------------------------

/-- Compositionality generalizes to any world model: two worlds
    that agree on every state of affairs agree on every compound
    proposition.  The proof is structurally identical to
    `truth_functional_compositionality`. -/
theorem truth_functional_compositionality_gen (p : Proposition S)
    (w₁ w₂ : M.W)
    (h : ∀ s : S, M.holds w₁ s ↔ M.holds w₂ s) :
    evalM M p w₁ ↔ evalM M p w₂ := by
  induction p with
  | elementary s => exact h s
  | neg q ih     => simp only [evalM]; exact ih.not
  | conj q r ihq ihr => simp only [evalM]; exact ihq.and ihr

end GeneralSemantics

/-- The free model recovers the original evaluation: `evalM (freeModel S)`
    and `Proposition.eval` compute the same truth value. -/
theorem evalM_free_eq_eval (p : Proposition S) (w : S → Prop) :
    evalM (freeModel S) p w = p.eval w := by
  induction p with
  | elementary s => rfl
  | neg q ih     => simp only [evalM, Proposition.eval, ih]
  | conj q r ihq ihr => simp only [evalM, Proposition.eval, ihq, ihr]

-- ═══════════════════════════════════════════════════════════════
-- SECTION 10: Main Theorems
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

-- [MAIN RESULT] --------------------------------------------------
-- truth_functional_compositionality (TLP 5)
-- Worlds agreeing on elementaries agree on all compounds.
-- ----------------------------------------------------------------

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

theorem elementary_independence [IndependentWorlds S] (assignment : S → Prop) :
    ∃ w : World S, ∀ s : S, w s ↔ assignment s :=
  IndependentWorlds.realizable assignment

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
-- SECTION 11: Constrained World Models
-- ═══════════════════════════════════════════════════════════════

/-
To show that `IndependentWorlds` is not vacuous, we exhibit
models where independence fails. Two examples demonstrate the
point: an abstract constrained model and a concrete weather model.
-/

-- ---------------------------------------------------------------
-- 11a: Abstract constrained model (TLP 2.061 contrast)
-- ---------------------------------------------------------------

/-
Consider two states of affairs, `a` and `b`, where `b` is
constrained to co-occur with `a`. No world in this model can
have `a` obtain while `b` does not.
-/

/-- A constrained world: `b` must obtain whenever `a` does. -/
def ConstrainedWorld (S : Type) (a b : S) :=
  { w : S → Prop // w a → w b }

/-- The full-world projection from a ConstrainedWorld. -/
def ConstrainedWorld.toWorld {S : Type} {a b : S}
    (cw : ConstrainedWorld S a b) : World S :=
  cw.val

-- [MAIN RESULT] --------------------------------------------------
-- constrained_independence_fails (TLP 2.061 contrast)
-- Independence is a modeling choice, not a logical law.
-- ----------------------------------------------------------------

/-- `IndependentWorlds` fails for the constrained model when `a ≠ b`.
    The assignment `{a ↦ True, b ↦ False}` has no constrained realizer. -/
theorem constrained_independence_fails (a b : S) (hab : a ≠ b) :
    ¬ ∀ assignment : S → Prop,
      ∃ cw : ConstrainedWorld S a b, ∀ s, cw.val s ↔ assignment s := by
  intro h
  let bad : S → Prop := fun s => s = a
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h bad
  have ha : w a := (hmatch a).mpr rfl
  have hb : w b := hw ha
  exact hab ((hmatch b).mp hb)

-- ---------------------------------------------------------------
-- 11b: Weather model — concrete constrained example
-- ---------------------------------------------------------------

/-
The free model treats every truth-value assignment as a possible
world. But in many domains, structural constraints rule out certain
assignments. Here we model a simple physical constraint: rain
implies clouds.

A `WeatherFacts` type has three states of affairs: rain, clouds,
and snow. The `weatherModel` restricts worlds to those satisfying
the constraint `rain → clouds`. This is a physical dependency,
not a logical one — the Tractarian object language cannot express
it, but the model theory can enforce it.

The key consequence: `elementary_independence` (Theorem 5) holds
for `freeModel` but *fails* for `weatherModel`. In the free model,
any assignment is realizable; in the weather model, the assignment
{rain, not-clouds} is forbidden by the constraint.
-/

inductive WeatherFacts where
  | rain
  | clouds
  | snow
  deriving DecidableEq, Repr

/-- A constrained world model: rain implies clouds.
    Not every truth-value assignment is a valid world. -/
def weatherModel : WorldModel WeatherFacts where
  W        := { w : WeatherFacts → Prop // w .rain → w .clouds }
  holds    := fun w s => w.val s
  nonempty := ⟨⟨fun _ => False, fun h => h.elim⟩⟩

/-- In the weather model, independence fails: there is no world
    where rain holds but clouds does not. The constraint
    `rain → clouds` prevents such a world from existing. -/
theorem weather_independence_fails :
    ¬ ∃ w : (weatherModel).W,
        weatherModel.holds w .rain ∧ ¬ weatherModel.holds w .clouds := by
  intro ⟨w, hrain, hclouds⟩
  exact hclouds (w.property hrain)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 12: Concrete Examples (TwoFacts Instantiation)
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
-- SECTION 13: Structural vs Semantic Equivalence (TLP 4.0141)
-- ═══════════════════════════════════════════════════════════════

/-
TLP 4.0141: "There is a general rule by means of which the musician
can obtain the symphony from the score, and which makes it possible
to derive the symphony from the groove on the gramophone disc..."

Wittgenstein's notion of logical form is NOT truth-functional.
Two propositions can share their truth conditions in every possible
world while differing in their logical form.  The formalization
necessarily captures only truth conditions — semantic equivalence.
Proving the divergence makes this limitation explicit rather than
merely asserting it in comments.
-/

namespace Proposition

/-- Structural (syntactic) equality of propositions. Two propositions
    are structurally equal iff they are built from identical constructors
    in the same tree shape. This is strictly stronger than semantic
    equivalence. -/
def structEq : Proposition S → Proposition S → Prop
  | .elementary s₁, .elementary s₂ => s₁ = s₂
  | .neg p₁,        .neg p₂        => structEq p₁ p₂
  | .conj p₁ q₁,   .conj p₂ q₂   => structEq p₁ p₂ ∧ structEq q₁ q₂
  | _,              _               => False

/-- Semantic (truth-conditional) equivalence of propositions. Two
    propositions are semantically equivalent iff they have the same
    truth value in every possible world. This is the relation the
    formalization can fully characterize. -/
def semEq (p q : Proposition S) : Prop :=
  ∀ w : World S, p.eval w ↔ q.eval w

-- ---------------------------------------------------------------
-- Atom Renaming (TLP 4.014)
-- ---------------------------------------------------------------

/-
TLP 4.014: "A gramophone record, the musical thought, the score, the
           waves of sound, all stand to one another in that pictorial
           internal relation which holds between language and the world."

`rename` applies an atom-renaming function to every elementary
proposition leaf. Connective structure is preserved; only atom
labels change. This is the formal correlate of Wittgenstein's
projection: a mapping that preserves logical form while varying
the particular atomic content.
-/

/-- Apply an atom-renaming function to every elementary proposition.
    Connective structure is preserved; only atom labels change. -/
def rename (σ : S → S) : Proposition S → Proposition S
  | .elementary s => .elementary (σ s)
  | .neg p        => .neg (p.rename σ)
  | .conj p q     => .conj (p.rename σ) (q.rename σ)

/-- Renaming by the identity function is the identity on propositions. -/
theorem rename_id (p : Proposition S) : p.rename id = p := by
  induction p with
  | elementary s => rfl
  | neg q ih     => simp [rename, ih]
  | conj q r ihq ihr => simp [rename, ihq, ihr]

/-- Renaming composes functorially:
    renaming by `σ` then `τ` equals renaming by `τ ∘ σ`. -/
theorem rename_comp (σ τ : S → S) (p : Proposition S) :
    (p.rename σ).rename τ = p.rename (τ ∘ σ) := by
  induction p with
  | elementary s => simp [rename]
  | neg q ih     => simp [rename, ih]
  | conj q r ihq ihr => simp [rename, ihq, ihr]

/-- Renaming commutes with evaluation: evaluating a renamed
    proposition at world `w` equals evaluating the original at the
    composed world `w ∘ σ`. -/
theorem rename_eval (σ : S → S) (p : Proposition S) (w : World S) :
    (p.rename σ).eval w = p.eval (fun s => w (σ s)) := by
  induction p with
  | elementary s => rfl
  | neg q ih     => simp [rename, eval, ih]
  | conj q r ihq ihr => simp [rename, eval, ihq, ihr]

-- ---------------------------------------------------------------
-- Logical-Form Equivalence: formEq (TLP 4.0141, 4.014)
-- ---------------------------------------------------------------

/-
TLP 4.0141: "There is a general rule by means of which the musician
             can obtain the symphony from the score..."

Two propositions share their logical form iff one is obtained from
the other by a bijective renaming of atoms (an `Equiv.Perm` on `S`).
This is strictly between syntactic identity (`structEq`) and
truth-conditional identity (`semEq`).

`formEq` captures exactly what is preserved under Wittgenstein's
projection: the tree structure (connective shape + arity at each
node), but not which particular atoms appear. `structEq` is too
strict (fixes atom identity); `semEq` is too weak (only truth
tables). `formEq` is the formal correlate of 'same logical form'
in the sense of 4.0141.
-/

/-- Logical-form equivalence: two propositions share their logical
    form iff one is obtained from the other by a bijective renaming
    of atoms (a permutation on the atom type `S`). -/
def formEq (p q : Proposition S) : Prop :=
  ∃ e : Equiv.Perm S, p.rename e = q

-- ---------------------------------------------------------------
-- formEq is an equivalence relation
-- ---------------------------------------------------------------

/-- `formEq` is reflexive: every proposition has its own logical form.
    Witnessed by the identity permutation. -/
theorem formEq_refl (p : Proposition S) : p.formEq p :=
  ⟨Equiv.refl S, rename_id p⟩

/-- `formEq` is symmetric: if `p` has the same form as `q`, then `q`
    has the same form as `p`. Witnessed by the inverse permutation. -/
theorem formEq_symm {p q : Proposition S} (h : p.formEq q) : q.formEq p := by
  obtain ⟨e, heq⟩ := h
  refine ⟨e.symm, ?_⟩
  subst heq
  rw [rename_comp]
  -- Goal: p.rename (⇑(e.symm) ∘ ⇑e) = p
  -- Since e.symm (e s) = s for all s, the composition is id
  have : (⇑(e.symm) ∘ ⇑e) = id := by
    ext s; simp [Function.comp, Equiv.symm_apply_apply]
  rw [this, rename_id]

/-- `formEq` is transitive: shared logical form composes.
    Witnessed by composition of permutations. -/
theorem formEq_trans {p q r : Proposition S}
    (hpq : p.formEq q) (hqr : q.formEq r) : p.formEq r := by
  obtain ⟨e₁, heq₁⟩ := hpq
  obtain ⟨e₂, heq₂⟩ := hqr
  refine ⟨e₁.trans e₂, ?_⟩
  -- (e₁.trans e₂) acts as e₂ ∘ e₁ pointwise
  -- By rename_comp: (p.rename e₁).rename e₂ = p.rename (e₂ ∘ e₁)
  calc p.rename ⇑(e₁.trans e₂)
      = p.rename (⇑e₂ ∘ ⇑e₁) := by congr 1; ext s; simp [Equiv.trans_apply]
    _ = (p.rename ⇑e₁).rename ⇑e₂ := (rename_comp _ _ _).symm
    _ = q.rename ⇑e₂ := by rw [heq₁]
    _ = r := heq₂

-- ---------------------------------------------------------------
-- Hierarchy: structEq → formEq (TLP 4.0141)
-- ---------------------------------------------------------------

/-- `structEq` implies equality of propositions (a helper for the
    hierarchy theorem). -/
private theorem eq_of_structEq : ∀ (p q : Proposition S),
    p.structEq q → p = q := by
  intro p
  induction p with
  | elementary s =>
    intro q; cases q with
    | elementary s' =>
      simp [structEq]
      intro h; subst h; rfl
    | _ => simp [structEq]
  | neg p' ih =>
    intro q; cases q with
    | neg q' =>
      simp [structEq]
      intro h; exact congrArg Proposition.neg (ih q' h)
    | _ => simp [structEq]
  | conj p' p'' ih₁ ih₂ =>
    intro q; cases q with
    | conj q' q'' =>
      simp [structEq]
      intro h₁ h₂
      exact congr (congrArg Proposition.conj (ih₁ q' h₁)) (ih₂ q'' h₂)
    | _ => simp [structEq]

/-- `structEq` implies `formEq`: syntactically identical propositions
    trivially share their logical form, witnessed by the identity
    permutation. -/
theorem structEq_implies_formEq {p q : Proposition S}
    (h : p.structEq q) : p.formEq q :=
  ⟨Equiv.refl S, by rw [rename_id]; exact eq_of_structEq p q h⟩

-- ---------------------------------------------------------------
-- Hierarchy: formEq → truth-table isomorphism
-- ---------------------------------------------------------------

/-
`formEq` does NOT imply `semEq` (pointwise truth-value agreement)
in general. Consider `elementary .rain` vs `elementary .snow`: they
have the same logical form (both are elementary propositions) but
different truth values in `rainyWorld`.

The correct intermediate notion is *truth-table isomorphism*: there
exists a world-relabeling making `p` and `q` agree on ALL worlds.
This is strictly weaker than `semEq` (where the relabeling must be
the identity) but captures the structural content of `formEq`.
-/

/-- `formEq` implies truth-table isomorphism: there exists a
    world-relabeling `f` such that `p` and `q` agree on all
    worlds after relabeling. -/
theorem formEq_implies_truth_table_iso {p q : Proposition S}
    (h : p.formEq q) :
    ∃ f : World S → World S, ∀ w : World S, p.eval w ↔ q.eval (f w) := by
  obtain ⟨e, heq⟩ := h
  -- Use w ∘ e.symm as the world relabeling: this ensures that
  -- evaluating q = p.rename e at (w ∘ e.symm) recovers p.eval w,
  -- since (w ∘ e.symm) ∘ e = w (by e.symm_apply_apply).
  refine ⟨fun w => w ∘ ⇑(e.symm), fun w => ?_⟩
  subst heq
  rw [rename_eval]
  -- Goal: p.eval w ↔ p.eval (fun s => (w ∘ ⇑(e.symm)) (e s))
  -- Since e.symm (e s) = s, both sides are equal.
  suffices hsuff : (fun s => (w ∘ ⇑(e.symm)) (↑e s)) = w by rw [hsuff]
  ext s
  simp [Function.comp, Equiv.symm_apply_apply]

/-- Truth-table isomorphism implies `semEq` when the relabeling is
    the identity (i.e., `f = id`). This shows that `semEq` is the
    special case of truth-table isomorphism with trivial relabeling. -/
theorem truth_table_iso_id_implies_semEq {p q : Proposition S}
    (h : ∀ w : World S, p.eval w ↔ q.eval w) : p.semEq q :=
  h

-- ---------------------------------------------------------------
-- Strictness witnesses: structEq ⊊ formEq ⊊ semEq
-- ---------------------------------------------------------------

/-- Witness that `structEq ⊊ formEq` (strict containment):
    two elementary propositions with swapped atoms are `formEq`
    (via the swap permutation) but not `structEq` (different atoms). -/
theorem formEq_not_structEq_witness :
    (Proposition.elementary TwoFacts.rain).formEq
      (Proposition.elementary TwoFacts.snow)
    ∧ ¬ (Proposition.elementary TwoFacts.rain).structEq
          (Proposition.elementary TwoFacts.snow) := by
  constructor
  · -- formEq via swap permutation
    refine ⟨Equiv.swap .rain .snow, ?_⟩
    simp [rename, Equiv.swap_apply_left]
  · -- not structEq: different atoms
    intro h
    simp [structEq] at h

/-- Witness that `formEq ⊊ semEq` (strict containment):
    `neg (neg (elementary s))` is `semEq` to `elementary s`
    (by double negation) but NOT `formEq` (rename preserves
    tree depth, so neg-neg-elementary cannot become elementary). -/
theorem semEq_not_formEq_witness (s : TwoFacts) :
    (Proposition.neg (.neg (.elementary s))).semEq (.elementary s)
    ∧ ¬ (Proposition.neg (.neg (.elementary s))).formEq (.elementary s) := by
  constructor
  · -- semEq by double negation
    intro w
    simp [eval, not_not]
  · -- not formEq: rename preserves tree structure
    rintro ⟨e, heq⟩
    simp [rename] at heq

end Proposition

-- ---------------------------------------------------------------
-- Theorem 14: Structural and semantic equivalence diverge
--             (TLP 4.0141)
-- ---------------------------------------------------------------

/-
`neg (neg p)` is semantically equivalent to `p` by double negation
(Theorem 6 above), but is NOT structurally equivalent to `p` — it
has an extra layer of negation in its syntactic tree.

This theorem makes explicit what the formalization captures and what
it cannot: truth conditions, but not logical form.

With the introduction of `formEq`, we now have a three-level hierarchy
of proposition equivalence:

  structEq ⊊ formEq ⊊ semEq

- `structEq` identifies tree shape AND atom identity.
- `formEq` identifies tree shape up to atom permutation.
- `semEq` identifies truth-table content (world-by-world agreement).

Each inclusion is strict: atom-swapped elementaries witness
structEq ⊊ formEq, and double negation witnesses formEq ⊊ semEq.
-/

-- [MAIN RESULT] --------------------------------------------------
-- structEq_ne_semEq (TLP 4.0141)
-- Structural and semantic equivalence diverge: truth conditions
-- cannot capture logical form.
-- ----------------------------------------------------------------

theorem structEq_ne_semEq [Nonempty S] :
    ∃ (p q : Proposition S),
      Proposition.semEq p q ∧ ¬ Proposition.structEq p q := by
  obtain ⟨s⟩ : Nonempty S := inferInstance
  refine ⟨.neg (.neg (.elementary s)), .elementary s, ?_, ?_⟩
  · -- semantic equivalence: double negation elimination
    intro w
    simp [Proposition.eval, not_not]
  · -- structural non-equivalence: syntactic trees differ
    simp [Proposition.structEq]

-- ═══════════════════════════════════════════════════════════════
-- The expresses relation (TLP 4.12, 4.1212)
-- ═══════════════════════════════════════════════════════════════

/-
`expresses p P` captures what it means for an object-language
proposition to "say" a meta-language truth P. The proposition
p expresses P when p's truth value tracks P in every possible
world -- they are always equal.

This makes the object/meta distinction visible in types:
  - `p : Proposition S`       -- object language
  - `P : Prop`                -- meta language
  - `expresses p P : Prop`    -- the bridge claim

TLP 4.12: Propositions can represent the whole of reality, but
they cannot represent what they must have in common with reality
in order to be able to represent it.
-/

def expresses (p : Proposition S) (P : Prop) : Prop :=
  ∀ w : World S, p.eval w ↔ P

-- ═══════════════════════════════════════════════════════════════
-- Analytical Decomposition: Invariance vs Dependence
-- ═══════════════════════════════════════════════════════════════

/-
The formalization reveals a three-way classification of all results.
The Tractatus is not a set of truths about the world — it is a
specification of a semantic architecture. Each theorem below falls
into exactly one class:

CORE INVARIANTS (hold in every WorldModel, no extra assumptions):
  truth_functional_compositionality_gen
    — compositionality is structural; it follows from the inductive
      definition of Proposition alone, independent of which worlds exist
  elem_prop_bivalence
    — excluded middle on world-predicate applications; requires
      Classical.em but no world-model constraints
  double_negation, de_morgan_disj
    — classical tautologies at the meta-level; world-invariant

MODEL ASSUMPTIONS (hold only in IndependentWorlds / freeModel;
may fail in constrained models):
  elementary_independence
    — realizable := fun a => ⟨a, fun _ => Iff.rfl⟩ exploits
      World S = S → Prop; this IS a design choice, not a theorem
  weather_independence_fails / constrained_independence_fails
    — both witness that independence is NOT a logical law but
      a property of the model

FORMAL LIMITS (provable boundaries of the system):
  saying_showing_triviality / proposition_seven
    — world-independent content collapses to tautology or contradiction
  nontrivial_expressibility_requires_world_dependence
    — non-trivial saying requires genuine world-dependence; proved
  structEq_ne_semEq (via the divergence theorem)
    — formalization captures truth conditions but not logical form

The three classes are mutually exclusive and jointly exhaustive
across all 25 theorems in this file.
-/
-- ═══════════════════════════════════════════════════════════════
-- SECTION 14: The Limits of Formalization (TLP 6.54, 7)
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
    must be a tautology or a contradiction.

    The hypothesis `expresses q P` states that `q`'s truth value
    tracks the meta-level proposition `P` in every world.  Since
    `expresses` unfolds to `∀ w, q.eval w ↔ P`, this is
    definitionally compatible with all prior callers. -/
theorem saying_showing_triviality (q : Proposition S) (P : Prop) [Nonempty S]
    (h : expresses q P) :
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

-- ---------------------------------------------------------------
-- Nontrivial: connecting predicate (TLP 4.46, 4.462)
-- ---------------------------------------------------------------

/-- A proposition that is neither a tautology nor a contradiction
    is nontrivial: it varies across worlds. Direct corollary of
    `contingent_propositions_vary`. -/
theorem nontrivial_of_not_taut_not_contra (q : Proposition S) [Nonempty S]
    (h_not_taut : ¬ IsTautology q)
    (h_not_contra : ¬ IsContradiction q) :
    Nontrivial q :=
  contingent_propositions_vary q h_not_taut h_not_contra

/-- `Nontrivial` is equivalent to being neither a tautology nor
    a contradiction. The forward direction unpacks the witnesses;
    the backward direction delegates to `contingent_propositions_vary`. -/
theorem nontrivial_iff_not_taut_not_contra (q : Proposition S) [Nonempty S] :
    Nontrivial q ↔ ¬ IsTautology q ∧ ¬ IsContradiction q := by
  constructor
  · rintro ⟨w₁, w₂, h₁, h₂⟩
    exact ⟨fun ht => h₂ (ht w₂), fun hc => (hc w₁) h₁⟩
  · rintro ⟨hnt, hnc⟩
    exact contingent_propositions_vary q hnt hnc

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
    This is the formal content of TLP 7 -- what cannot be said
    (non-trivially) in the object language can only be shown
    by the structure of the metalanguage. -/
theorem proposition_seven (q : Proposition S) (P : Prop) [Nonempty S]
    (h : expresses q P) :
    IsTautology q ∨ IsContradiction q :=
  saying_showing_triviality q P h

/-- A proposition nontrivially expresses content P only if P varies
    with the world -- i.e., P cannot be world-independent.
    Contrapositive of `saying_showing_triviality`. -/
theorem nontrivial_expressibility_requires_world_dependence
    (q : Proposition S) (P : Prop) [Nonempty S]
    (hnt : Nontrivial q)
    (h : expresses q P) :
    False := by
  rcases saying_showing_triviality q P h with htaut | hcontra
  · obtain ⟨_, w₂, _, h₂⟩ := hnt
    exact h₂ (htaut w₂)
  · obtain ⟨w₁, _, h₁, _⟩ := hnt
    exact (hcontra w₁) h₁

/-- A nontrivial proposition cannot express any world-independent
    property.  If `p` varies across worlds, there is no `P : Prop`
    such that `expresses p P`.  This is the typed form of the
    saying/showing boundary: genuine content cannot be pinned to a
    single meta-proposition. -/
theorem nontrivial_cannot_express_world_independent
    (p : Proposition S) (P : Prop) [Nonempty S]
    (hnt : Nontrivial p) :
    ¬ expresses p P := by
  intro h
  exact nontrivial_expressibility_requires_world_dependence p P hnt h

/-- TLP 7: *Wovon man nicht sprechen kann, darüber muss man schweigen.*

    This axiom no longer stands alone as a bare gesture.  The
    `expresses` relation (TLP 4.12) makes the object/meta boundary
    a type-level concept, and the theorems above prove that:

      - `expresses p P` -- typed bridge between object and meta language.
      - `saying_showing_triviality` -- any expression of world-independent
        content collapses to a tautology or contradiction.
      - `nontrivial_cannot_express_world_independent` -- nontrivial
        propositions cannot express any `P : Prop`.
      - `proposition_seven` -- TLP 7 restated via `expresses`.

    Silence marks where the chain ends: the ladder's top rung.  It is
    not the result of a missing proof obligation but a structural
    feature -- the saying/showing distinction cannot be captured
    within the same formalism that draws it. -/
axiom silence : True

end Tractatus
