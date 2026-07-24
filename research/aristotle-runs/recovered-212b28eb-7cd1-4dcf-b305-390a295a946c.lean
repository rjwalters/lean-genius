import Mathlib

/-
# Tractatus functional completeness (TLP 5.101) — Aristotle problem file

Companion to the machine-checked Tractatus formalization at
https://github.com/rjwalters/tractatus. The source development proves
that {¬, ∧} defines disjunction/implication/biconditional and that NAND
expresses {¬, ∧}. This file states the full strength of TLP 5.101 —
EVERY truth-function on finitely many atoms is realized by some
proposition — which the source development does not yet contain.

Target: `functional_completeness`. The expected construction is the
disjunctive normal form: for each satisfying assignment `v`, build the
minterm conjoining `elementary s` or `neg (elementary s)` according to
`v s`, then disjoin (via De Morgan: `disj p q = neg (conj (neg p)
(neg q))`) the minterms of all satisfying assignments. `Fintype` and
`DecidableEq` make the assignment space finite and the construction
effective.

Note the `[Nonempty S]` hypothesis: it is genuinely required. For empty
`S` the type `Proposition S` has no inhabitants at all (every
proposition bottoms out in an elementary leaf), while `(S → Bool) → Bool`
still has two elements — so there is nothing to realize the constant
functions with. With at least one atom, constants are realizable as
`p ∨ ¬p` and `p ∧ ¬p`.

`evalBool` (rather than the `Prop`-valued evaluator) keeps the statement
decidable and the induction finitary.

All definitions are inlined so the file depends only on Mathlib.
-/

namespace TractatusFunctionalCompletenessAristotle

/-- Truth-functional propositions over atoms `S` (TLP 4.21, 5). -/
inductive Proposition (S : Type) where
  | elementary : S → Proposition S
  | neg        : Proposition S → Proposition S
  | conj       : Proposition S → Proposition S → Proposition S

/-- Bool-valued evaluation against a Bool-valued world. -/
def Proposition.evalBool {S : Type} (p : Proposition S) (w : S → Bool) :
    Bool :=
  match p with
  | .elementary s => w s
  | .neg q        => !(q.evalBool w)
  | .conj q r     => q.evalBool w && r.evalBool w

section Construction

variable {S : Type}

/-- Disjunction defined from `neg`/`conj` by De Morgan. -/
def Proposition.disj (p q : Proposition S) : Proposition S :=
  .neg (.conj (.neg p) (.neg q))

@[simp] lemma Proposition.disj_evalBool (p q : Proposition S) (w : S → Bool) :
    (p.disj q).evalBool w = (p.evalBool w || q.evalBool w) := by
  simp [Proposition.disj, Proposition.evalBool]

/-- The literal for atom `s`: `elementary s` if `b`, else its negation. -/
def Proposition.literal (s : S) (b : Bool) : Proposition S :=
  if b then .elementary s else .neg (.elementary s)

@[simp] lemma Proposition.literal_evalBool (s : S) (b : Bool) (w : S → Bool) :
    (Proposition.literal s b).evalBool w = (w s == b) := by
  cases b <;> simp +decide [ literal, Proposition.evalBool ]

/-- An always-true proposition built from a designated atom `s`. -/
def truePropOf (s : S) : Proposition S :=
  (Proposition.elementary s).disj (.neg (.elementary s))

/-- An always-false proposition built from a designated atom `s`. -/
def falsePropOf (s : S) : Proposition S :=
  (Proposition.elementary s).conj (.neg (.elementary s))

@[simp] lemma truePropOf_evalBool (s : S) (w : S → Bool) :
    (truePropOf s).evalBool w = true := by
  cases w s <;> simp_all +decide [ truePropOf ]; all_goals cases w s <;> simp +decide [ *, Proposition.evalBool ]

@[simp] lemma falsePropOf_evalBool (s : S) (w : S → Bool) :
    (falsePropOf s).evalBool w = false := by
  cases w s <;> simp +decide [ *, falsePropOf ]; all_goals simp +decide [ Proposition.evalBool ]

variable [Fintype S] [DecidableEq S]

/-- The minterm for target world `v`: conjoin the literals of every atom
    (as required by `v`), anchored by an always-true base. -/
noncomputable def minterm (s0 : S) (v : S → Bool) : Proposition S :=
  List.foldr (fun s acc => (Proposition.literal s (v s)).conj acc)
    (truePropOf s0) (Finset.univ.toList)

/-
Evaluation of a folded conjunction of literals.
-/
omit [Fintype S] [DecidableEq S] in
lemma conjFold_evalBool (s0 : S) (v w : S → Bool) (L : List S) :
    (List.foldr (fun s acc => (Proposition.literal s (v s)).conj acc)
      (truePropOf s0) L).evalBool w = L.all (fun s => w s == v s) := by
  induction L <;> simp_all +decide [ Proposition.evalBool ]

/-
The minterm for `v` is true at `w` exactly when `w = v`.
-/
omit [DecidableEq S] in
lemma minterm_evalBool (s0 : S) (v w : S → Bool) :
    (minterm s0 v).evalBool w = decide (w = v) := by
  have := @conjFold_evalBool;
  convert this s0 v w ( Finset.univ.toList ) using 1;
  by_cases h : w = v <;> simp +decide [ h ];
  exact Function.ne_iff.mp h

/-- Disjunction folded over a list, anchored by an always-false base. -/
def bigDisj (s0 : S) (L : List (Proposition S)) : Proposition S :=
  List.foldr Proposition.disj (falsePropOf s0) L

/-
Evaluation of a folded disjunction.
-/
omit [Fintype S] [DecidableEq S] in
lemma bigDisj_evalBool (s0 : S) (L : List (Proposition S)) (w : S → Bool) :
    (bigDisj s0 L).evalBool w = L.any (fun p => p.evalBool w) := by
  induction L <;> simp_all +decide [ bigDisj ]

/-- The disjunctive normal form realizing `g`. -/
noncomputable def dnf (s0 : S) (g : (S → Bool) → Bool) : Proposition S :=
  bigDisj s0 (((Finset.univ.filter (fun v => g v = true)).toList).map (minterm s0))

/-
The DNF construction realizes `g`.
-/
lemma dnf_evalBool (s0 : S) (g : (S → Bool) → Bool) (w : S → Bool) :
    (dnf s0 g).evalBool w = g w := by
  unfold dnf;
  rw [ bigDisj_evalBool ];
  simp +decide [ List.any_eq, minterm_evalBool ]

end Construction

/-- TLP 5.101, full strength: every truth-function of the elementary
    propositions is the truth-function of some proposition. For a finite,
    decidable, nonempty atom type `S`, every `g : (S → Bool) → Bool` is
    realized by some `p : Proposition S`. -/
theorem functional_completeness {S : Type} [Fintype S] [DecidableEq S]
    [Nonempty S] (g : (S → Bool) → Bool) :
    ∃ p : Proposition S, ∀ w : S → Bool, p.evalBool w = g w := by
  refine ⟨dnf (Classical.arbitrary S) g, ?_⟩
  intro w
  exact dnf_evalBool (Classical.arbitrary S) g w

end TractatusFunctionalCompletenessAristotle