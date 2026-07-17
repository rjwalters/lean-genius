import Proofs.TractatusOntology

/-
# Tractatus functional completeness (TLP 5.101), full strength

The core development proves that {¬, ∧} defines
disjunction/implication/biconditional and that NAND expresses {¬, ∧}.
This file proves the full strength of TLP 5.101: EVERY truth-function
on finitely many atoms is realized by some proposition.

The construction is the disjunctive normal form: for each satisfying
assignment `v`, build the minterm conjoining `elementary s` or
`neg (elementary s)` according to `v s`, then disjoin (via the derived
`disj`) the minterms of all satisfying assignments. `Fintype` and
`DecidableEq` make the assignment space finite and the construction
effective.

Note the `[Nonempty S]` hypothesis on the main theorem: it is genuinely
required. For empty `S` the type `Proposition S` has no inhabitants at
all (every proposition bottoms out in an elementary leaf), while
`(S → Bool) → Bool` still has two elements — so nothing realizes the
constant functions. With at least one atom, constants are realizable as
`p ∨ ¬p` and `p ∧ ¬p`.

`evalBool` (rather than the `Prop`-valued evaluator) keeps the statement
decidable and the induction finitary; `evalBool_correct` (in
`TractatusOntology`) transfers the result to the `Prop`-valued
semantics.

## Attribution

The statement of `functional_completeness` was authored by us (it
sharpens the paper's abstract-level completeness claim). The proof —
including the supporting definitions `literal`, `truePropOf`,
`falsePropOf`, `minterm`, `bigDisj`, `dnf` and their evaluation
lemmas — was produced by Harmonic's Aristotle automated theorem prover
(https://aristotle.harmonic.fun), project
`212b28eb-7cd1-4dcf-b305-390a295a946c`, 2026-07-12, from the sorried
statement; the statement is unchanged from submission. All proofs were
re-verified against this repository's pinned toolchain. Axiom
footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace Tractatus

section Construction

variable {S : Type}

@[simp] lemma Proposition.disj_evalBool (p q : Proposition S) (w : S → Bool) :
    (p.disj q).evalBool w = (p.evalBool w || q.evalBool w) := by
  simp [Proposition.disj, Proposition.evalBool]

/-- The literal for atom `s`: `elementary s` if `b`, else its negation. -/
def Proposition.literal (s : S) (b : Bool) : Proposition S :=
  if b then .elementary s else .neg (.elementary s)

@[simp] lemma Proposition.literal_evalBool (s : S) (b : Bool) (w : S → Bool) :
    (Proposition.literal s b).evalBool w = (w s == b) := by
  cases b <;> simp +decide [ Proposition.literal, Proposition.evalBool ]

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

omit [Fintype S] [DecidableEq S] in
/-- Evaluation of a folded conjunction of literals. -/
lemma conjFold_evalBool (s0 : S) (v w : S → Bool) (L : List S) :
    (List.foldr (fun s acc => (Proposition.literal s (v s)).conj acc)
      (truePropOf s0) L).evalBool w = L.all (fun s => w s == v s) := by
  induction L <;> simp_all +decide [ Proposition.evalBool ]

omit [DecidableEq S] in
/-- The minterm for `v` is true at `w` exactly when `w = v`. -/
lemma minterm_evalBool (s0 : S) (v w : S → Bool) :
    (minterm s0 v).evalBool w = decide (w = v) := by
  have hfold : (minterm s0 v).evalBool w
      = (Finset.univ.toList).all (fun s => w s == v s) :=
    conjFold_evalBool s0 v w (Finset.univ.toList)
  rw [hfold]
  by_cases h : w = v
  · subst h
    simp
  · rw [decide_eq_false h]
    apply Bool.of_not_eq_true
    intro hall
    apply h
    funext s
    have hs : (w s == v s) = true :=
      List.all_eq_true.mp hall s (Finset.mem_toList.mpr (Finset.mem_univ s))
    exact beq_iff_eq.mp hs

/-- Disjunction folded over a list, anchored by an always-false base. -/
def bigDisj (s0 : S) (L : List (Proposition S)) : Proposition S :=
  List.foldr Proposition.disj (falsePropOf s0) L

omit [Fintype S] [DecidableEq S] in
/-- Evaluation of a folded disjunction. -/
lemma bigDisj_evalBool (s0 : S) (L : List (Proposition S)) (w : S → Bool) :
    (bigDisj s0 L).evalBool w = L.any (fun p => p.evalBool w) := by
  induction L <;> simp_all +decide [ bigDisj ]

/-- The disjunctive normal form realizing `g`. -/
noncomputable def dnf (s0 : S) (g : (S → Bool) → Bool) : Proposition S :=
  bigDisj s0 (((Finset.univ.filter (fun v => g v = true)).toList).map (minterm s0))

/-- The DNF construction realizes `g`. -/
lemma dnf_evalBool (s0 : S) (g : (S → Bool) → Bool) (w : S → Bool) :
    (dnf s0 g).evalBool w = g w := by
  unfold dnf;
  rw [ bigDisj_evalBool ];
  simp +decide [ List.any_eq, minterm_evalBool ]

end Construction

-- [MAIN RESULT] --------------------------------------------------
-- functional_completeness (TLP 5.101, full strength)
-- Every truth-function on finitely many atoms is realized by some
-- proposition; Nonempty S is genuinely required.
-- ----------------------------------------------------------------

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

end Tractatus
