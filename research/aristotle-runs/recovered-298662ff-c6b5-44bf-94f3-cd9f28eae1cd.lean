import Mathlib

/-
# Tractatus: exact characterization of the expressible — Aristotle problem file

Companion to https://github.com/rjwalters/tractatus. The paper's collapse
theorem says which meta-level contents propositions CANNOT express
(world-independent `P : Prop`). This file states the positive
complement: over a finite, decidable, nonempty atom type, a
world-dependent property `P : World S → Prop` is expressible by a
proposition IFF `P` is invariant under pointwise-iff agreement of
worlds.

Target: `expressible_iff_iff_invariant` (the last `sorry`).
Forward direction: truth-functional compositionality (provided, proved).
Backward direction hint: given invariant `P`, pass to Bool worlds
(classically decide `w s`), realize `fun v => decide (P (fun s => v s = true))`
by `functional_completeness` (provided, proved), and transfer back
along `evalBool_correct` (provided, proved) and compositionality.

All support lemmas below are already proved; only the final theorem is
a `sorry`. Classical logic throughout.
-/

namespace TractatusExpressibilityAristotle

inductive Proposition (S : Type) where
  | elementary : S → Proposition S
  | neg        : Proposition S → Proposition S
  | conj       : Proposition S → Proposition S → Proposition S

def World (S : Type) := S → Prop

def Proposition.eval {S : Type} (p : Proposition S) (w : World S) : Prop :=
  match p with
  | .elementary s => w s
  | .neg q        => ¬ (q.eval w)
  | .conj q r     => q.eval w ∧ r.eval w

def Proposition.evalBool {S : Type} (p : Proposition S) (w : S → Bool) : Bool :=
  match p with
  | .elementary s => w s
  | .neg q        => !(q.evalBool w)
  | .conj q r     => q.evalBool w && r.evalBool w

theorem Proposition.evalBool_correct {S : Type} (p : Proposition S) (w : S → Bool) :
    (p.evalBool w = true) ↔ p.eval (fun s => w s = true) := by
  induction p with
  | elementary s => simp [evalBool, eval]
  | neg q ih     =>
    show (!q.evalBool w) = true ↔ ¬ q.eval (fun s => w s = true)
    have h1 : (!q.evalBool w) = true ↔ q.evalBool w = false := by
      cases q.evalBool w <;> simp
    have h2 : q.evalBool w = false ↔ ¬ q.evalBool w = true := by
      cases q.evalBool w <;> simp
    rw [h1, h2, ih]
  | conj q r ihq ihr => simp [evalBool, eval, Bool.and_eq_true, ihq, ihr]

theorem truth_functional_compositionality {S : Type} (p : Proposition S)
    (w₁ w₂ : World S) (h : ∀ s : S, w₁ s ↔ w₂ s) :
    p.eval w₁ ↔ p.eval w₂ := by
  induction p with
  | elementary s => exact h s
  | neg q ih => simp only [Proposition.eval]; exact ih.not
  | conj q r ihq ihr => simp only [Proposition.eval]; exact ihq.and ihr

section Construction

variable {S : Type}

def Proposition.disj (p q : Proposition S) : Proposition S :=
  .neg (.conj (.neg p) (.neg q))

@[simp] lemma Proposition.disj_evalBool (p q : Proposition S) (w : S → Bool) :
    (p.disj q).evalBool w = (p.evalBool w || q.evalBool w) := by
  simp [Proposition.disj, Proposition.evalBool]

def Proposition.literal (s : S) (b : Bool) : Proposition S :=
  if b then .elementary s else .neg (.elementary s)

@[simp] lemma Proposition.literal_evalBool (s : S) (b : Bool) (w : S → Bool) :
    (Proposition.literal s b).evalBool w = (w s == b) := by
  cases b <;> simp +decide [ Proposition.literal, Proposition.evalBool ]

def truePropOf (s : S) : Proposition S :=
  (Proposition.elementary s).disj (.neg (.elementary s))

def falsePropOf (s : S) : Proposition S :=
  (Proposition.elementary s).conj (.neg (.elementary s))

@[simp] lemma truePropOf_evalBool (s : S) (w : S → Bool) :
    (truePropOf s).evalBool w = true := by
  cases w s <;> simp_all +decide [ truePropOf ]; all_goals cases w s <;> simp +decide [ *, Proposition.evalBool ]

@[simp] lemma falsePropOf_evalBool (s : S) (w : S → Bool) :
    (falsePropOf s).evalBool w = false := by
  cases w s <;> simp +decide [ *, falsePropOf ]; all_goals simp +decide [ Proposition.evalBool ]

variable [Fintype S] [DecidableEq S]

noncomputable def minterm (s0 : S) (v : S → Bool) : Proposition S :=
  List.foldr (fun s acc => (Proposition.literal s (v s)).conj acc)
    (truePropOf s0) (Finset.univ.toList)

omit [Fintype S] [DecidableEq S] in
lemma conjFold_evalBool (s0 : S) (v w : S → Bool) (L : List S) :
    (List.foldr (fun s acc => (Proposition.literal s (v s)).conj acc)
      (truePropOf s0) L).evalBool w = L.all (fun s => w s == v s) := by
  induction L <;> simp_all +decide [ Proposition.evalBool ]

omit [DecidableEq S] in
lemma minterm_evalBool (s0 : S) (v w : S → Bool) :
    (minterm s0 v).evalBool w = decide (w = v) := by
  have := @conjFold_evalBool;
  convert this s0 v w ( Finset.univ.toList ) using 1;
  by_cases h : w = v <;> simp +decide [ h ];
  exact Function.ne_iff.mp h

def bigDisj (s0 : S) (L : List (Proposition S)) : Proposition S :=
  List.foldr Proposition.disj (falsePropOf s0) L

omit [Fintype S] [DecidableEq S] in
lemma bigDisj_evalBool (s0 : S) (L : List (Proposition S)) (w : S → Bool) :
    (bigDisj s0 L).evalBool w = L.any (fun p => p.evalBool w) := by
  induction L <;> simp_all +decide [ bigDisj ]

noncomputable def dnf (s0 : S) (g : (S → Bool) → Bool) : Proposition S :=
  bigDisj s0 (((Finset.univ.filter (fun v => g v = true)).toList).map (minterm s0))

lemma dnf_evalBool (s0 : S) (g : (S → Bool) → Bool) (w : S → Bool) :
    (dnf s0 g).evalBool w = g w := by
  unfold dnf;
  rw [ bigDisj_evalBool ];
  simp +decide [ List.any_eq, minterm_evalBool ]

end Construction

theorem functional_completeness {S : Type} [Fintype S] [DecidableEq S]
    [Nonempty S] (g : (S → Bool) → Bool) :
    ∃ p : Proposition S, ∀ w : S → Bool, p.evalBool w = g w := by
  refine ⟨dnf (Classical.arbitrary S) g, ?_⟩
  intro w
  exact dnf_evalBool (Classical.arbitrary S) g w

/-
════════════════════════════════════════════════════════════════
TARGET: exact characterization of expressibility
════════════════════════════════════════════════════════════════

Over a finite, decidable, nonempty atom type, a world property
    `P : World S → Prop` is expressible by some proposition iff `P` is
    invariant under pointwise-iff agreement of worlds.
-/
theorem expressible_iff_iff_invariant {S : Type} [Fintype S] [DecidableEq S]
    [Nonempty S] (P : World S → Prop) :
    (∃ p : Proposition S, ∀ w : World S, p.eval w ↔ P w) ↔
    (∀ w₁ w₂ : World S, (∀ s, w₁ s ↔ w₂ s) → (P w₁ ↔ P w₂)) := by
  constructor;
  · grind +suggestions;
  · intro h_invariant
    obtain ⟨p, hp⟩ : ∃ p : Proposition S, ∀ w : S → Bool, p.evalBool w = (P (fun s => w s = true)) := by
      convert functional_completeness ( fun w => decide ( P fun s => w s = true ) ) using 1;
      grind;
      exact fun w => Classical.propDecidable _;
    use p;
    intro w;
    convert hp ( fun s => decide ( w s ) ) using 1;
    grind;
    convert Proposition.evalBool_correct p ( fun s => decide ( w s ) ) |> Iff.symm;
    grind;
    exact fun s => Classical.propDecidable _;
    grind +suggestions

end TractatusExpressibilityAristotle