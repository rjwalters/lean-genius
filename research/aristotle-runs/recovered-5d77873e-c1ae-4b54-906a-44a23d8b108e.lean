import Mathlib

/-
# Tractatus: N-generation completeness (toward TLP 6) — Aristotle problem file

Companion to https://github.com/rjwalters/tractatus. The development
proves that a SINGLE application of Wittgenstein's N-operator (joint
denial) expresses negation and conjunction. TLP 6 claims more: every
proposition arises from elementary propositions by SUCCESSIVE
applications of N. This file states that claim, up to semantic
equivalence, for the propositional fragment.

`NGen` is the inductive closure of the elementary propositions under
the N-operator. Targets (the `sorry` lemmas):
- `semEq_neg_congr`, `semEq_conj_congr` — semantic equivalence is a
  congruence for the connectives.
- `nGen_complete` — every proposition is semantically equivalent to an
  N-generated one. Hint: induct on the proposition; for `neg p` use
  `NOp q []`; for `conj p r` use `NOp (NOp qp []) [NOp qr []]` and
  `conj_via_NOp` (provided, proved).

Classical logic throughout.
-/

namespace TractatusNGenerationAristotle

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

/-- Semantic equivalence: same truth value in every world. -/
def Proposition.semEq {S : Type} (p q : Proposition S) : Prop :=
  ∀ w : World S, p.eval w ↔ q.eval w

/-- Wittgenstein's N-operator over a nonempty argument list (TLP 5.502). -/
def NOp {S : Type} (p : Proposition S) (ps : List (Proposition S)) :
    Proposition S :=
  ps.foldl (fun acc q => Proposition.conj acc (Proposition.neg q))
    (Proposition.neg p)

/-- Unary N is negation (proved; TLP 5.512). -/
theorem neg_via_NOp {S : Type} (p : Proposition S) (w : World S) :
    (NOp p []).eval w ↔ (Proposition.neg p).eval w := by
  rfl

/-- Conjunction from N alone (proved; TLP 5.5). -/
theorem conj_via_NOp {S : Type} (p q : Proposition S) (w : World S) :
    (NOp (NOp p []) [NOp q []]).eval w ↔
      (Proposition.conj p q).eval w := by
  simp +decide [NOp, Proposition.eval]

-- ════════════════════════════════════════════════════════════════
-- N-generation: the closure of the elementaries under N
-- ════════════════════════════════════════════════════════════════

/-- The propositions reachable from elementary propositions by
    (iterated) applications of the N-operator. -/
inductive NGen {S : Type} : Proposition S → Prop where
  | elem (s : S) : NGen (Proposition.elementary s)
  | nop (p : Proposition S) (ps : List (Proposition S)) :
      NGen p → (∀ q ∈ ps, NGen q) → NGen (NOp p ps)

-- ════════════════════════════════════════════════════════════════
-- TARGETS
-- ════════════════════════════════════════════════════════════════

/-- Semantic equivalence is a congruence for negation. -/
theorem semEq_neg_congr {S : Type} {p q : Proposition S}
    (h : p.semEq q) : (Proposition.neg p).semEq (Proposition.neg q) :=
  fun w => not_congr (h w)

/-- Semantic equivalence is a congruence for conjunction. -/
theorem semEq_conj_congr {S : Type} {p₁ q₁ p₂ q₂ : Proposition S}
    (h₁ : p₁.semEq q₁) (h₂ : p₂.semEq q₂) :
    (Proposition.conj p₁ p₂).semEq (Proposition.conj q₁ q₂) :=
  fun w => and_congr (h₁ w) (h₂ w)

/-- TLP 6 for the propositional fragment, up to semantic equivalence:
    every proposition is semantically equivalent to one generated from
    elementary propositions by iterated N-application. -/
theorem nGen_complete {S : Type} (p : Proposition S) :
    ∃ q : Proposition S, NGen q ∧ q.semEq p := by
  induction p with
  | elementary s =>
      exact ⟨Proposition.elementary s, NGen.elem s, fun w => Iff.rfl⟩
  | neg p ih =>
      obtain ⟨qp, hqp, hsem⟩ := ih
      refine ⟨NOp qp [], NGen.nop qp [] hqp (by simp), fun w => ?_⟩
      rw [neg_via_NOp]
      exact not_congr (hsem w)
  | conj p r ihp ihr =>
      obtain ⟨qp, hqp, hsemp⟩ := ihp
      obtain ⟨qr, hqr, hsemr⟩ := ihr
      refine ⟨NOp (NOp qp []) [NOp qr []], ?_, fun w => ?_⟩
      · refine NGen.nop (NOp qp []) [NOp qr []]
          (NGen.nop qp [] hqp (by simp)) ?_
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact NGen.nop qr [] hqr (by simp)
      · rw [conj_via_NOp]
        exact and_congr (hsemp w) (hsemr w)

end TractatusNGenerationAristotle
