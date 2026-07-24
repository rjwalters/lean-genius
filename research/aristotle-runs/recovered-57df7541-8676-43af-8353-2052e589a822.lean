import Mathlib

/-
# Tractatus: the totality of facts is inexpressible — Aristotle problem file

Companion to https://github.com/rjwalters/tractatus. TLP 1: "The world
is everything that is the case."  This file proves that, over an
infinite atom type, the world-property "everything is the case"
(`fun w => ∀ s, w s`) is invariant under pointwise-iff agreement of
worlds yet is NOT expressible by any proposition — although over
finite atom types every invariant property is expressible (proved in a
companion file). The obstruction is finite support: a proposition's
truth value depends only on its finitely many atoms.

Targets (the `sorry` lemmas):
- `eval_depends_only_on_atoms` — finite support: worlds agreeing on
  `p.atoms` agree on `p`. Hint: structural induction.
- `totality_not_expressible` — no proposition expresses
  `fun w => ∀ s, w s` when `S` is infinite. Hint: if `p` expressed it,
  compare the all-true world with the world true exactly on `p.atoms`
  (they agree on `p.atoms`, but an infinite type has an element outside
  that finite list, so totality holds at the first and fails at the
  second).
-/

namespace TractatusTotalityAristotle

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

/-- The (finitely many) atoms occurring in a proposition. -/
def Proposition.atoms {S : Type} : Proposition S → List S
  | .elementary s => [s]
  | .neg q        => q.atoms
  | .conj q r     => q.atoms ++ r.atoms

/-
════════════════════════════════════════════════════════════════
TARGETS
════════════════════════════════════════════════════════════════

Finite support: a proposition's truth value depends only on its
    atoms.
-/
theorem eval_depends_only_on_atoms {S : Type} (p : Proposition S)
    (w₁ w₂ : World S) (h : ∀ s ∈ p.atoms, w₁ s ↔ w₂ s) :
    p.eval w₁ ↔ p.eval w₂ := by
  -- We proceed by induction on $p$.
  induction' p with s p₁ p₂ ih₁ ih₂;
  · exact h s ( by tauto );
  · exact not_iff_not.mpr ( p₂ h );
  · simp_all +decide [ Proposition.eval, Proposition.atoms ]

/-
TLP 1 cannot be said: over an infinite atom type, no proposition
    expresses the totality property "everything is the case" --- even
    though that property is invariant under pointwise-iff agreement of
    worlds.
-/
theorem totality_not_expressible {S : Type} [Infinite S] :
    ¬ ∃ p : Proposition S, ∀ w : World S, p.eval w ↔ (∀ s, w s) := by
  by_contra! h_contra;
  obtain ⟨ p, hp ⟩ := h_contra;
  have h_support : ∀ s, s ∈ p.atoms := by
    convert eval_depends_only_on_atoms p ( fun _ => True ) ( fun s => s ∈ p.atoms ) _ using 1; all_goals aesop;
  exact absurd ( List.finite_toSet p.atoms ) ( Set.infinite_univ.mono fun x _ => h_support x )

end TractatusTotalityAristotle