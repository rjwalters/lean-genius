import Mathlib

/-
# Tractatus: deciding semantic and formal equivalence — Aristotle problem file

Companion to https://github.com/rjwalters/tractatus. The development
distinguishes semantic equivalence (same truth value in every world,
`Prop`-valued worlds) and logical-form equivalence (atom permutation).
This file makes both decidable over finite atom types, via a bridge to
`Bool`-valued worlds.

Targets (the `sorry` declarations):
- `semEq_iff_evalBool` — semantic equivalence over `Prop`-valued
  worlds coincides with agreement of the `Bool` evaluators on all
  `Bool` assignments. Hint: forward, instantiate at
  `fun s => v s = true` and use `evalBool_correct` (provided, proved);
  backward, for a `Prop` world `w` classically decide each `w s` and
  transfer along compositionality (provided, proved).
- `decideSemEq` — decidability of semantic equivalence for `Fintype`
  atoms (via the bridge; `(S → Bool)` is a `Fintype`).
- `decideFormEq` — decidability of logical-form equivalence for
  `Fintype` atoms (finitely many permutations; `Proposition S` has
  decidable equality).

Classical logic throughout (the bridge itself is classical; the
decision procedures are then honest `Decidable` data).
-/

namespace TractatusDecidabilityAristotle

inductive Proposition (S : Type) where
  | elementary : S → Proposition S
  | neg        : Proposition S → Proposition S
  | conj       : Proposition S → Proposition S → Proposition S
  deriving DecidableEq

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

/-- Atom renaming (connective structure preserved). -/
def Proposition.rename {S : Type} (σ : S → S) : Proposition S → Proposition S
  | .elementary s => .elementary (σ s)
  | .neg p        => .neg (p.rename σ)
  | .conj p q     => .conj (p.rename σ) (q.rename σ)

/-
════════════════════════════════════════════════════════════════
TARGETS
════════════════════════════════════════════════════════════════

Semantic equivalence over `Prop`-valued worlds coincides with
    `Bool`-evaluator agreement on all `Bool` assignments.  Holds for
    arbitrary `S` (classically).
-/
theorem semEq_iff_evalBool {S : Type} (p q : Proposition S) :
    (∀ w : World S, p.eval w ↔ q.eval w) ↔
    (∀ v : S → Bool, p.evalBool v = q.evalBool v) := by
  classical
  constructor
  · intro h v
    have hw := h (fun s => v s = true)
    rw [← Proposition.evalBool_correct p v, ← Proposition.evalBool_correct q v] at hw
    cases hp : p.evalBool v <;> cases hq : q.evalBool v <;> simp_all
  · intro h w
    set v : S → Bool := fun s => decide (w s) with hv
    have hbridge : ∀ s : S, w s ↔ (v s = true) := by
      intro s; simp [hv]
    rw [truth_functional_compositionality p w (fun s => v s = true) hbridge,
        truth_functional_compositionality q w (fun s => v s = true) hbridge,
        ← Proposition.evalBool_correct p v, ← Proposition.evalBool_correct q v, h v]

/-
Semantic equivalence is decidable over finite atom types.
-/
def decideSemEq {S : Type} [Fintype S] [DecidableEq S]
    (p q : Proposition S) :
    Decidable (∀ w : World S, p.eval w ↔ q.eval w) :=
  decidable_of_iff _ (semEq_iff_evalBool p q).symm

/-
Logical-form equivalence (existence of an atom permutation carrying
    `p` to `q`) is decidable over finite atom types.
-/
def decideFormEq {S : Type} [Fintype S] [DecidableEq S]
    (p q : Proposition S) :
    Decidable (∃ e : Equiv.Perm S, p.rename e = q) :=
  Fintype.decidableExistsFintype

end TractatusDecidabilityAristotle