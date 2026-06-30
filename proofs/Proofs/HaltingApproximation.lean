/-
# Approximating the Halting Problem: the Self-Locating Hard Instance

## What This Proves
The classical undecidability theorem (`Proofs.HaltingProblem`) rules out a
*total* halting oracle `H : ℕ → ℕ → Bool`. A natural follow-up — open question
**OQ-01** of the gallery's halting-problem entry, *"What is the computational
complexity of approximating the halting problem?"* — asks what happens when we
relax totality and allow an algorithm to **decline** (give up) on hard inputs.

We model such an *approximator* as a partial Boolean function

  `Approximator := ℕ → ℕ → Option Bool`

where `none` means "I decline / I do not know". The headline result is that the
diagonal argument survives the relaxation in a sharp form:

* **No total approximator is correct at its own diagonal point**
  (`total_approx_errs`) — recovering the classical oracle theorem as the
  always-commit special case (`no_halting_oracle_from_approx`).
* **Every *sound* approximator must decline at its own diagonal point**
  (`sound_approx_declines_on_diagonal`). The gap is not optional: the input on
  which the approximator must give up is *self-locating* — it is the code of the
  diagonal program built from the approximator itself.

This is the precise structural sense in which the halting problem is
"approximable, but only with unavoidable, constructively findable gaps."

## Approach
- **Foundation (from Mathlib):** None. Like `HaltingProblem.lean`, this file uses
  only Lean's built-in `Nat`, `Bool`, and `Option`, plus the classical
  definitions imported from `Proofs.HaltingProblem`. Zero Mathlib dependencies.
- **Original Contributions:** Generalizes the two-valued oracle to a three-valued
  (`true` / `false` / decline) approximator and isolates the diagonal point as the
  forced gap. The "sound approximator must decline at the diagonal" theorem is the
  honest schematic core of approximation hardness.
- **Proof Techniques Demonstrated:** Diagonalization against a partial function,
  case analysis on `Option`, soundness/totality as explicit predicates.

## Scope / Honesty Note
This is the **diagonalization schema** for partial approximators: `Approximator`
is an arbitrary partial Boolean function with *no* computability constraint and
*no* execution model. The theorems therefore formalize the *structural* barrier
(every approximator has a self-locating point where it cannot be correct-and-
committed) rather than a *quantitative* complexity statement. A genuine
computational-complexity answer to OQ-01 — e.g. density/measure of the set on
which halting is approximable, or the position of the "approximation gap" in the
arithmetical hierarchy — requires a model of computation (Mathlib's
`Nat.Partrec` / `ComputablePred`) and is **not** formalized here. See the
companion `knowledge.md` for that assessment.
-/

import Proofs.HaltingProblem

namespace HaltingApproximation

/-- An **approximator** for the halting problem. It may answer `some true`
("halts"), `some false` ("loops"), or `none` ("decline / don't know"). This
generalizes `HaltingOracle = ℕ → ℕ → Bool`, which is forced to commit. -/
def Approximator := Nat → Nat → Option Bool

/-- The diagonal behavior built from an approximator: at input `n`, oppose the
approximator's guess for program `n` on itself, defaulting to `true` when the
approximator declines. This is a genuine total `Behavior : ℕ → Bool`. -/
def diagApprox (A : Approximator) : Nat → Bool :=
  fun n => match A n n with
           | some b => !b
           | none   => true

/-- **Core lemma.** No approximator can *commit* the diagonal value at its own
diagonal point: at every `n`, `A n n` is never equal to `some (diagApprox A n)`.
Either `A` declines (`none`) at `n`, or it commits a value that differs from the
diagonal behavior there. -/
theorem approx_not_commit_diagonal (A : Approximator) (n : Nat) :
    A n n ≠ some (diagApprox A n) := by
  unfold diagApprox
  cases h : A n n with
  | none => simp
  | some b => cases b <;> simp

/-- An approximator is **total** if it always commits (never declines). -/
def Total (A : Approximator) : Prop := ∀ p i, (A p i).isSome = true

/-- An approximator is **sound** with respect to the true behavior `B` if every
committed answer is correct. Declining (`none`) is always allowed. -/
def Sound (A : Approximator) (B : Nat → Nat → Bool) : Prop :=
  ∀ p i v, A p i = some v → v = B p i

/-- **Total approximators err at the diagonal.** A total approximator must give
*some* answer at its diagonal point, and by `approx_not_commit_diagonal` that
answer is wrong: it differs from the diagonal behavior. This is the
approximation-theoretic form of "no total halting decider". -/
theorem total_approx_errs (A : Approximator) (hT : Total A) (n : Nat) :
    ∃ v, A n n = some v ∧ v ≠ diagApprox A n := by
  cases h : A n n with
  | none => exact absurd (hT n n) (by simp [h])
  | some v =>
    refine ⟨v, rfl, ?_⟩
    intro hv
    exact approx_not_commit_diagonal A n (h.trans (by rw [hv]))

/-- **The self-locating hard instance.** Suppose `A` is *sound* for the true
behavior `B`, and `n` is a code that *implements the diagonal behavior* of `A`
(i.e. the true behavior of program `n` on itself equals `diagApprox A n`). Then
`A` is forced to **decline** at `(n, n)`: `A n n = none`.

In words: any sound approximation procedure has a hard input on which it must
give up, and that input is constructible from the procedure itself — the code of
its own diagonal program. -/
theorem sound_approx_declines_on_diagonal
    (A : Approximator) (B : Nat → Nat → Bool) (hS : Sound A B)
    (n : Nat) (hDiag : diagApprox A n = B n n) :
    A n n = none := by
  cases h : A n n with
  | none => rfl
  | some v =>
    have hv : v = B n n := hS n n v h
    rw [← hDiag] at hv
    exact absurd (h.trans (by rw [hv])) (approx_not_commit_diagonal A n)

/-- **Summary barrier.** For every approximator there is a concrete behavior (its
diagonal) on which no code is correctly classified-and-committed. -/
theorem halting_approx_barrier (A : Approximator) :
    ∃ b : Nat → Bool, ∀ code : Nat, A code code ≠ some (b code) :=
  ⟨diagApprox A, fun code => approx_not_commit_diagonal A code⟩

/-! ## The classical oracle is the always-commit special case -/

/-- A total Boolean halting oracle, embedded as the approximator that always
commits. -/
def embedOracle (H : HaltingOracle) : Approximator := fun p i => some (H p i)

/-- The embedded oracle is total. -/
theorem embedOracle_total (H : HaltingOracle) : Total (embedOracle H) := by
  intro p i; simp [embedOracle]

/-- The classical no-halting-oracle result recovered: for the embedded oracle,
the diagonal point is never correctly committed. This is `no_halting_oracle`
viewed through the approximation lens. -/
theorem no_halting_oracle_from_approx (H : HaltingOracle) (c : Nat) :
    embedOracle H c c ≠ some (diagApprox (embedOracle H) c) :=
  approx_not_commit_diagonal (embedOracle H) c

#check @approx_not_commit_diagonal
#check @total_approx_errs
#check @sound_approx_declines_on_diagonal
#check @halting_approx_barrier
#check @no_halting_oracle_from_approx

end HaltingApproximation
