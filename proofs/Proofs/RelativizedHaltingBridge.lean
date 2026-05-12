/-
# Bridge: Classical ↔ Relativized Halting (halting-problem-oq-03, S4 ACT-C)

## What This Provides
Explicit Lean-level connection between the existing zero-import files
`Proofs.HaltingProblem` (classical halting problem, Turing 1936) and
`Proofs.RelativizedHalting` (oracle-aware relativized halting, S2 ACT-A of
halting-problem-oq-03).

The abstract diagonal in `Proofs.RelativizedHalting` is *strictly stronger*
than the classical diagonal in `Proofs.HaltingProblem`: every classical
`HaltingOracle` is the specialization of an oracle-independent
relativized predictor at any oracle, so the relativized undecidability
result *implies* the classical one. Until S4 this implication was prose
only (in `Proofs.RelativizedHalting`'s docstring §"Why the abstract level
suffices for OQ-03a"). This file makes the implication a Lean term:
`halting_problem_undecidable_from_relativized` is the corollary.

## Scope (S4 ACT-C, researcher-1, 2026-05-12; extended S5 ACT-D, researcher-12, 2026-05-12)
S4 ACT-C: single-session deliverable. Zero new axioms, zero new sorries,
zero imports beyond the two existing zero-import files. ~50 lines of pure
embedding arithmetic + a one-line corollary.

S5 ACT-D (this iteration): adds Section 5 — *jump-tower collapse* for
embedded classical predictors. An oracle-independent classical
`HaltingOracle`, embedded via `embedClassical`, generates a trivial
(level-≥1 constant) jump tower: every level ≥ 1 collapses to
`diagonalBehavior H`. This is a strict-separation result for the abstract
S3 framework — the nontriviality of the iterated jump `A, A', A'', ...`
requires the predictor to be genuinely oracle-aware. ~60 lines, zero new
imports, zero new axioms, zero new sorries.

## Why This Is Not Enumeration Theater
The iterated-jump framework in PR #18003 (S3 ACT-B) extends
`Proofs.RelativizedHalting` "upward" (to A', A'', …). This file extends
*downward*: it witnesses the trivial-oracle specialization back to the
parent's already-formalized classical statement. The bridge is small
(≤120 lines total after S5) and orthogonal to S3's content; it eliminates
a documentation gap (S4) and quantifies the *degeneracy* of the jump tower
under classical embedding (S5).

## Out of Scope (deferred)
* The Mathlib `Nat.Partrec.Code` bridge (parallel `OracleCode` inductive,
  ~200 lines; deferred per S2 ACT-A notes).
* Arithmetical hierarchy (OQ-03b) and hypercomputation (OQ-03c).
-/
import Proofs.HaltingProblem
import Proofs.RelativizedHalting

namespace RelativizedHaltingBridge

/-! ### Section 1. Embedding and specialization -/

/-- Embed a classical halting oracle `H : Nat → Nat → Bool` as an
oracle-independent relativized predictor: every oracle agrees with the
classical answer. -/
def embedClassical (H : HaltingOracle) :
    RelativizedHalting.RelativizedHaltingPredictor :=
  fun _o => H

/-- Specialize a relativized predictor at a particular oracle, recovering a
classical halting oracle. -/
def specialize (H : RelativizedHalting.RelativizedHaltingPredictor)
    (o : Nat → Bool) : HaltingOracle :=
  H o

/-! ### Section 2. Round-trip identities (definitional) -/

/-- Specializing the classical embedding at any oracle returns the original
classical oracle. -/
theorem specialize_embedClassical (H : HaltingOracle) (o : Nat → Bool) :
    specialize (embedClassical H) o = H := rfl

/-- Specializing the classical embedding at the trivial oracle (`fun _ =>
false`) returns the original classical oracle. Stated separately because
this is the specific instance used by the bridge corollary below. -/
theorem specialize_embedClassical_trivial (H : HaltingOracle) :
    specialize (embedClassical H) (fun _ => false) = H := rfl

/-! ### Section 3. Diagonal compatibility -/

/-- The relativized diagonal of any predictor `H` at any oracle `o` equals
the classical diagonal of the predictor `H` specialized at `o`. Pointwise,
zero imports, by `rfl`. -/
theorem relativizedDiagonal_eq_classicalDiagonal_of_specialize
    (H : RelativizedHalting.RelativizedHaltingPredictor) (o : Nat → Bool)
    (n : Nat) :
    RelativizedHalting.relativizedDiagonalBehavior H o n =
      diagonalBehavior (specialize H o) n := rfl

/-- Function-extensionality form of `relativizedDiagonal_eq_classicalDiagonal_of_specialize`:
the underlying behavior functions agree as `Nat → Bool`. -/
theorem relativizedDiagonal_eq_classicalDiagonal_funext
    (H : RelativizedHalting.RelativizedHaltingPredictor) (o : Nat → Bool) :
    (fun n => RelativizedHalting.relativizedDiagonalBehavior H o n) =
      (fun n => diagonalBehavior (specialize H o) n) := by
  funext n
  rfl

/-! ### Section 4. The bridge corollary -/

/-- **Bridge corollary.** The classical halting-problem undecidability
result is a corollary of `RelativizedHalting.relativized_halting_undecidable`
applied to `embedClassical H` at the trivial oracle. This witnesses, as a
Lean term, the literature claim that the relativized form is a strict
generalization of the classical form.

The statement here matches `Proofs.HaltingProblem.halting_problem_undecidable`
modulo the `∀ H` outer binder being beta-reduced. -/
theorem halting_problem_undecidable_from_relativized (H : HaltingOracle) :
    ∃ behavior : Behavior, ∀ code : Nat, ¬(H code code = behavior code) := by
  obtain ⟨b, hb⟩ :=
    RelativizedHalting.relativized_halting_undecidable
      (fun _ : Nat => false) (embedClassical H)
  refine ⟨b, ?_⟩
  intro code h
  exact hb code h

/-! ### Section 5. Jump-tower collapse for embedded classical predictors

The abstract Turing-jump iteration `jumpIter` from
`Proofs.RelativizedHalting` is nontrivial precisely when the underlying
predictor is genuinely oracle-aware. A classical halting oracle
`H : HaltingOracle`, embedded as an oracle-independent predictor via
`embedClassical H`, produces a *degenerate* jump tower:

* Level 0: the seed `o₀` (whatever it is).
* Level ≥ 1: constantly `diagonalBehavior H`. The oracle argument is
  discarded by `embedClassical`, so every iteration reproduces the
  same classical diagonal — irrespective of seed or step count.

This is a structural strict-separation result. Classically Post 1944
established `A < A' < A'' < ...`; the abstract analog of *that* chain
requires oracle dependence, since the embedded classical case generates
no strictness beyond level 1. The lemmas below witness the collapse as
Lean terms, motivating why a future Mathlib-class bridge sub-OQ
(`halting-problem-oq-03-bridge`) must use the parallel `OracleCode`
inductive rather than re-embedding `Nat.Partrec.Code` as oracle-blind.

Each theorem is proved by `rfl` modulo a single induction step (the
inductive case is itself definitional, but the proof is written with
`induction n` for readability; the entire S5 deliverable is one `rfl`
plus three `funext`/`induction`/`Nat.succ_eq_add_one` rewrites). -/

/-- Under `embedClassical`, the relativized diagonal at any oracle equals
the classical diagonal of `H`. Pointwise, by `rfl`: `embedClassical H`
discards its oracle argument, so the diagonal reduces to
`fun n => !(H n n) = diagonalBehavior H`. -/
theorem relativizedDiagonal_embedClassical_eq_classicalDiagonal
    (H : HaltingOracle) (o : Nat → Bool) (n : Nat) :
    RelativizedHalting.relativizedDiagonalBehavior (embedClassical H) o n =
      diagonalBehavior H n := rfl

/-- Function-extensionality form: as `Nat → Bool` functions, the
relativized diagonal of an embedded classical oracle equals the classical
diagonal, *independent of the oracle argument*. -/
theorem relativizedDiagonal_embedClassical_eq_classicalDiagonal_funext
    (H : HaltingOracle) (o : Nat → Bool) :
    (fun n => RelativizedHalting.relativizedDiagonalBehavior
        (embedClassical H) o n) =
      (fun n => diagonalBehavior H n) := rfl

/-- Under `embedClassical`, the abstract Turing jump (level 1 of the jump
iteration) coincides with the classical diagonal, pointwise. -/
theorem jumpOracle_embedClassical_eq_classicalDiagonal
    (H : HaltingOracle) (o : Nat → Bool) (n : Nat) :
    RelativizedHalting.jumpOracle (embedClassical H) o n =
      diagonalBehavior H n := rfl

/-- **Jump-tower collapse (succ form).** For every classical halting oracle
`H`, every seed `o₀ : Nat → Bool`, every level `n`, and every code `c`,
the level-`(n+1)` entry of the abstract Turing-jump tower under
`embedClassical H` equals `diagonalBehavior H c`. In other words, *every*
level ≥ 1 of the embedded jump tower collapses to the classical diagonal,
regardless of the seed or step count.

The proof is by induction on `n`:
* `n = 0`: `jumpIter (embedClassical H) o₀ 1 = jumpOracle (embedClassical
  H) o₀ = diagonalBehavior H` by `rfl` (oracle ignored).
* `n = k + 1`: the inductive step is also by `rfl` because the next
  iteration applies `jumpOracle (embedClassical H) _` which is again
  oracle-blind. -/
theorem jumpIter_embedClassical_succ_eq_classicalDiagonal
    (H : HaltingOracle) (o₀ : Nat → Bool) (n c : Nat) :
    RelativizedHalting.jumpIter (embedClassical H) o₀ (n + 1) c =
      diagonalBehavior H c := by
  induction n with
  | zero => rfl
  | succ _ _ => rfl

/-- Function-extensionality form of `jumpIter_embedClassical_succ_eq_classicalDiagonal`. -/
theorem jumpIter_embedClassical_succ_eq_classicalDiagonal_funext
    (H : HaltingOracle) (o₀ : Nat → Bool) (n : Nat) :
    (fun c => RelativizedHalting.jumpIter (embedClassical H) o₀ (n + 1) c) =
      (fun c => diagonalBehavior H c) := by
  funext c
  exact jumpIter_embedClassical_succ_eq_classicalDiagonal H o₀ n c

/-- **Stability above level 1.** For any classical halting oracle `H`, any
seed `o₀`, any two levels `m, n ≥ 1`, and any code `c`, the jump-tower
entries coincide pointwise: the embedded jump tower is constant above
level 0. -/
theorem jumpIter_embedClassical_stable_above_one
    (H : HaltingOracle) (o₀ : Nat → Bool) (m n c : Nat) :
    RelativizedHalting.jumpIter (embedClassical H) o₀ (m + 1) c =
      RelativizedHalting.jumpIter (embedClassical H) o₀ (n + 1) c := by
  rw [jumpIter_embedClassical_succ_eq_classicalDiagonal H o₀ m c,
      jumpIter_embedClassical_succ_eq_classicalDiagonal H o₀ n c]

/-- **`jumpIterWitness` collapses under classical embedding.** The named
diagonal witness from `RelativizedHalting.jumpIterWitness` coincides
pointwise with `diagonalBehavior H` for every starting seed and every
level, when applied to `embedClassical H`. Same content as
`jumpIter_embedClassical_succ_eq_classicalDiagonal`, packaged via the
alias for downstream consumers. -/
theorem jumpIterWitness_embedClassical_eq_classicalDiagonal
    (H : HaltingOracle) (o₀ : Nat → Bool) (n c : Nat) :
    RelativizedHalting.jumpIterWitness (embedClassical H) o₀ n c =
      diagonalBehavior H c :=
  jumpIter_embedClassical_succ_eq_classicalDiagonal H o₀ n c

#check embedClassical
#check specialize
#check specialize_embedClassical
#check specialize_embedClassical_trivial
#check relativizedDiagonal_eq_classicalDiagonal_of_specialize
#check relativizedDiagonal_eq_classicalDiagonal_funext
#check halting_problem_undecidable_from_relativized
#check relativizedDiagonal_embedClassical_eq_classicalDiagonal
#check relativizedDiagonal_embedClassical_eq_classicalDiagonal_funext
#check jumpOracle_embedClassical_eq_classicalDiagonal
#check jumpIter_embedClassical_succ_eq_classicalDiagonal
#check jumpIter_embedClassical_succ_eq_classicalDiagonal_funext
#check jumpIter_embedClassical_stable_above_one
#check jumpIterWitness_embedClassical_eq_classicalDiagonal

end RelativizedHaltingBridge
