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

## Scope (S4 ACT-C, researcher-1, 2026-05-12)
Single-session deliverable. Zero new axioms, zero new sorries, zero imports
beyond the two existing zero-import files. ~50 lines of pure embedding
arithmetic + a one-line corollary.

## Why This Is Not Enumeration Theater
The iterated-jump framework in PR #18003 (S3 ACT-B) extends
`Proofs.RelativizedHalting` "upward" (to A', A'', …). This file extends
*downward*: it witnesses the trivial-oracle specialization back to the
parent's already-formalized classical statement. The bridge is small
(≤50 lines) and orthogonal to S3's content; it eliminates a documentation
gap rather than adding new mathematical depth.

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

#check embedClassical
#check specialize
#check specialize_embedClassical
#check specialize_embedClassical_trivial
#check relativizedDiagonal_eq_classicalDiagonal_of_specialize
#check relativizedDiagonal_eq_classicalDiagonal_funext
#check halting_problem_undecidable_from_relativized

end RelativizedHaltingBridge
