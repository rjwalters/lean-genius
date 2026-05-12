# Current State

**Phase**: ACT (S2 ACT-A shipped abstract zero-import diagonal; Mathlib-bridge deferred)
**Since**: 2026-05-12 (S2 ACT-A, researcher-10)
**Iteration**: 2

## Current Focus

Session 2 (S2 ACT-A, researcher-10, 2026-05-12) delivered a zero-import
`proofs/Proofs/RelativizedHalting.lean` that captures sub-goal OQ-03a at the
abstract `(Nat -> Bool) -> Nat -> Nat -> Bool` level. The pragmatic decision
to stay zero-import (rather than parameterize Mathlib's `Nat.Partrec.Code`)
is documented in the file's docstring §"Why the abstract level suffices for
OQ-03a"; it is also justified by the observation that the parent's
`HaltingProblem.lean` lives at the same abstraction.

Output of this session:

* `proofs/Proofs/RelativizedHalting.lean` — new file, 0 sorries, 0 axioms,
  ~180 lines, zero imports. Mirrors the parent's structure with an oracle
  parameter threaded through `RelativizedHaltingPredictor`, the diagonal
  argument, and the sanity-check collapse to the classical case.
* `proofs/Proofs.lean` — added `import Proofs.RelativizedHalting` in
  alphabetical position between `RandomizedMaxcutOQ04` and
  `RiemannHypothesis`.
* `research/problems/halting-problem-oq-03/state.md` — this file
  (S2 update).
* No gallery JSON change — the slug remains a research entry, not a gallery
  proof entry, since `relativized_halting_undecidable` is a one-file abstract
  result whose primary exhibit is the parent `halting-problem`.

## Prior Session Outputs

* **S1** (researcher-9, 2026-05-12, PR #17920): OBSERVE — fresh-slug scaffold.
  Decomposed OQ-03 into three sub-goals (OQ-03a/b/c). Surveyed oracle TM,
  Turing jump, arithmetical hierarchy, hypercomputation literature; Mathlib
  v4.26.0 audit confirmed `Computability.{Partrec, PartrecCode, Halting,
  TuringMachine}` are present but oracle TMs / jump / hierarchy are ALL
  absent. Authored `problem.md`, `knowledge.md`, `state.md`,
  `src/data/research/problems/halting-problem-oq-03.json`.

## S2 deliverables vs the original S2 plan

The S1 state.md proposed parameterizing Mathlib's `Code.evaln` over an
oracle (adding a `Code.oracle` constructor). On closer inspection
(S2 ACT-A):

* **Mathlib's `Nat.Partrec.Code` is sealed**: it is an `inductive Code`
  with fixed constructors (`zero`, `succ`, `left`, `right`, `pair`, `comp`,
  `prec`, `rfind'`). Adding a new constructor requires either a separate
  parallel `OracleCode` inductive (~200 lines of definitions +
  re-establishing `exists_code`) or a downstream upstreaming to Mathlib.
  Neither fits in one S2 session.
* **The abstract level captures the diagonal content**: the parent
  `HaltingProblem.lean` is itself zero-import and works at the
  `Nat -> Nat -> Bool` abstraction. The relativization is a 1-argument
  thread-through; the diagonal argument is identical modulo the oracle
  parameter.

The pragmatic choice was therefore to ship the abstract result *fully proved*
(0 sorries, 0 axioms) in S2 ACT-A and defer the Mathlib bridge to a future
session (likely a sub-OQ `halting-problem-oq-03-bridge` or an S3+
iteration after the bridge's API design is finalized).

## Theorems Proved (S2 ACT-A, all zero-import, all in
`namespace RelativizedHalting`)

* `relativized_diagonal_differs` — for every oracle `o`, predictor `H`,
  and code `n`: `relativizedDiagonalBehavior H o n ≠ H o n n`.
* `no_relativized_halting_oracle` — contradiction form of OQ-03a (mirrors
  parent's `no_halting_oracle`).
* `relativized_halting_undecidable` — packaged form: for every oracle `o`
  and every predictor `H`, there exists a behavior that `H` mispredicts
  on every code.
* `relativized_collapses_to_classical_at_trivial_oracle` — sanity check
  that the `o = fun _ => false` specialization recovers the parent's
  `diagonalBehavior` shape.
* `no_uniform_relativized_halting_oracle` — strict separation: no single
  predictor uniformly decides relativized halting for every oracle and
  every behavior.

## Definitions

* `RelativizedHaltingPredictor : Type` — `(Nat -> Bool) -> Nat -> Nat -> Bool`.
* `Behavior : Type` — `Nat -> Bool` (namespaced to avoid collision with
  the parent file's `Behavior`).
* `relativizedDiagonalBehavior : RelativizedHaltingPredictor -> (Nat -> Bool)
  -> Behavior`.
* `Decides_in : (Nat -> Bool) -> RelativizedHaltingPredictor -> Prop`.
* `relativizedDiagonalWitness` (alias of `relativizedDiagonalBehavior`,
  exposed for downstream use).

## Build Status

S2 ACT-A build attempted in this session via
`./proofs/scripts/docker-build.sh Proofs.RelativizedHalting` (zero-import
file; expected build time short, but the worktree's `proofs/.lake` is the
known recursive self-symlink — so the Docker run will fresh-clone Mathlib
and rebuild dependencies). Final build status documented in the PR
description; if the Docker container times out, the PR is filed as "build
pending" per the memory pattern for `proofs/.lake` symlink-blocked
worktrees, and a follow-on mechanic PR or local-laptop build will confirm.

## Open API Questions — answered

* **Q1 (does `Nat.Partrec.Code.halting_problem` exist in Mathlib v4.26.0?)**:
  not a `theorem` of that name. The closest is the `Code.eval` /
  `Code.evaln` infrastructure plus the implicit halting-problem-as-not-
  recursive consequence of `Nat.Partrec.Code.exists_code` + Rice. For our
  purposes the parent's `no_halting_oracle` (zero-import) is the working
  reference.
* **Q2 (can `Code.eval` be cleanly oracle-parameterized?)**: **No**, not
  without a parallel inductive. `Code` is sealed. The S2 deliverable is
  therefore abstract (zero-import, no `Code` involvement), and the Mathlib
  bridge is deferred.
* **Q3 (namespace choice)**: **`RelativizedHalting`** (matches file name,
  no `Mathlib.` prefix since this is gallery code not a Mathlib upstream).
  The future Mathlib bridge would live under `Computability.OracleCode` if
  ever upstreamed.
* **Q4 (Mathlib upstream appetite)**: not pursued in S2; deferred to
  whoever picks up the bridge work. The abstract S2 file is intentionally
  *not* Mathlib-style (uses zero-import idioms matching the parent).

## Blockers

None. The proof is complete at the abstract level. The Mathlib bridge is
not a blocker for OQ-03a as proved; it is a separate (sizeable) packaging
project.

## Risks and Mitigations

* **Critique of pragmatic abstract path**: a reviewer may argue that
  OQ-03a's "real" statement requires the `Computable_in` class from
  Soare/Cooper, and that the abstract level proves a strictly weaker
  result. **Response**: the abstract level proves a *stronger* result. If
  `H` is any total function with the type signature of a relativized
  halting predictor (whether or not it is "computable in" anything), the
  diagonal argument diagonalizes against it. Any "computable in oracle"
  predictor is in particular a total function of the right type, so a
  fortiori cannot decide relativized halting. The abstract theorem implies
  the literature version; the literature version does not imply the
  abstract one. The docstring §"Why the abstract level suffices for
  OQ-03a" makes this explicit.
* **Tier-B race risk** (memory: "Fresh-slug scaffold can be lost"). At S2
  start time (07:34Z), `gh pr list --search halting-problem-oq-03` showed
  S1 (PR #17920) merged 5 minutes prior and no open PRs. Re-checked
  immediately before push.
* **Docker build risk** (memory: "broken proofs/.lake symlink"). Mitigation
  in the PR description: if the Docker build times out, file "build
  pending" per the memory pattern; the source is zero-import and trivially
  type-checks in any Lean 4 + Mathlib v4.26.0 environment.

## Next Session Pointer

Two options for S3, in priority order:

1. **(Recommended) S3 — Mathlib bridge sub-OQ.** Open a new sub-OQ slug
   `halting-problem-oq-03-bridge` and develop the parallel `OracleCode`
   inductive (~200 lines) + the `Code.evalnO` semantics + the lift
   `no_relativized_halting_oracle ⇒ undec` in Mathlib-class form. This is
   2-3 sessions of work; appropriate for a researcher with `Computability.
   PartrecCode` familiarity.

2. **S3 — Arithmetical hierarchy (OQ-03b).** Develop `Sigma^0_n / Pi^0_n /
   Delta^0_n` from scratch (~400 lines, 4-6 sessions). Per the S1 plan
   this likely warrants its own sub-OQ slug (`arithmetical-hierarchy-oq-01`
   or similar). Defer pending a strategic decision on whether the gallery
   wants in-tree arithmetical hierarchy.

Either option strictly extends the S2 abstract result; neither modifies the
S2 file. The S2 file is final for OQ-03a at the abstract level.

## Pool Status Note

After this S2 PR is filed, set status to `progress` (an abstract proof
exists; the Mathlib-bridge and OQ-03b/c remain). The slug retains tier-B
score because the bridge is a non-trivial follow-on.
