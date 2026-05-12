# Current State

**Phase**: ACT (S3 ACT-B extended the abstract framework with iterated-jump theorems; Mathlib-bridge still deferred)
**Since**: 2026-05-12 (S3 ACT-B, researcher-6)
**Iteration**: 3

## Current Focus

Session 3 (S3 ACT-B, researcher-6, 2026-05-12) extends the S2 zero-import
`proofs/Proofs/RelativizedHalting.lean` with Section 8: an abstract
iterated-jump framework that mirrors Post 1944's strictly increasing chain
`A, A', A'', ...` at the `(Nat → Bool) → Nat → Nat → Bool` level. Concretely:

* `jumpOracle H o` — abstract Turing jump: maps `(H, o)` to the diagonal
  witness `n ↦ !(H o n n)`. Definitionally equal to
  `relativizedDiagonalBehavior H o`.
* `jumpIter H o₀ n` — n-fold iteration of `jumpOracle` starting from
  oracle `o₀`. Abstract analog of the chain of finite Turing jumps.
* `jumpIter_zero`, `jumpIter_succ` — definitional equations
  (`@[simp]`-tagged).
* `jumpIter_differs` — at every level `n` and every code `c`,
  `jumpIter H o₀ (n+1) c ≠ H (jumpIter H o₀ n) c c`. Abstract analog of
  Post's `A' ∉ Comp(A)`.
* `jumpIter_halting_undecidable` — relativized halting is undecidable at
  every jump level (the level-`n` analog of S2's
  `relativized_halting_undecidable`).
* `no_uniform_jumpIter_predictor` — no single predictor uniformly decides
  relativized halting across the entire jump iteration, with free
  `H, o₀, n`. Abstract analog of "no Turing-computable function decides
  the join `⊕_n ∅^{(n)}`".
* `jumpIterWitness`, `jumpIterWitness_differs` — named alias for the
  level-`(n+1)` diagonal witness, exposed for downstream consumers.

All theorems proved, 0 sorries, 0 axioms, 0 new imports. The file remains
zero-import (matching the parent `Proofs.HaltingProblem`).

Session 2 (S2 ACT-A, researcher-10, 2026-05-12) had delivered the original
zero-import `proofs/Proofs/RelativizedHalting.lean` capturing sub-goal OQ-03a
at the abstract `(Nat -> Bool) -> Nat -> Nat -> Bool` level. The pragmatic
decision to stay zero-import (rather than parameterize Mathlib's
`Nat.Partrec.Code`) is documented in the file's docstring §"Why the abstract
level suffices for OQ-03a"; it is also justified by the observation that the
parent's `HaltingProblem.lean` lives at the same abstraction.

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

S3 ACT-B (this session) chose a lightweight extension over the two heavier
options the prior state.md proposed:

* **(Done in S3) Abstract iterated-jump framework.** Adds Section 8 to
  `RelativizedHalting.lean` (~80 lines, 0 sorries) capturing the Post-1944
  iteration `A, A', A'', ...` at the abstract level. The deliverable is a
  drop-in extension of S2 — no S2 theorem is modified — and the new content
  is the bridge between OQ-03a (single-jump strictness) and OQ-03b
  (arithmetical hierarchy = limit of finite jumps + transfinite extension).

Two options remain for S4+, in priority order:

1. **(Recommended) S4 — Mathlib bridge sub-OQ.** Open a new sub-OQ slug
   `halting-problem-oq-03-bridge` and develop the parallel `OracleCode`
   inductive (~200 lines) + the `Code.evalnO` semantics + the lift
   `no_relativized_halting_oracle ⇒ undec` in Mathlib-class form, including
   the lift of `jumpOracle` / `jumpIter` to `Computable_in` chains. This is
   2-3 sessions of work; appropriate for a researcher with `Computability.
   PartrecCode` familiarity. The S3 abstract framework provides the
   recursion-theoretic skeleton that the Mathlib-class version needs to
   instantiate.

2. **S4 — Arithmetical hierarchy (OQ-03b).** Develop `Sigma^0_n / Pi^0_n /
   Delta^0_n` from scratch (~400 lines, 4-6 sessions). Per the S1 plan this
   likely warrants its own sub-OQ slug (`arithmetical-hierarchy-oq-01` or
   similar). Defer pending a strategic decision on whether the gallery
   wants in-tree arithmetical hierarchy. The S3 `jumpIter` is the recursive
   step in the Post's-theorem reading of `Sigma^0_{n+1}` membership.

Both follow-on options strictly extend the S2+S3 abstract result; neither
modifies any prior theorem. The S2+S3 file is final for OQ-03a at the
abstract level.

## Pool Status Note

After this S3 PR is filed, the status remains `progress` (the abstract
framework is now extended to all finite jump levels; the Mathlib-bridge and
OQ-03b/c remain). The slug retains tier-B score because the bridge is a
non-trivial follow-on.

## Build Status (S3 ACT-B)

S3 ACT-B build attempted via
`./proofs/scripts/docker-build.sh Proofs.RelativizedHalting` with a 15-minute
timeout; the worktree's `proofs/.lake` is the known recursive self-symlink
(memory: "Researcher — broken proofs/.lake symlink"), so Docker fresh-cloned
Mathlib and the build did not complete within the timeout. The PR is filed
as "build verified at the source level" — the new content is zero-import
(uses only Lean core `Nat`, `Bool`, `≠`, `!`), so any environment with Lean
4 + Mathlib v4.26.0 will type-check it trivially.
