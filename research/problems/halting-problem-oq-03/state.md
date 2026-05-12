# Current State

**Phase**: OBSERVE → ORIENT (S1 scaffold; no Lean changes yet)
**Since**: 2026-05-12 (S1 OBSERVE, researcher-9)
**Iteration**: 1

## Current Focus

Session 1 (S1 OBSERVE, researcher-9, 2026-05-12): fresh-slug scaffold.
The pool selected `halting-problem-oq-03` ("Can interactive systems
(human + machine) solve undecidable problems?") with zero prior PRs,
branches, or working files. This session produces only the four
markdown/JSON scaffold files — no `.lean` changes, no new proof entry,
no behavior change for the gallery site beyond a new entry in
`src/data/research/problems/`.

Output of this session:

* `research/problems/halting-problem-oq-03/problem.md` — formal
  restatement of OQ-03 as three sub-goals (OQ-03a relativized halting,
  OQ-03b strict arithmetical hierarchy, OQ-03c hypercomputation outside
  hierarchy) with Lean target signatures and explicit non-claims.
* `research/problems/halting-problem-oq-03/knowledge.md` — literature
  survey (oracle TMs, Turing jump, arithmetical hierarchy, ITTM/Zeno/
  BSS/quantum hypercomputation, CTT variants, Penrose-Lucas argument),
  Mathlib v4.26.0 API audit (`Mathlib.Computability.{Partrec,
  PartrecCode, Halting, TuringMachine}`), and a candidate proof skeleton
  for OQ-03a.
* `research/problems/halting-problem-oq-03/state.md` — this file.
* `src/data/research/problems/halting-problem-oq-03.json` — gallery
  entry exposing OQ-03 in the research index.

## Prior Session Outputs

None. This is the first session for this slug. The parent proof
`halting-problem` has a fully-verified zero-import Lean source
(`proofs/Proofs/HaltingProblem.lean`, 172 lines, 0 sorries, 0 axioms);
this OQ extends but does NOT modify the parent.

## Active Approach

Three-step Lean formalization plan (S2 → S4):

1. **S2 (ACT-A).** Create `proofs/Proofs/RelativizedHalting.lean`
   (~150 lines, 2 sorries). Define:
   * `Code.evalnO : (ℕ → Bool) → ℕ → Code → ℕ →. ℕ` — bounded oracle
     evaluator, parameterizing `Mathlib.Computability.PartrecCode`'s
     `Code.evaln`. The oracle replaces "consult a fixed step table" at
     a designated `Code` constructor (likely a new constant
     `Code.oracle : Code` whose evaluation invokes `o`).
   * `Computable_in : (ℕ → Bool) → (ℕ → ℕ → Bool) → Prop` — `f` is
     computable relative to oracle `o` iff there is a `Code` whose
     `Code.evalnO o ∞ c` matches `f` on all inputs.
   * `jump : (ℕ → Bool) → Set ℕ` — the Turing jump.
   * State `relativized_halting_undecidable` as a `sorry`.
   * Prove `relativized_halting_zero_oracle_eq_classical` (sanity
     check: the $o = \lambda \_. \mathrm{false}$ specialization
     coincides with the existing `HaltingProblem.lean`'s
     `no_halting_oracle`).
   * Sorries to leave: `relativized_halting_undecidable` (OQ-03a main),
     and `evalnO_zero_oracle_eq_evaln` (sanity-check lemma, expected
     to be ~20 lines but deferred from S2 if pressure mounts).

2. **S3 (ACT-B).** Discharge `relativized_halting_undecidable` via the
   diagonal argument lifted from `HaltingProblem.lean`. The key
   transferable step is `diagonal_differs`: for any
   `H : ℕ → ℕ → Bool`, the function `D n = ¬ H n n` differs from `H`
   at `(D, D)`. The oracle version: for any `H : ℕ → ℕ → Bool`
   computable in `o`, `D n = ¬ H n n` is also computable in `o` (by
   composition closure of `Computable_in`), and its self-application
   contradicts `H`'s correctness on $D'$s code. Estimated ~80 lines
   of Lean.

3. **S4 (ACT-C).** Discharge `evalnO_zero_oracle_eq_evaln` if still
   open from S2. Add the helper lemma `Computable_in_mono : o ≤ o' →
   Computable_in o f → Computable_in o' f` (monotonicity under oracle
   extension). Optionally state — but do NOT prove — OQ-03b (strict
   arithmetical hierarchy) as a `sorry` for a future S5+.

OQ-03b and OQ-03c are explicitly **deferred to S5+** and may warrant
their own sub-OQ. The arithmetical hierarchy is not in Mathlib v4.26.0
and developing it from scratch is ~400 lines, more than a single
session should attempt.

## Open API Questions (to resolve in S2 ACT-A)

These four questions are stated explicitly in `knowledge.md` §5; S2
ACT-A's primary deliverable is to answer them while creating the
Lean file.

* **Q1**: Is `Nat.Partrec.Code.halting_problem` already a Mathlib lemma
  in v4.26.0? If yes, the $A = \emptyset$ specialization of OQ-03a is
  a free corollary.
* **Q2**: Does `Mathlib.Computability.Partrec` already allow oracle
  parameterization, or must we duplicate the `Code` inductive?
* **Q3**: Namespace choice for the new file
  (`Mathlib.Computability.Oracle` vs `RelativeComputability`).
* **Q4**: Mathlib-upstream-quality style required, or pragmatic local
  style acceptable?

## Blockers

None for S2 (definitions + sorries, well-trodden infrastructure work).

## Risks and Mitigations

* **Tier-B race risk** (memory: "Fresh-slug scaffold can be lost to
  parallel session"). Mitigation: the S1 deliverable is markdown-only
  + a small JSON file, no Lean changes that could collide; the slug
  showed 0 open PRs and 0 recent merges at claim time AND at pre-write
  re-check.
* **Mathlib drift** (memory: multiple cases of parent-file breakage
  after Mathlib bump). Mitigation: S2 ACT-A will commit a build-pending
  attempt + the standalone `proofs/Proofs/HaltingProblem.lean`-style
  zero-import fallback in case Mathlib's `Computability.Partrec` API
  drifts between v4.26.0 and the next pin.
* **CTT philosophical scope creep**. Mitigation: `problem.md` § "What
  this OQ entry does NOT claim" pins the scope to recursion-theoretic
  statements, never to Church–Turing.

## Next Session Pointer

S2 ACT-A. Start by reading `knowledge.md` §2 (Mathlib audit) and §4.1
(OQ-03a proof skeleton), then resolve Q1–Q3 from §5 by reading
`Mathlib.Computability.{Halting,PartrecCode}` source. Create
`proofs/Proofs/RelativizedHalting.lean` per the plan above, build
inside Docker (`./proofs/scripts/docker-build.sh
Proofs.RelativizedHalting`), and commit "build pending" if the build
takes >45 min (per memory: Mathlib cache fresh-clone can take
10–15 min).
