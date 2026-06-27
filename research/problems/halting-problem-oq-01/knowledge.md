# Knowledge — halting-problem OQ-01

**Question.** *What is the computational complexity of approximating the
halting problem?* (`openQuestions[0]` of the gallery `halting-problem` entry.)

## Summary

The parent proof rules out a *total* halting decider. OQ-01 asks what happens
when the decider is allowed to **decline** or to **err on few inputs**, and how
expensive correct-where-it-commits approximation must be. This session:

1. Formalized the **structural core** (OQ-01a) in the gallery's zero-import
   schematic style: an *approximator* `A : ℕ → ℕ → Option Bool` may answer
   `true`/`false`/decline. Main theorem — **every sound approximator must
   decline at its own diagonal point**, a self-locating hard instance built from
   `A` itself. The classical no-oracle theorem is recovered as the always-commit
   special case.
2. Surveyed the genuine *quantitative* readings (density / generic-case
   complexity, OQ-01b; arithmetical-hierarchy placement, OQ-01c) and produced an
   infrastructure assessment for each: both need a computation model
   (`Mathlib.Computability.*`) and are **not** formalized here.

`HaltingApproximation.lean`: 0 sorries, 0 axioms, 0 Mathlib imports (imports only
the zero-import `Proofs.HaltingProblem`).

---

## Session 2026-06-27 (Session 1) — Partial-approximator diagonalization

**Mode**: FRESH (EMPTY tier, knowledge score 0)
**Outcome**: progress — new verified file `HaltingApproximation.lean`

### What I did
- Generalized `HaltingOracle = ℕ → ℕ → Bool` to
  `Approximator = ℕ → ℕ → Option Bool` (three-valued: commit-true / commit-false
  / decline).
- `diagApprox A n` = oppose `A`'s self-application guess, default `true` on decline.
- Proved:
  - `approx_not_commit_diagonal` — `A n n ≠ some (diagApprox A n)` for all `n`
    (the diagonal value is never correctly committed).
  - `total_approx_errs` — a `Total` approximator commits a *wrong* value at its
    diagonal point.
  - `sound_approx_declines_on_diagonal` — a `Sound` approximator (correct
    whenever it commits) must return `none` at any code implementing its diagonal
    behavior. **This is the headline result.**
  - `halting_approx_barrier` — summary existential.
  - `embedOracle` / `no_halting_oracle_from_approx` — classical undecidability is
    the always-commit special case, tying the new file back to the parent proof.

### Key findings / insights
- In the *schematic* (no-computation-model) setting, the "approximation" angle is
  genuinely captured by going from `Bool` to `Option Bool`: with totality dropped,
  the diagonal contradiction does not vanish — it *relocates* into a forced
  `none`. The hard instance is not adversarial/random but **self-locating**: the
  code of the approximator's own diagonal program.
- This is the honest schematic shadow of the real theorem "K is r.e. but not
  recursive": a sound semi-decider can confirm halting (commit `true`) but is
  forced to stay silent exactly on the non-halting diagonal instances.

### Infrastructure assessment — quantitative OQ-01 (NOT done this session)
- **OQ-01b density / generic-case (Hamkins–Miasnikov 2006):** "halting is
  decidable on a set of density 1" holds for *one* standard one-tape model and is
  **encoding-sensitive**. Formalizing needs: a concrete machine model with an
  input encoding, a density/measure on `ℕ`, and the black-hole/complexity
  argument. Size estimate **> 1000 lines** on top of a machine model Mathlib does
  not package for this purpose. **Decision: BLOCKED (needs computation model).**
- **OQ-01c hierarchy placement:** "the approximation gap is `Π⁰₁` and not `Σ⁰₁`"
  follows from Post's theorem. Mathlib has `Nat.Partrec`, `Nat.Partrec.Code`,
  `ComputablePred`, and `Mathlib.Computability.Halting`. Estimated **300–600
  lines** to (a) define the halting set via `Nat.Partrec.Code`, (b) show its
  complement is not r.e. This is the most tractable *genuine* next step.
  **Decision: ALTERNATIVE / future BUILD** — promising, deferred (this session
  prioritized the zero-import structural core to match gallery style).

### Files modified
- `proofs/Proofs/HaltingApproximation.lean` (new, ~140 lines, 0 sorry, 0 axiom)
- `proofs/Proofs.lean` (registered the new module)
- `research/problems/halting-problem-oq-01/{problem,knowledge}.md` (new)

### Next steps
- **OQ-01c**: build the arithmetical-hierarchy placement on `Nat.Partrec.Code`:
  define `K`, prove `K` r.e. (`Nat.Partrec`), prove `Kᶜ` not r.e. via the
  schematic diagonal already proven. This converts the schematic barrier into a
  genuine non-`Σ⁰₁` statement. ~300–600 lines.
- Optionally exhibit a *nontrivial sound approximator* (a "run k steps then
  decline" family) to demonstrate the decline-set is the only obstruction.
