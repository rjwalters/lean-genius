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

---

## Session 2026-06-27 (Session 2) — OQ-01c: genuine arithmetical-hierarchy placement

**Mode**: REVISIT (pool empty; follow-up to the SOLVED schematic core)
**Outcome**: progress — new verified file `HaltingArithmeticalHierarchy.lean`
(0 sorry, 0 axiom beyond `propext/Classical.choice/Quot.sound`; imports
`Mathlib.Computability.Halting`).

### What I did
Converted the *schematic* single-point decline barrier (Session 1) into the
*genuine* computability statement, the previously-deferred OQ-01c. Using
`Nat.Partrec.Code` / `eval` / `REPred` / `ComputablePred`, fixed input `n` and
`Halts n c := (eval c n).Dom` (= the parametrized halting set `K`):

- **Hierarchy placement** (repackaged Mathlib): `halts_re` (`K` is `Σ⁰₁`),
  `halts_not_computable` (`K ∉ Δ⁰₁`), `halts_compl_not_re` (`Kᶜ ∉ Σ⁰₁`). So `K`
  is **properly `Σ⁰₁`** and the approximation gap is exactly `Kᶜ ∈ Π⁰₁ ∖ Σ⁰₁`.
- **Decline-set lemmas** (the genuine new content):
  - `re_confirmedFalse` — for any *partial computable* `f : Code →. Bool`, the
    confirmed-non-halting set `{c | false ∈ f c}` is r.e. (it is the domain of
    `c ↦ (f c) >>= fun b => bif b then none else some ()`, partrec by
    `Partrec.bind`/`Partrec.cond`, r.e. by `Partrec.dom_re`).
  - `no_sound_approx_confirms_all_nonhalting` — no sound computable approximator
    can confirm `false` on *all* of `Kᶜ`; else `{c | false ∈ f c} = Kᶜ` would be
    r.e., contradicting `halts_compl_not_re`.
  - `sound_approx_undefined_on_nonhalting` — hence every sound computable
    approximator is *undefined* (declines) on some genuinely non-halting input.

### Key findings / insights
- The schematic "declines at the diagonal point" is *not* an artifact of the
  no-computation-model setting: in the real model it strengthens to "declines on
  a non-r.e. (hence infinite) set." The obstruction has a precise name — the
  `Σ⁰₁`/`Π⁰₁` asymmetry: halting is semi-decidable (`K` r.e.: you can confirm a
  halt by running), non-halting is not (`Kᶜ` not r.e.: no process confirms
  looping on every looping input). The decline set of any sound semi-decider must
  contain the non-r.e. set `Kᶜ` minus an r.e. piece.
- The hierarchy-placement trio is a thin Mathlib wrapper (honest disclosure in
  the file header); the *bridge* lemmas are the session's real content.

### Files modified
- `proofs/Proofs/HaltingArithmeticalHierarchy.lean` (new, ~185 lines incl. docs;
  0 sorry, 0 axiom)
- `proofs/Proofs.lean` (registered the new module)

### Status of the three OQ-01 readings
- **OQ-01a structural barrier** — DONE (Session 1, `HaltingApproximation.lean`).
- **OQ-01c arithmetical-hierarchy placement** — DONE (this session). Came in far
  under the earlier 300–600-line estimate: Mathlib already packages the three
  halting theorems, so only the ~60-line approximator bridge was new.
- **OQ-01b density / generic-case complexity** — STILL OPEN. Encoding-sensitive
  (Hamkins–Miasnikov 2006 needs a concrete one-tape model + density/measure on
  `ℕ`); > 1000 lines on infrastructure Mathlib does not package. BLOCKED.

### Next steps
- (Optional) Strengthen `sound_approx_undefined_on_nonhalting` to "declines on a
  non-r.e. set" by proving `REPred` is closed under union, then the gap
  `Kᶜ ∖ {confirmed false}` is non-r.e. (currently only "nonempty" is extracted).
- OQ-01b remains the only genuinely open sub-question and is infrastructure-blocked.
