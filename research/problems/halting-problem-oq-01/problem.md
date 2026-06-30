# OQ-01 of the Halting Problem — Formal Statement

**Parent proof**: `halting-problem` (Turing 1936; `proofs/Proofs/HaltingProblem.lean`).

**Informal question** (from `src/data/proofs/halting-problem/meta.json`,
`openQuestions[0]`):

> What is the computational complexity of approximating the halting problem?

## What "approximating" means

The parent proof rules out a *total* decider: there is no
`H : ℕ → ℕ → Bool` correct on every `(p, i)`. The natural relaxation studied
in the literature is to allow the decider to **decline** on hard inputs, or to
err on a small set, and to ask *how much* it must decline/err. Three concrete
formal readings:

- **OQ-01a (partial / one-sided approximation — the schematic core).**
  Model an approximator as a partial Boolean function
  `A : ℕ → ℕ → Option Bool`, where `none` means "decline". Ask: must `A`
  decline somewhere, and *where*? — **Answered formally this session** (see
  `HaltingApproximation.lean`): every sound `A` must decline at its own
  *diagonal point*, a self-locating, constructively-findable hard instance.

- **OQ-01b (density / generic-case complexity).** For a fixed encoding, what is
  the asymptotic density of the set of inputs on which halting *is* decidable by
  a total computable approximator? Hamkins–Miasnikov (2006) show the halting
  problem is decidable on a set of density 1 *for one standard model* (one-tape,
  one-way), i.e. "generically computable" — but this is **encoding-sensitive**
  and fails for other models. Formalizing requires a measure/density on program
  space plus a computation model.

- **OQ-01c (hierarchy placement of the gap).** The halting set `K` is
  `Σ⁰₁`-complete: r.e. but not co-r.e. The "approximation gap" — the set where a
  sound semi-decider must remain silent — is exactly the complement of an r.e.
  set, hence `Π⁰₁` and not `Σ⁰₁`. Formalizing requires Mathlib's
  `Nat.Partrec` / `ComputablePred` and Post's theorem.

## This session's scope

OQ-01a is formalized in the gallery's established **zero-import schematic**
style (no computation model, no Mathlib). OQ-01b and OQ-01c are the genuine
*quantitative* complexity content; both require a computation model and are
documented as infrastructure assessments in `knowledge.md`, not formalized here.

## Honest status

The schematic theorem proved this session captures the *structural* barrier
(every approximator has a self-locating forced gap) but **not** a complexity
class statement. The prose question OQ-01, in its full quantitative sense,
remains open and is correctly flagged as requiring `Mathlib.Computability.*`.
