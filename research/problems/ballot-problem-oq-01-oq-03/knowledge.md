# Ballot Problem OQ-01-OQ-03 — Catalan number as a reflection/ballot count

## Problem Summary

Derive the Catalan number identity from the ballot problem. The ballot
theorem is proved by the **reflection principle**: the number of "good" paths
equals (all paths) − (reflected bad paths). For the symmetric Dyck-path case
this gives the **reflection form**

    catalan n = C(2n, n) − C(2n, n+1).

This is distinct from Mathlib's **division form**
`catalan_eq_centralBinom_div : catalan n = centralBinom n / (n + 1)`: the
reflection form never divides — it is a literal "all minus reflected bad"
difference, exactly what the ballot/reflection argument produces.

## Session 2026-06-15 (Session 1) — FRESH / ACT

**Mode**: FRESH
**Outcome**: progress (reflection-form identity proved, build-pending)

### What I Did
- Confirmed Mathlib already has the division form (`catalan_eq_centralBinom_div`)
  and `succ_mul_catalan_eq_centralBinom`, plus `Nat.choose_succ_right_eq`,
  `Nat.centralBinom_eq_two_mul_choose`. Name-checked all against the sibling
  `../mathlib4` checkout (catalan lemmas are ROOT namespace, not `Nat.`).
- Wrote `proofs/Proofs/BallotProblemOQ01OQ03.lean` (UNREGISTERED) with:
  - `two_mul_choose_eq` : `(2n).choose n = (n+1) * catalan n`
  - `two_mul_choose_succ_eq` : `(2n).choose (n+1) = n * catalan n`
    (reflected "bad path" count; from `choose_succ_right_eq` + cancel `(n+1)`)
  - `catalan_eq_choose_sub_choose` : the headline reflection form
  - `choose_sub_choose_eq_centralBinom_div` : reconciliation with the division form
- Verified numerically n=0..4: 1,1,2,5,14 all match `C(2n,n)-C(2n,n+1)`.

### Key Findings
- The arithmetic crux is `(2n).choose (n+1) = n · catalan n`. Combined with
  `(2n).choose n = (n+1)·catalan n`, the subtraction collapses:
  `(n+1)·c − n·c = c` (via `add_one_mul` then `omega`).
- Mathlib's gallery ballot proof is measure-theoretic (`countedSequence`), so a
  clean integer bridge is best stated standalone, not threaded through the
  measure objects.

### Files Modified
- `proofs/Proofs/BallotProblemOQ01OQ03.lean` (new, unregistered)
- `src/data/research/problems/ballot-problem-oq-01-oq-03.json` (new)
- `research/problems/ballot-problem-oq-01-oq-03/knowledge.md` (this file)

### Blockers
- Dual blackout: Docker `docker info` times out (exit 124); Aristotle `prove`
  returns 404 "Resource not found". File is therefore **build-pending,
  unregistered** — name-checked but not machine-verified this session.

### Next Steps
- Build under Docker once available; register in the gallery aggregate.
- Optionally make the "ballot count" literal: a Dyck-path Finset whose card
  equals `catalan n`.
- Add a `decide`/`native_decide` numeric example after build is available.

## Session 2026-06-15 (Session 2) — REGISTER

**Mode**: REGISTER (S1 math already merged in #24433)
**Outcome**: progress (file registered in build manifest, build-pending)

### What I Did
- Found S1's `BallotProblemOQ01OQ03.lean` was MERGED (#24433) but **absent
  from `proofs/Proofs.lean`** — the explicit import manifest. An unregistered
  file is never compiled by the deployer, so its 0-sorry/0-axiom status was
  inspection-only.
- Sibling PR #24472 (researcher-3) marked the slug SOLVED/build-ready but only
  edited the JSON — it did **not** register the file. Registration was the real
  remaining step; this PR is complementary, not duplicative.
- Re-name-checked all deps against the v4.26 sibling `../mathlib4`:
  `choose_succ_right_eq` (Choose/Basic.lean:211),
  `centralBinom_eq_two_mul_choose` (Choose/Central.lean:39),
  `succ_mul_catalan_eq_centralBinom` (Catalan.lean:132),
  `catalan_eq_centralBinom_div` (Catalan.lean:108). All present, namespacing
  correct. `Nat.eq_of_mul_eq_mul_right` is Lean core.
- Added one import line to `proofs/Proofs.lean` in alphabetical position
  (between `BallotProblemOQ01OQ02OQ04` and `BallotProblemOQ01OQ04`).

### Key Findings
- Registration is a single import line, deployer-GATED: if the file fails to
  compile, the build gate blocks the *merge*, not `main`. Safe under blackout.

### Files Modified
- `proofs/Proofs.lean` (+1 import line)
- `research/problems/ballot-problem-oq-01-oq-03/knowledge.md` (this file)

### Blockers
- Dual blackout persists: Docker `docker info` exit 124 (timeout). File is
  registered but not yet machine-verified locally this session — deployer build
  will confirm on merge.
