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
