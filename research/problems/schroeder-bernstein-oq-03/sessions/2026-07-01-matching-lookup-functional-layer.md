# researcher-2 — Myhill OQ-03: the matching as a computed partial function (2026-07-01)

## Context
Myhill's isomorphism theorem (computable injections ⟹ computable bijection). The
easy direction and a large infrastructure layer are proved; the single remaining
`sorry` is the hard direction (`myhill_isomorphism` →) — the stage-wise
back-and-forth scheduler with collision-chasing (~200 lines of Partrec work).

researcher-6 built the fully-computable easy case + Π₁ obstruction analysis.
researcher-1 (PR #32280) built the finite-matching layer: `IsMatching`,
`MatchingCorr`, atomic steps `matching_step_f`/`matching_step_g`, and the
set-theoretic partial-bijection lemmas `matching_functional`/`matching_cofunctional`.

## This session — the functional/computed layer (Section 4d)
The scheduler's final step reads off the total permutation `σ` from the *limiting*
matching and must certify `σ` computable. That needs the matching presented as an
actual **computed function**, not merely a set-theoretic partial bijection. Added:

- **`mLookup L a := L.lookup a`** — the computable partner map.
- **`mLookup_eq_some_of_mem`** — on a matching, `(a,b) ∈ L ⟹ mLookup L a = some b`
  (the functional/computed form of `matching_functional`). Proof: induction using
  domain-side `Nodup` — off the head `a ≠ k` so `List.lookup` skips it.
- **`mLookup_isSome_iff`** — `(mLookup L a).isSome ↔ a ∈ mDom L`: the lookup is
  defined *exactly* on the domain.
- **`mem_of_mLookup_eq_some`** — converse (no matching hypothesis needed).
- **`matchingCorr_mLookup`** — the computed lookup respects `p ↔ q`, so `σ` is read
  off **without** ever evaluating the possibly-non-computable predicates `p, q`.

All four are 0-axiom (`#print axioms` = only `propext, Classical.choice, Quot.sound`;
no `sorryAx`). File: 674 LOC, 41 theorems/lemmas, 11 defs, **1 sorry** (the open
hard core, unchanged). Compiles clean against pinned Mathlib v4.26.0.

## Honest status
This is partial progress on an OPEN problem. The single hard `sorry` (the scheduler)
is untouched; this PR completes a verified sub-API it will consume. No new axioms,
no `True` placeholders.

## Next
- Define the stage builder (recursion over stages) using the atomic `matching_step_f/_g`.
- Prove exhaustion invariants (k enters by stage 2k+1) and read off `σ` via `mLookup`
  on the limiting matching; derive computability from the stage function + `mLookup`.
