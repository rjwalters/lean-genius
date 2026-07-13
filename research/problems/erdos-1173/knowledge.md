# Knowledge Base: erdos-1173

Insights accumulated during research on this problem.

---

## Problem Understanding

Erdős–Hajnal set-mapping problem on the singular cardinal ℵ_ω.
Under GCH, given a set mapping
  f : ω_{ω+1} → [ω_{ω+1}]^{≤ℵ_ω}
satisfying the almost-disjoint condition |f(α) ∩ f(β)| < ℵ_ω for α ≠ β,
the question is whether there exists a free set of cardinality ℵ_{ω+1}
(where S is free if α ∉ f(β) for all distinct α, β ∈ S).

This generalizes the Hajnal free set theorem from regular to singular
cardinals, with a weaker (pairwise) intersection bound replacing the
pointwise size bound.

## Status

**Erdős Database Status**: OPEN
**Tractability Score**: 6/10
**Aristotle Suitable**: No (main conjecture is research-level; supporting
infrastructure already proved without sorries)

## Lean Formalization

`proofs/Proofs/Erdos1173Problem.lean` — 0 axioms, 0 sorries:
- Defines `aleph_omega`, `aleph_omega_succ`, `omega_omega_succ`, `GCH`
- Defines `SetMapping`, `BoundedImageSize`, `AlmostDisjoint`, `IsFreeSet`,
  `HasFreeSetOfCard`
- Defines the conjecture `erdos_1173 : Prop` (statement only — not proved)
- Proves: `gch_aleph_omega_strong_limit`, `overlap_bounded_by_aleph_n`,
  `aleph_omega_lt_succ`, `gch_power`, `free_set_empty`,
  `free_set_singleton`, `free_set_subset`

The main conjecture itself is left as `def erdos_1173 : Prop := ...`
(a problem statement, not a theorem). Gallery `meta.json` correctly
records `status: "axiomatized"` / `badge: "wip"`.

## Tags

- erdos, set-theory, infinitary-combinatorics, singular-cardinals,
  free-sets, GCH

## Related Problems

- Problem #2000, #83, #888, #2, #39, #1

## References

- Erdős, P. & Hajnal, A. — original problem
- Komjáth, P. (Ko25b), Problem 35
- Vaughan, J. (Va99), 7.88

---

## Insights

- All 4 named "axioms" referenced in early notes were either deep set-
  theoretic results (Hajnal's theorem, GCH consequences) or have since
  been *proved* in `Erdos1173Problem.lean` from Mathlib (no axiom
  declarations remain).
- `gch_aleph_omega_strong_limit` follows from GCH via the limit
  characterization of ℵ_ω = sup_{n<ω} ℵ_n.
- `overlap_bounded_by_aleph_n` shows the AlmostDisjoint hypothesis is
  equivalent to: for each pair α ≠ β there exists n with |f(α) ∩ f(β)|
  ≤ ℵ_n. This pigeonhole-style observation is the natural starting
  point for any positive resolution.
- The singularity of ℵ_ω prevents direct application of Hajnal's
  free-set theorem (which requires regularity).

## Dead Ends

- (none yet recorded)

---

## Sessions

### 2026-04-28: Metadata reconciliation (researcher-3)

`src/data/research/problems/erdos-1173.json` and `problem.md` were
largely empty placeholders ("Problem statement not found", empty
`whyMatters`/`knownResults`) while the Lean source and `meta.json`
were already correct. This session reconciled:

- Filled in `problemStatement.formal`, `.plain`, `.whyMatters`
- Populated `knownResults.proven`, `.open`, `.goal`
- Updated `currentState` to OBSERVE / blocked-on-research-level
- Removed self-referential `relatedProofs` entry (`erdos-1173`)
- Added `references.papers/urls/mathlib`
- Rewrote `problem.md` and this `knowledge.md` with real content

No Lean changes (file is already verified at 0 axioms / 0 sorries).
Disk constraints (98% full) made Docker builds inadvisable; pure-text
metadata reconciliation was the highest-value action available.

---

*Originally generated from erdosproblems.com on 2026-01-15.*
