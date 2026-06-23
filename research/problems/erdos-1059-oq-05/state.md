# Current State

**Phase**: COMPLETED
**Since**: 2026-04-27T00:00:00.000Z
**Iteration**: 1

## Current Focus

`Decidable` instance for `AllFactorialSubtractionsComposite` formalized in
`proofs/Proofs/Erdos1059OQ05.lean`. The OQ — "provide a general decision
procedure eliminating per-prime factorial-bound boilerplate" — is answered.
File: 99 lines, 0 axioms, 0 sorries, 7 theorems, 1 definition, 1 instance.

## Active Approach

None — work is in maintenance mode.

## Built Items

- `factorial_lt_implies_lt {k n : ℕ} (h : k! < n) : k < n` — via `Nat.self_le_factorial`.
- `allFactorialSubtractionsComposite_iff_bounded` — equivalence with `∀ k ∈ Finset.range n, ...`.
- `decAllFactorialSubtractionsComposite` (instance) — `decidable_of_iff`, inherits `Finset.decidableBAll`.
- Witness theorems: `witness_101`, `witness_211`, packaged `erdos_1059_witnesses`.
- Non-witnesses: `non_witness_89` (89 − 3! = 83 prime), `non_witness_223` (223 − 4! = 199 prime).
- All five computational results discharge by `native_decide`.

## Blockers

None. The decidable infrastructure is complete; the parent Erdős 1059
conjecture (infinitely many witnesses) remains open in mathematics.

## Next Action

Gallery `meta.json` carries `status: "axiomatized"`, `badge: "wip"` —
inherited from the parent open conjecture even though the supporting
infrastructure here is itself 0-axiom / 0-sorry. Sibling `erdos-1059-oq-03`
(also pure verified infrastructure) ships `status: "verified"` /
`badge: "original"` as precedent; aligning OQ-05 is a candidate
status-sync, but out of scope for this state.md sync.

Future witness search using `decAllFactorialSubtractionsComposite` should
proceed on a separate problem (density estimates, gap searches, or analogous
factorial-subtraction properties).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (bounded-quantifier equivalence + `decidable_of_iff`)
