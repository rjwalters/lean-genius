# Current State

**Phase**: AXIOMATIZED — EQUIVALENCE-PROVED (conjecture isolated, 0 sorries)
**Since**: 2026-05-13 (STATE-SYNC, prior stub since 2026-01-13)
**Iteration**: STATE-SYNC

## Current Focus

The Lean formalization (`proofs/Proofs/Erdos430Problem.lean`, 249 LOC) is structurally
complete with the open conjecture isolated as a single axiom and the Adenwalla
equivalence with Erdős #385 fully proved in both directions. State.md was a seeker-init
"NEW" stub four months out of sync with the Lean source; this entry refreshes the
visible state without modifying any proof artifact.

## Source-of-Truth Counts (proofs/Proofs/Erdos430Problem.lean)

| Kind            | Count | Examples                                                  |
|-----------------|-------|-----------------------------------------------------------|
| Definitions     | 7     | `minPrimeFactor`, `allPrimeFactorsExceed`, `IsAdmissible`, `greedyNext`, `greedySeq`, `seqTerminates`, `hasComposite` |
| Decidable inst. | 2     | `decidableAllPrimeFactorsExceed`, `decidableIsAdmissible` |
| Theorems        | 5     | `example_n8`, `greedySeq_le`, `greedySeq_terminates`, `erdos_385_equivalence`, `small_n_all_prime` |
| Private lemmas  | 5     | `greedyNext_admissible`, `greedySeq_admissible`, `greedyNext_lt`, `greedyNext_zero`, `greedySeq_zero_of_le_one` |
| Sorries         | 0     | (verified by `grep -cE '^[[:space:]]*sorry[[:space:]]*$\|:= sorry$\|:= by sorry'`) |
| Axioms          | 1     | `erdos_430_conjecture` (open conjecture, isolated) |

## Axiom Inventory (1 total, all open-conjecture)

| Axiom                    | Status   | Group                | Notes |
|--------------------------|----------|----------------------|-------|
| `erdos_430_conjecture`   | OPEN     | Open conjecture only | "∃ N₀, ∀ n ≥ N₀, hasComposite n" — Erdős/Graham/Selfridge, no proof known |

No foundational or finite-decidable axioms remain. The previously-axiomatized
`small_n_all_prime` was discharged in an earlier iteration (n₀ = 1 makes the sequence
identically 0, so any positive element of the sequence is vacuously prime for n ≤ 1).

## Equivalence Theorem (the key formal contribution)

`erdos_385_equivalence` (lines 164–219) proves:

```
(∃ N₀, ∀ n ≥ N₀, hasComposite n)  ↔  (∃ N₀, ∀ n ≥ N₀, ∃ m, 1 < m < n ∧ ¬m.Prime ∧ allPrimeFactorsExceed m (n - m))
```

This is the Adenwalla observation that #430 reduces to (the first part of) #385.

- **Forward direction**: a composite element of the greedy sequence is, by
  `greedySeq_admissible`, an admissible composite < n.
- **Backward direction**: an admissible composite m < n is bounded below by the
  greedy sequence (proved via strong induction on the gap `current - m`, using
  the key lemma `greedyNext n prev ≥ m when prev > m`), so the sequence reaches m.

Both directions are by-tactic, no sorries.

## Active Approach

State synchronization only; no proof edits. The Lean source is already at the
"axiomatized with equivalence proved" frontier and matches the public framing of
Erdős #430 (open conjecture; equivalent to first part of #385).

## Forward Levers (NOT a roadmap to resolve the open conjecture)

1. **Erdős #385 first-part formalization (parallel slug).** Discharging
   `erdos_430_conjecture` is equivalent (by the proved equivalence theorem) to
   producing a constructive `(N₀, ∀ n ≥ N₀, ∃ m …)` witness — which is the
   #385 first-part statement. Work on either slug discharges the other via the
   equivalence theorem already in this file. (Both remain open.)
2. **Computational evidence for specific N₀.** `greedySeq` is fully computable
   (Decidable instances + `Finset.sup` over a finite range); a `native_decide`
   bracket over n ∈ [n₀, n_max] could confirm `hasComposite n` empirically for
   each n in range and tighten the conjectured N₀. Currently only `example_n8`
   (n = 8, no composite — small-n boundary) is proved by `native_decide`.
3. **Strengthen `small_n_all_prime`.** The current statement uses n₀ = 1 (trivial
   range where the sequence is identically zero). A nontrivial extension would
   prove that for some explicit small range n ∈ [2, n_small], the sequence
   contains no composite — this carves out the boundary where the conjectured
   N₀ must lie.

## Blockers

None — the proof file builds. The remaining `axiom erdos_430_conjecture` is an
open mathematical conjecture (Erdős/Graham/Selfridge), not a Lean blocker.

## Next Action

Either:
- claim Erdős #385 slug and use this equivalence theorem to import progress, or
- pursue Forward Lever 2 (computational `native_decide` bracket) on a separate
  branch.

No edit to this slug's Lean source is required to advance.

## Honesty Block

- This is a doc-only state.md refresh — no `.lean` file, no `meta.json`, no
  `annotations.json`, and no Mathlib symbol was modified.
- The "Phase" label is descriptive of the saturated state of the Lean source;
  it does NOT claim the open conjecture is resolved. The conjecture remains
  the standing axiom `erdos_430_conjecture` at line 226.
- The Adenwalla equivalence (`erdos_385_equivalence`) is fully proved and
  axiom-free given Mathlib; the proof uses standard finset/decidability
  machinery and a strong induction on a `ℕ`-valued gap.
- `meta.json` claims `theoremCount: 10` and `definitionCount: 7`; the table
  above counts 5 public theorems + 5 private lemmas = 10 (matches) and 7 defs
  (matches). `axiomCount: 1` matches the inventory.

## Attempt Counts

- Total attempts (cumulative across sessions): 1+ (prior researcher session(s)
  produced the equivalence proof and discharged `small_n_all_prime`)
- Current approach attempts: STATE-SYNC iteration (this PR)
- Approaches tried (cumulative): equivalence-to-#385 (proved), greedy-sequence
  admissibility + descent (proved), small-n boundary (proved for n ≤ 1)
