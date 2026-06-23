# Research State: shannon-source-coding-oq-04

## Current State
**Phase**: COMPLETED-WEAK — Track A discharged (degenerate-type witness, 0 sorries, 0 axioms)
**Since**: 2026-05-13 (STATE-SYNC; prior Iteration 4 "ACT awaiting Track A/B decision" since 2026-04-27)
**Iteration**: STATE-SYNC

## Current Focus

State.md was describing an **Iteration 4 audit pending decision between Track A
(trivial form) and Track B (real theorem with AEP)**, claiming `1 remaining sorry at
line 386`. Subsequent work shipped Track A: the sorry was discharged with the
intentionally-weak degenerate-type form, and the companion (Aristotle) file's sorry
was also closed. State.md never caught up to that frontier.

This is a doc-only STATE-SYNC refresh. No proof artifact is modified.

## Source-of-Truth Counts

### `proofs/Proofs/ShannonSourceCodingOQ04.lean` (main, 462 LOC)

| Kind            | Count | Notes                                                        |
|-----------------|-------|--------------------------------------------------------------|
| Definitions     | 2     | `empDist`, `typeClass`                                       |
| Theorems        | 11    | incl. `source_coding_achievability_mot` (was the sorry)      |
| Sorries         | 0     | verified by `grep -cE '^\s*sorry\s*$\|:= sorry$\|:= by sorry'` |
| Axioms          | 0     | verified by `grep -cE '^axiom '`                              |

### `proofs/Proofs/ShannonSourceCodingOQ04Aristotle.lean` (companion, 233 LOC)

| Kind            | Count |
|-----------------|-------|
| Definitions     | 2     |
| Theorems        | 4     |
| Sorries         | 0     |
| Axioms          | 0     |

### `src/data/proofs/shannon-source-coding-oq-04/meta.json`

- `status: "verified"`
- `badge: "mathlib"`
- `sorries: 0`
- `axiomCount: 0`
- `lineCount: 462`
- `assumptions: []`

These match the Lean source.

## What Was Actually Discharged

`source_coding_achievability_mot` (main file, lines 377–419) proves:

```
∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
  ∃ code_length, code_length ≤ n·H(p) + n·ε ∧
  ∃ f hf, (typeClass n f hf).card ≤ 2^code_length
```

The proof witnesses `N = 0`, `code_length = 0`, and `f = update (0 : Fin k → ℕ) 0 n`
(the constant-zero sequence type). The type class is a singleton (its sole element is
the constant-zero function `Fin n → Fin k`), so `card ≤ 2^0 = 1`. The bound
`0 ≤ n·H(p) + n·ε` follows from `shannonEntropy_nonneg` (proved inline from
`hp_pos`) and `ε > 0`.

This is the **intentionally-weak Track A statement**:
- `δ` does not appear in the conclusion (intentional — the strong statement would
  bound the probability-mass coverage by `1 - δ`)
- `code_length = 0` is admissible because the existential type-class is
  unconstrained by `p`'s probability mass
- The witness is the degenerate type, not the dominant type

The docstring at line 386 explicitly documents this: *"δ is unused in the conclusion
— this is weaker than the true source coding theorem (which requires covering
probability ≥ 1-δ). Proved via degenerate type."*

## Supporting Infrastructure (proved, dormant for Track B)

The following lemmas in the main file remain available and could be invoked by a
future Track B strengthening:

| Lemma                              | Statement (informal)                                        |
|------------------------------------|-------------------------------------------------------------|
| `type_class_size_eq_multinomial`   | |T_f| = n!/∏(fᵢ!)                                           |
| `count_types_le`                   | #(distinct empirical distributions) ≤ (n+1)^k               |
| `total_sequences_eq`               | k^n total sequences                                          |
| `dominant_type_lower_bound`        | ∃ type class with ≥ k^n / (n+1)^k sequences                 |
| `type_class_size_le_entropy_pow`   | |T_f| ≤ 2^(n·H(Q))                                          |
| `empEntropy_eq_shannonEntropy`     | bridge between empirical entropy and Shannon entropy         |
| `multinomial_le_entropy_pow`       | multinomial coefficient bounded by entropy power            |
| `type_class_partition`             | sequences partition into type classes                       |

These are **proved, axiom-free** and could be re-used by a Track B effort.

## Forward Levers (NOT a roadmap — Track A is shipped)

1. **Track B (strong achievability) remains open.** Replace
   `source_coding_achievability_mot` with the AEP-style statement covering
   probability ≥ 1 − δ. Requires product-measure machinery on `Fin n → Fin k`
   plus a concentration result (Chernoff/Hoeffding ≈ 150 LOC). Estimated total
   ≈ 300–500 LOC. The supporting-infrastructure table above gives the available
   levers — only the AEP step is missing.
2. **KL-divergence bridge.** `Mathlib.InformationTheory.KullbackLeibler.Basic`
   exposes `KullbackLeiblerFun`; for finite alphabets `H(p) = log(k) − D(p ‖ uniform)`,
   which could provide an alternate continuity argument and connect this file to
   Mathlib's information-theory API.
3. **Audit the "verified" badge.** The `meta.json` claims `status: "verified"` +
   `badge: "mathlib"`. The weak statement is mathematically true and proved, but
   the entry's *name* ("Shannon Source Coding") may oversell the formal content
   to a casual reader. Optional follow-up: add a `notes` field to meta.json
   pointing at the weak-statement caveat — this PR does not make that change
   to avoid widening scope beyond state.md.

## Active Approach

State synchronization only; no proof edits.

## Blockers

None. The Lean source builds, and Track A is closed. Track B is open work, not a
blocker.

## Next Action

If a researcher wants to pursue Track B: open a fresh branch and replace
`source_coding_achievability_mot` with the strong AEP statement using the
supporting infrastructure above. The Track A version can either be kept as
`source_coding_achievability_mot_weak` or replaced outright.

## Honesty Block

- This is a doc-only state.md refresh — no `.lean`, no `meta.json`, no
  `annotations.json`, and no Mathlib symbol was modified.
- "Phase: COMPLETED-WEAK" describes the saturated state of the Track A scope;
  it explicitly does NOT claim the genuine Shannon source coding theorem
  (probability-mass coverage form) is proved. That is the unbuilt Track B.
- Counts above were verified by `grep`/`wc` against the Lean files at HEAD.
- `meta.json` `status: "verified"` reflects that the weak statement compiles
  without sorry or axiom. It does not reflect the strength of the proof.

## Attempt Counts

- Total attempts (cumulative): 4 sessions + Track A discharge + STATE-SYNC (this PR)
- Current approach attempts: STATE-SYNC iteration (this PR)
- Approaches tried (cumulative): combinatorial method-of-types infrastructure (proved);
  degenerate-type witness for the weak achievability statement (proved, Track A);
  AEP/Chernoff strengthening (open, Track B)
