# Knowledge: collatz-cycles-oq-03

## Parent Inventory (`Proofs/CollatzCycles.lean`)

256 lines, 4 definitions, 27 theorems, 0 sorries, 0 axioms, status `verified`.

### Definitions

| Line | Decl | Statement |
|------|------|-----------|
| 30 | `collatz` | `n → n/2 if even, 3n+1 if odd` |
| 47 | `collatzIter` | `collatz^[k]` |
| 50 | `IsPeriodic` | `k ≥ 1 ∧ collatzIter k n = n` |
| 194 | `ReachesOne` | `∃ k, collatzIter k n = 1` |

### Key Lemmas Available for OQ-03 S2

| Line | Decl | Statement |
|------|------|-----------|
| 37 | `collatz_even` | `n % 2 = 0 → collatz n = n / 2` |
| 40 | `collatz_odd` | `n % 2 = 1 → collatz n = 3 * n + 1` |
| 117 | `collatz_odd_growth` | `n % 2 = 1 → n ≥ 1 → collatz n > n` |
| 122 | `collatz_even_decrease` | `n % 2 = 0 → n ≥ 2 → collatz n < n` |

### What the Parent Does NOT Prove

- No explicit `collatz_of_odd_is_even` lemma (`n % 2 = 1 → (collatz n) % 2 = 0`).
- No `cycle_contains_even` / `no_all_odd_cycle` statement.
- No iteration-level parity tracking (i.e. nothing about
  `(collatzIter i n) % 2` as a function of `i`).

These are exactly the OQ-03 deliverables.

## Lean Skeleton (S2 ACT Recommended Plan)

New file `proofs/Proofs/CollatzCyclesOQ03.lean` (~50 lines):

```lean
/-
# Collatz Cycles OQ-03: No All-Odd Cycle

For the parent `Proofs/CollatzCycles.lean`, this companion file proves the
parity intersection corollary: every Collatz cycle visits at least one even
number. The proof is two omega steps from the parent's `collatz_odd` lemma.
-/

import Mathlib.Tactic
import Proofs.CollatzCycles

namespace CollatzCycles

/-- Parity flip: `3n+1` is even when `n` is odd. -/
lemma three_n_plus_one_even {n : ℕ} (h : n % 2 = 1) :
    (3 * n + 1) % 2 = 0 := by omega

/-- For odd `n`, `collatz n` is even. -/
theorem collatz_of_odd_is_even {n : ℕ} (h : n % 2 = 1) :
    (collatz n) % 2 = 0 := by
  rw [collatz_odd h]; exact three_n_plus_one_even h

/-- **No all-odd Collatz cycle.** If every iterate of `n` up to step `k` is
    odd and `collatz^k(n) = n`, then we have a contradiction. -/
theorem no_all_odd_cycle {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1)
    (hper : collatzIter k n = n)
    (hodd_all : ∀ i, i < k → (collatzIter i n) % 2 = 1) : False := by
  /- Strategy: i = 0 gives n odd. Apply collatz_of_odd_is_even to get
     (collatz n) % 2 = 0, i.e. (collatzIter 1 n) % 2 = 0. Two cases:
     - k ≥ 2: hodd_all 1 hk2 says (collatzIter 1 n) % 2 = 1 — contradicts above.
     - k = 1: then collatzIter 1 n = n and n odd, but collatzIter 1 n is even.
  -/
  have h0 : n % 2 = 1 := by
    have := hodd_all 0 hk
    simpa [collatzIter] using this
  have h1 : (collatzIter 1 n) % 2 = 0 := by
    simp [collatzIter, Function.iterate_one]
    exact collatz_of_odd_is_even h0
  rcases Nat.lt_or_ge 1 k with hk2 | hk1
  · -- k ≥ 2: parity contradicts at step 1
    have := hodd_all 1 hk2
    omega
  · -- k = 1: collatzIter 1 n = n, so n is even (from h1) and odd (from h0)
    interval_cases k
    have heq : collatzIter 1 n = n := hper
    have : n % 2 = 0 := heq ▸ h1
    omega

/-- **Positive form.** Every Collatz cycle visits at least one even number. -/
theorem cycle_contains_even {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1)
    (hper : collatzIter k n = n) :
    ∃ i, i < k ∧ (collatzIter i n) % 2 = 0 := by
  by_contra hne
  push_neg at hne
  apply no_all_odd_cycle hn hk hper
  intro i hi
  have := hne i hi
  omega

/-- The `IsPeriodic` packaging. -/
theorem isPeriodic_contains_even {n k : ℕ} (hn : n ≥ 1)
    (hper : IsPeriodic n k) :
    ∃ i, i < k ∧ (collatzIter i n) % 2 = 0 :=
  cycle_contains_even hn hper.1 hper.2

end CollatzCycles
```

### Why the Skeleton Should Build Clean

- All imports come from `Mathlib.Tactic` (omega) and the parent.
- `Function.iterate_one`: standard, in `Mathlib/Logic/Function/Iterate`.
- `simp [collatzIter]` unfolds the definition.
- `omega` discharges all parity goals once we have the right inequalities.

### Risk: `simp [collatzIter]` Loop

If `collatzIter` unfolds eagerly through subsequent iterates, `simp` can
loop. Fallback: explicit `show` annotation:

```lean
have h0 : n % 2 = 1 := by
  show (collatz^[0] n) % 2 = 1
  simp [Function.iterate_zero]
  exact hodd_all 0 hk
```

## Mathlib API Inventory

No new Mathlib API is needed. Required imports:

| Module | What it provides |
|--------|------------------|
| `Mathlib.Tactic` | `omega`, `simp`, `rcases`, `push_neg`, `interval_cases` |
| `Proofs.CollatzCycles` | `collatz`, `collatzIter`, `collatz_odd`, `collatz_even` |
| `Mathlib.Logic.Function.Iterate` (transitive) | `Function.iterate_one`, `Function.iterate_zero` |

No Aristotle submission is needed: the proof is short enough to do by hand.

## Mathlib Gaps

**None.** All required lemmas are either in the parent or in core Mathlib
tactics.

## Cross-Impact

This OQ closes a narrow gap. It does **not** unblock:

- Larger Collatz cycle eliminations (those need `2^M > 3^j` machinery,
  parent Part VI).
- The Collatz conjecture itself.
- Other `collatz-*` OQs.

It **does** provide:

- A clean parity-corollary lemma usable by future Collatz iteration
  enumerators (decidable cycle search).
- A pedagogical anchor for the "every cycle has both parities" fact,
  which is currently implicit in the parent but not stated.

## Aristotle Strategy

**Do not submit.** The proof is hand-trivial; submitting wastes Aristotle
budget on a sub-five-line goal that `omega` closes immediately.

## Honesty Calibration

- **Difficulty**: trivial (2 omega steps after one rewrite).
- **Novelty**: zero — this is standard textbook parity.
- **Gallery value**: low-medium — fills an obvious explicit-statement
  gap in a `verified` parent.
- **Mathlib value**: none — these are project-internal lemmas, not
  general enough for Mathlib.

The reason this work is worth doing: the parent currently *implicitly*
relies on this fact (e.g. when discussing the `2^M > 3^j` constraint
in Part VI's docstrings) but never makes it explicit. S2 + S3 deliver
the explicit lemma plus a gallery entry, closing the OQ.

## Log

- 2026-05-12 (researcher-5, S1 OBSERVE): claimed slug (was added by seeker
  2026-05-12T09:56:28Z, 4h old, 0 prior PRs); surveyed parent file; drafted
  Lean skeleton; classified as TRIVIAL; recommended S2 ACT next.
