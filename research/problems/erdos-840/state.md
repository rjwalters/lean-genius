# Current State

**Phase**: ACT (S2 ACT shipped 2026-06-09 by researcher-5)
**Since**: 2026-04-21 (S1 ACT — initial formalization) → 2026-06-09 (S2 ACT)
**Iteration**: 2

## S2 ACT (2026-06-09, researcher-5) — discharge `unordered_pairs_card` sorry

**Mode**: ACT (Lean sorry → proven theorem).

**Outcome**: Replaced the `sorry` on `unordered_pairs_card` in
`Erdos840Aristotle.lean` with a complete proof via the swap-bijection argument.

### Mathematical content

Goal: `((A ×ˢ A).filter fun p => p.1 < p.2).card = A.card.choose 2`

Proof sketch (~50 LOC):

1. Let `L` = strict-lt pairs, `G` = strict-gt pairs.
2. `L ∪ G` coincides with `(A ×ˢ A).filter (· ≠ ·)` and is disjoint, so
   `|L ∪ G| = |L| + |G|`.
3. By the already-proven `card_ordered_pairs`,
   `|(A ×ˢ A).filter (· ≠ ·)| = |A| * (|A| - 1)`.
4. Swap bijection `(a, b) ↦ (b, a)`: `G = L.image swap`, swap is injective,
   so `|G| = |L|`.
5. Therefore `2 * |L| = |A| * (|A| - 1)`.
6. By the already-proven (private) `two_mul_choose_two`,
   `2 * A.card.choose 2 = |A| * (|A| - 1)`.
7. `omega` closes: `|L| = A.card.choose 2`.

### Why this proof, not the powersetCard-bijection route

The natural alternative is to biject lt-pairs with 2-element subsets of `A`
and use `Finset.card_powersetCard`. That route requires reasoning about
`Finset` extensionality on doubletons (`{a, b} = {c, d}` with `a<b, c<d`
implies `a=c, b=d`), which is hairier in Lean 4 than the symmetric-counting
argument above. The chosen proof reuses two lemmas already proven in this
file (`card_ordered_pairs`, `two_mul_choose_two`) — no new infrastructure.

### What landed

- `proofs/Proofs/Erdos840Aristotle.lean` — `unordered_pairs_card` replaces
  `:= by sorry` with the full ~50-LOC proof; doc-comment rewritten to
  describe the swap-bijection strategy. Sorry count 2 → 1 (only
  `sidon_card_le_sqrt` remains).
- `src/data/research/problems/erdos-840.json` — phase ACT (iter 1) → ACT (iter 2);
  refreshed `progressSummary` / `builtItems` / `insights` / `nextSteps`.
- `src/data/proofs/erdos-840/meta.json` (if present) — refresh `sorryCount`
  and `theoremCount`.
- `state.md` (this new file) — initial creation; phase ACT, iter 2.

### Docker build status

**Docker build: PASSED** (7743 jobs, 388s build of `Proofs.Erdos840Aristotle`).
Only one warning: `Erdos840Aristotle.lean:240:8: declaration uses 'sorry'`,
which is the remaining `sidon_card_le_sqrt` we explicitly defer. The new
`unordered_pairs_card` proof compiles cleanly.

Final file size: 193 → 242 lines (+49 lines for the proof body).

### Lean delta

- 0 new theorems by signature (the sorry was already declared as a `theorem`)
- 1 sorry discharged (`unordered_pairs_card` was the cleaner of the two
  remaining sorries in the Aristotle file)
- 0 new axioms
- Net: −1 sorry in `Erdos840Aristotle.lean`

### Remaining sorries / axioms

**Aristotle file** (1 sorry remaining):
- `sidon_card_le_sqrt` (line 191): `|A| ≤ √(2N) + 1` for Sidon `A ⊆ {1..N}`.
  Proof requires the "distinct differences" argument: the C(k,2) positive
  differences lie in {1, …, N-1}, giving k*(k-1)/2 ≤ N-1, hence the bound.
  This needs `IsSidon → distinct differences` (substantive) and
  `Real.sqrt` arithmetic to invert the quadratic — heavier than this S2 step.

**Problem file** (8 axioms, unchanged):
- `sidon_sumset_card`, `erdos_freud_lower_bound`, `construction_is_quasi_sidon`,
  `erdos_freud_upper_bound`, `pikhurko_upper_bound`, `pikhurko_constant_approx`,
  `sidon_set_upper_bound`, `sidon_set_exists` — all research-level results
  correctly axiomatized per the gallery's axiomatization policy.

## Active Approach

Continue closing Aristotle-file sorries via direct Lean proofs that don't
depend on research-level results.

## Blockers

- `sidon_card_le_sqrt` needs an intermediate "Sidon ⇒ distinct differences"
  lemma plus `Real.sqrt` quadratic inversion. ~80-120 LOC; deferred.

## Next Action

**S3 ACT (future)**: prove `sidon_card_le_sqrt` via differences-argument:

```lean
theorem sidon_card_le_sqrt (A : Finset ℕ) (N : ℕ) (hN : N ≥ 1)
    (hA : ∀ a ∈ A, a ≤ N) (hS : IsSidon' A) :
    (A.card : ℝ) ≤ Real.sqrt (2 * N) + 1 := by
  -- Step 1: define differences set D = {a - b : a, b ∈ A, b < a}
  -- Step 2: show D has cardinality C(|A|, 2) (Sidon distinctness)
  -- Step 3: D ⊆ Finset.Icc 1 N
  -- Step 4: C(|A|, 2) ≤ N, i.e. k*(k-1)/2 ≤ N
  -- Step 5: solve quadratic: k ≤ √(2N) + 1
```

Expected ~100-150 LOC + Docker build.

## Honesty

This S2 ACT iteration eliminates one sorry from the Aristotle file via a
self-contained proof that reuses two lemmas already established in the same
file. The proof is not novel mathematics — it is a standard "double counting
of ordered pairs vs unordered pairs" argument that any combinatorics text
states in one line. The contribution is the careful Lean encoding, especially
the `Finset.image` + injectivity bridge for the swap bijection.

Mathlib likely has this identity under a different name (some variant of
`Finset.card_powersetCard`-derived); I did not attempt to track it down
because the local-reuse proof is ~50 LOC and self-contained, and the
gallery's policy prefers self-contained Aristotle helpers over chained
Mathlib invocations for clarity.
