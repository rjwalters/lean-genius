# Session 2026-06-04 (Session 2) — General lower bound S(k) ≥ 3

**Mode**: ACT (RICH, knowledge score 15, MODERATE+)
**Outcome**: completed (4 new theorems, +52 LOC, 0 sorries, 0 axioms)

## What I Did

Added a general lower bound complementing the existing trivial upper bound:

- **`smoothBlockSet_empty_of_ge_two_le_one`** — For k ≥ 2 and x ≤ 1, smoothBlockSet k x = ∅
  (Generalizes private k=2 lemma via `smoothBlockSet_antitone`)
- **`smoothBlockSet_two_sub_zero_of_ge_two`** — For k ≥ 2, smoothBlockSet k 2 ⊆ {0}
  (Generalizes private k=2 lemma via `smoothBlockSet_antitone`)
- **`upperDensity_empty`** — Upper density of ∅ is 0
- **`smoothThreshold_ge_three`** — For k ≥ 2, smoothThreshold k ≥ 3
  (Combined with `trivial_upper`, gives 3 ≤ S(k) ≤ k+1 for k ≥ 2)

Also fixed two pre-existing parse errors (orphan docstrings on lines 255-258 — `/-- ... -/`
without an attached declaration). Converted to plain `/- ... -/` comments. Build was
silently failing — these errors weren't visible at the surface but caused docker build
exit code 139 (initially) and exit code 1 after retry surfaced them.

Also fixed a deprecation warning: `Set.eq_empty_iff_forall_not_mem` →
`Set.eq_empty_iff_forall_notMem`.

## Key Findings

- `Nat.le_find_iff` is the dual of `Nat.find_eq_iff`: `k ≤ Nat.find h ↔ ∀ n < k, ¬ p n`.
  Used to convert the lower bound goal into case analysis on x ∈ {0, 1, 2}.
- The `smoothBlockSet_antitone` lemma cleanly lifts k=2 emptiness/subset results to
  k ≥ 2: smoothBlockSet k x ⊆ smoothBlockSet 2 x for k ≥ 2.
- `upperDensity_empty` follows immediately from `Filter.limsup_const` once the
  filter range filter is identified as ∅ (then card = 0, ratio = 0).
- Build process: Lean 4.26.0 with `Set.eq_empty_iff_forall_not_mem` is deprecated;
  use `notMem` (camelCase).

## Files Modified

- `proofs/Proofs/Erdos929Problem.lean` (377→429 lines, +4 theorems, fixed 2 parse errors + 1 deprecation)
- `src/data/proofs/erdos-929/meta.json` (lineCount 377→429, theoremCount 19→23)

## Status

- 0 sorries, 0 axioms (unchanged)
- 23 theorems (was 19), 7 definitions (unchanged)
- Known bounds: trivial upper (S(k) ≤ k+1), monotonicity (S monotone), specific
  S(2)=3, and now **general lower bound S(k) ≥ 3 for k ≥ 2**.

## Next Steps

- The main conjecture S(k) ≥ k^{1−o(1)} remains open and requires sieve-theory
  infrastructure not yet in Mathlib.
- A possible incremental next step: prove S(3) = 3 specifically (the AP n ≡ 1 mod 6
  has 3 ∣ n+1, 2 ∣ n+2 (wait, no — n+1 = 6t+2, 6t+3, 6t+4), all with minFac ≤ 3).
  Together with `smoothThreshold_ge_three`, that would close out S(3).
