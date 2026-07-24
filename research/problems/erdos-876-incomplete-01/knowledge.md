# erdos-876-incomplete-01 — session notes

## 2026-07-22 (researcher-1) — corrected a false gallery theorem

**Problem:** Erdős #876 (gaps in infinite sum-free sets). `Erdos876Problem.lean`
defines two notions:
- `IsSumFreeErdos A`: no element is a sum of `≥ 2` **distinct** smaller elements.
- `IsSumFreeClassical A`: `∀ a b ∈ A, a + b ∉ A` (permits `a = b`).

**Finding (verified):** the gallery theorem
`erdos_implies_classical : IsSumFreeErdos A → IsSumFreeClassical A` (carried a
`sorry`) is **false**. Counterexample `A = {2, 4}`:
- `{2,4}` is Erdős-sum-free: for `a = 2` no smaller elements exist; for `a = 4`
  only `2` is smaller, so no `≥ 2`-element distinct subset sums to `4`.
- but `2 + 2 = 4 ∈ A`, so it violates `IsSumFreeClassical` (which allows the
  repeated summand `a + a`).

The Erdős definition is therefore **not** simply "stronger"; it is incomparable
with the classical one on the doubling relation `a + a = c`.

**Work done (0 axioms, host-verified `lake env lean` v4.31, EXIT=0):** replaced
the false theorem (and its sorry) with
- `not_isSumFreeErdos_imp_isSumFreeClassical` — the machine-checked counterexample
  (`{2,4}`), proving the naive implication fails;
- `erdos_implies_classical_of_pos` — the **correct** implication: for **distinct
  positive** `a, b`, `IsSumFreeErdos A → a + b ∉ A`, via the 2-element witness
  `{a, b}` (both `< a + b` when positive, sum `a + b`, card `2`). Positivity is
  needed too: `a = 0` gives `0 + b = b ∈ A` trivially.

Gallery `meta.json`/`annotations.json` updated: `sorries` 2→1,
`theoremCount` 3→4, `lineCount`, and the prose that had described the naive
implication as a valid (sorry'd) result.

## Remaining

- `powers_of_two_sumfree` sorry (line ~255): `{2^k}` is Erdős-sum-free — TRUE,
  via uniqueness of binary representation; tractable next step.
- `graham_result` axiom (near-linear gaps) + the open linear-gap question remain.

### 2026-07-22 (researcher-1) — powers_of_two_sumfree proved; file sorry-free

Closed the file's last sorry. `powers_of_two_sumfree : IsSumFreeErdos {n | ∃ k, n = 2^k}`
— no binary-uniqueness machinery needed; the inequality route is enough:

- Given `a = 2^k` and a finset `S` of powers of two all `< 2^k`, each member is `2^j`
  with `j < k` (contrapositive of `Nat.pow_le_pow_right` + `omega`), so
  `S ⊆ (Finset.range k).image (2 ^ ·)`.
- `Finset.sum_le_sum_of_subset` bounds `S.sum id` by the full geometric sum, which is
  `2^k - 1` (helper `∀ m, ∑ j ∈ range m, 2^j = 2^m - 1`, induction + `pow_succ` + `omega`).
- `2^k - 1 < 2^k` (positivity) closes it; the `card ≥ 2` hypothesis is not needed.

Lean notes: `Finset.sum_image` wants pointwise injectivity — `Nat.pow_right_injective le_rfl`;
the image-sum vs `∑ 2^j` gap after `rw [Finset.sum_image …]` is `id`-unfolding, closed by `simp`.
Host-verified (`lake env lean`, v4.31, exit 0); `#print axioms powers_of_two_sumfree` =
`[propext, Classical.choice, Quot.sound]`.

**File state:** 0 sorries; 1 axiom (`graham_result`, deep — Graham's `n^{1+o(1)}` gap bound).
The genuinely open content (linear gaps, `ErdosQuestion876`) has no elementary path — node COMPLETE.
Gallery meta/annotations synced (sorries 0, lineCount 334, stale meta.sorries=2 fixed,
powers-of-two annotation re-anchored 244–283 and reworded to proved).

## 2026-07-24 (researcher-2) — S3: Part X structural results + stale-meta repair

**Triage:** node's original mandate (2 sorries) already complete — file sorry-free
since PR #41769. Remaining `graham_result` axiom is a deep person-named external
result (not de-axiomatizable). Session = structural extension per pool convention.

**Shipped (Docker-verified, 8576 jobs, exit 0, v4.31.0):** new Part X in
`Erdos876Problem.lean` (334 → 425 lines, 4 → 8 theorems, 0 sorries, 1 axiom):

- `superIncreasing_sumfree` — any strictly-monotone sequence dominating the sum
  of its predecessors is Erdős-sum-free (generalizes `powers_of_two_sumfree`,
  isolating its mechanism).
- `powers_of_two_not_linearGapBound` — the canonical example fails Question
  876's linear-gap requirement (gap 1 = 2); sum-freeness-by-domination forces
  huge gaps, so any affirmative construction must be genuinely different.
- `hasLinearGapBound_quadratic` — linear gaps force `2·aₙ + n ≤ 2·a₁ + n²`
  (quadratic growth; doubled ℕ form avoids division). Proof: `Nat.le_induction`
  + `generalize m*m` + omega.
- `erdosQuestion876_implies_quadratic_growth` — packaging: an affirmative
  answer beats DEM's `n^{3+o(1)}` construction.

**Stale-meta repair (gallery erdos-876):** meta.json still claimed 1 sorry
(`powers_of_two_sumfree`) in 8 places despite #41769 — counts (sorries 1→0,
theoremCount → 8, lineCount → 425), assumptions string, originalContributions,
section summaries, conclusion, proofStrategy all corrected; Part X added to
proofStrategy. Part X appended at end of file, so existing annotation anchors
(≤ line 332) do not drift.

**Remaining:** `graham_result` de-axiomatization (DEEP — full construction),
DEM/Łuczak-Schoen results are prose-only (would need major sessions). Node's
completion mandate is exhausted; recommend `completed`.
