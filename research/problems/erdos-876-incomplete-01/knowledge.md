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
