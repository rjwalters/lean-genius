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
