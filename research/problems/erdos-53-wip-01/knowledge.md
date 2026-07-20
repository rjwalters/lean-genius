# Knowledge Base: erdos-53-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session note (2026-07-20, researcher-1): 12 axiom-free foundational lemmas

`Erdos53Problem.lean` (sum-product / Erdős–Szemerédi Problem 53) was a definitions-only
stub (9 defs, 0 theorems). Added 12 axiom-free foundational lemmas (host-verified, Lean
v4.31.0; `#print axioms` = propext/Classical.choice/Quot.sound): subset-sum/product
membership (`0` and each element), inclusions into `sumsOrProducts`, `subsetSums_card_le`
(≤ 2^|A|), `subsetSums_mono`, the count-domination lemmas, `sumset_card_le`/`productset_card_le`
(≤ |A|²), and `subsetSums_empty` ({0}). Chang 2003 (conjecture holds) and the Erdős–Szemerédi
upper bound remain documented-only — they need additive combinatorics beyond Mathlib.
Meta synced (theoremCount 0 → 12, lineCount 116 → 197).

---

## Session 2026-07-20 (researcher-1): k=1 base case + distinct-prime richness

Batch 2 of axiom-free lemmas added to `Proofs/Erdos53Problem.lean` (Section 8),
raising the theorem count 12 → 24, still 0 axioms. Host-verified with
`lake env lean` (Mathlib-only imports); `#print axioms` on every new headline
theorem yields only `[propext, Classical.choice, Quot.sound]`.

Key results (mechanism, not wording):

- **k=1 base case (`erdosProblem53_exponent_one`)**: `A ⊆ subsetSums A ⊆
  sumsOrProducts A` gives `|A| ≤ |sumsOrProducts A|`, i.e. the `k=1` slice of the
  Erdős–Szemerédi lower bound holds with `N₀ = 0`. This is the *only* elementary
  instance of Problem 53; growth to `|A|^k` for `k ≥ 2` is Chang's deep theorem.
- **Distinct-prime richness (`subsetProducts_card_of_prime`)**: for a `Finset ℤ`
  of distinct **positive** primes, `|subsetProducts A| = 2^{|A|} - 1`. Proof =
  subset-product injectivity (`subsetProd_injOn_of_prime`): for a positive prime
  `p ∈ A`, `p ∈ S ↔ p ∣ ∏ S` (via `Prime.dvd_finsetProd_iff` +
  `Prime.associated_of_dvd` + `Int.associated_iff_natAbs`, with positivity
  killing the `p ↔ -p` collision that `Prime` alone allows over `ℤ`), so a
  nonempty subset is recovered from its product. Number of nonempty subsets =
  `2^{|A|} - 1` via `powerset.erase ∅`.
- **Trivial upper bracket (`sumsOrProducts_card_le`)**: `|sumsOrProducts A| ≤
  2^{|A|+1}`. Combined with the base case this pins the count in `[|A|,
  2^{|A|+1}]`; distinct-prime richness shows the multiplicative side of the upper
  bound is essentially attained.
- Missing `subsetProducts` analogues filled: `subsetProducts_empty`,
  `subsetProducts_card_le`, `subsetProducts_mono`; plus `sumsOrProducts_mono`,
  `zero_mem_sumsOrProducts`, `sumsOrProducts_nonempty`, `subset_subsetSums`.

### Insight
Positivity (not just `Prime`) is required for the ℤ richness lemma: `Prime`
over `ℤ` is closed under negation, so `{2, -2}` would collide on products
without the `0 < p` hypothesis. Stated with `hpos : ∀ p ∈ A, 0 < p`.

### Next targets
- Small concrete `decide` computations of `|sumsOrProducts A|` for explicit tiny
  `A` (problem.md item iii) — bounded by `2^{|A|}` powerset enumeration.
- Chang's theorem and the Erdős–Szemerédi subexponential upper bound remain
  genuinely deep (Balog–Szemerédi–Gowers, multiplicative energy) and out of
  Mathlib scope; keep documented, not axiomatized.
