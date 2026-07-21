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

## Session 2026-07-20 (researcher-1) — exponential richness of prime sets (0-axiom)

**Mode**: FRESH (greenfield WIP node; parent rich, no prior WIP file) · **Outcome**:
new axiom-free file `Erdos53WIP01.lean`, host-verified under v4.31.

The parent `Erdos53Problem.lean` (405 L, 0-axiom) already proves the k=1 base case,
the trivial `2^{|A|+1}` upper bracket, distinct-prime **product** richness
`|subsetProducts A| = 2^{|A|}-1` (`subsetProducts_card_of_prime`), and
superincreasing subset-sum injectivity `|subsetSums A| = 2^{|A|}`.

**New content.** The additive side contributes exactly one value the multiplicative
side cannot: `0` (the empty subset sum), which is never a product of positive primes
(`subsetProducts_pos_of_prime`: every subset product of positive primes is `> 0`).
Adjoining it to the `2^{|A|}-1` distinct positive products gives:

- `sumsOrProducts_card_ge_two_pow_of_prime`: `2^{|A|} ≤ |sumsOrProducts A|` for
  distinct positive primes. The strongest witness on the EASY direction of Problem
  53 — the representable count is *exponential*, dwarfing every `|A|^k`.
- `sumsOrProducts_card_prime_pinned`: with the parent upper bracket, prime sets are
  pinned in `[2^{|A|}, 2^{|A|+1}]`.
- `sq_le_two_pow`: `n^2 ≤ 2^n` for `n ≥ 4` (elementary induction, no analysis).
- `erdosProblem53_prime_of_dominates` / `erdosProblem53_prime_exponent_two`: honest
  conditional — on prime sets `|A|^k ≤ |sumsOrProducts A|` the moment `|A|^k ≤ 2^{|A|}`;
  instantiated for `k = 2`, `N₀ = 4` (first superlinear instance, unconditional on primes).

**Honesty.** This bears only on the easy direction. Chang's theorem is the uniform
`|A|^k` bound over ALL large `A` (not just primes); the prime family is never the
obstruction. Chang's theorem stays documented, not axiomatized.

**Verification.** Parent is Mathlib-only, so host-verified without Docker via the
fresh-parent-olean path: `bin/lake exe cache get`, build
`Proofs/Erdos53Problem.olean` into `.lake/build/lib/lean/Proofs/`, then
`bin/lake env lean Proofs/Erdos53WIP01.lean` → exit 0, no errors/warnings.
`#print axioms` on the three headline theorems = `[propext, Classical.choice,
Quot.sound]` (axiom-free).

### Files modified
- `proofs/Proofs/Erdos53WIP01.lean` (new)
