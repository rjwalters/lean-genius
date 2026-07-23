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

## Session 2026-07-21 (researcher-1) — general poly-vs-exp domination (arbitrary exponent k)

Added 2 axiom-free theorems to `Erdos53WIP01.lean` (theoremCount 7→9; host-verified v4.31
via fresh parent olean + `lake env lean`, exit 0; `#print axioms` =
propext/Classical.choice/Quot.sound on both). Generalises the `k=2` chain
(`sq_le_two_pow` / `erdosProblem53_prime_exponent_two`) to **all** exponents:

- `exists_pow_le_two_pow (k) : ∃ N, ∀ n ≥ N, n^k ≤ 2^n` — the eventual polynomial-vs-
  exponential domination for every k, replacing the explicit `n≥4` threshold of the
  hand-rolled `sq_le_two_pow`. Route: `isLittleO_pow_const_const_pow_of_one_lt k (1<2)`
  gives `(n:ℝ)^k =o[atTop] (2:ℝ)^n`; `IsLittleO.eventuallyLE` + `eventually_atTop` extract
  a threshold N with `‖(n:ℝ)^k‖ ≤ ‖(2:ℝ)^n‖`; strip norms (`abs_of_nonneg`, both sides
  nonneg) and `exact_mod_cast` back to ℕ.
- `erdosProblem53_prime_exponent_eventually (k) : ∃ N, ∀ A (distinct pos primes), |A|≥N →
  |A|^k ≤ |sumsOrProducts A|` — the Problem-53-on-primes statement for arbitrary polynomial
  degree, via `erdosProblem53_prime_of_dominates` + the domination above. So the prime
  family unconditionally exhibits every polynomial growth rate of `|sumsOrProducts A|`.

### Import note
Added `import Mathlib.Analysis.SpecificLimits.Normed` to the WIP file (parent imports only
Nat/Int/Finset); needed for `isLittleO_pow_const_const_pow_of_one_lt`. Host-verify is
unaffected (Mathlib oleans cached); no docker.

### Frontier (UNCHANGED)
Chang's theorem (the |A|^k bound for *arbitrary* large A, not just primes) stays documented,
not axiomatized — it needs additive-combinatorics machinery (Freiman/Plünnecke) absent here.
The prime family is now fully handled for all k.

## Session 2026-07-22 (researcher-1) — quadratic additive bound for arbitrary positive sets

Added 8 axiom-free theorems to `Erdos53WIP01.lean` (theoremCount 11→19, 294→476 lines;
host-verified v4.31 via fresh-parent-olean path, exit 0; `#print axioms` on all four
headline theorems = propext/Classical.choice/Quot.sound).

**The point.** Every previous bound in the development is prime-family-specific (the
exponential richness lives on the multiplicative side). This session proves the first
bound whose scope matches Problem 53's "arbitrary large A" quantifier (restricted to
positive elements): the classical Erdős subset-sums chain.

- `subsetSums_card_quadratic` / `subsetSums_card_ge_quadratic('`)`: for ANY set of n
  distinct positive integers, `n(n+1) + 2 ≤ 2·|subsetSums A|`, i.e.
  `|subsetSums A| ≥ n(n+1)/2 + 1` (sharp for {1,…,n}). Induction on n removing
  `m = max A`: every subset sum of `A' = A.erase m` is `≤ T − m` (`T = Σ A`,
  `mem_subsetSums_le_sum` + `sum_erase_eq_sub`), while the n values
  `{T} ∪ {T − a : a ∈ A'}` are distinct subset sums strictly above `T − m`
  (distinct by `sub_right_injective`; above by `a < m` from `le_max'` + erase-ne).
  Disjoint-union card count adds n per step; triangular number accumulates.
- `sumsOrProducts_card_ge_quadratic`: same bound for the full representable set —
  quadratic growth over ALL positive sets, beating the linear
  `card_le_sumsOrProducts` by a factor ~|A|/2.
- `sumsOrProducts_card_superlinear (C)`: explicit threshold `N = 2C` past which
  `C·|A| ≤ |sumsOrProducts A|` — the k=1 case of Problem 53 with any prescribed
  linear rate, on all positive sets.

**Lean notes.** `Finset.sum_erase_eq_sub` needs a trailing `id_eq` rewrite (id a vs a
not closed by rw's rfl). `Finset.card_erase_of_mem` leaves `n+1−1 = n` (ℕ sub) — close
with omega. Avoided `Finset.erase_subset` signature drift by using
`fun x hx => Finset.mem_of_mem_erase hx` inline. Final arithmetic (triangular-number
step and superlinearity) via `nlinarith` with an explicit `Nat.mul_le_mul_right` hint.

**Honesty.** `n(n+1)/2 + 1 < n²` for `n ≥ 3`: even the k=2 case of Problem 53 over
arbitrary sets remains untouched. Chang's theorem stays documented, not axiomatized.
This widens the unconditional frontier (primes → all positive sets) at polynomial
degree ~2/2, it does not approach the uniform |A|^k crux. Negative elements also
untouched (the chain needs positivity for the total-sum upper bound).

### Files modified
- `proofs/Proofs/Erdos53WIP01.lean` (+182 lines, 8 theorems)
- `src/data/research/problems/erdos-53-wip-01.json`

## Session 2026-07-23 (researcher-1) — multiplicative Erdős chain (product-side quadratic)

`subsetProducts_card_quadratic`: |subsetProducts A| ≥ n(n+1)/2 for ARBITRARY
finite A ⊆ ℤ with all elements > 1. Mirror of the additive chain (same
max-removal induction), transposed division-free:

- Fresh values: {Π A} ∪ {Π(A.erase a) : a ∈ A.erase m} — never written P/a.
- Recombination law `hRmul : Π(A.erase a) · a = Π A` (Finset.prod_erase_mul)
  drives everything: injectivity via mul_left_cancel₀, strict separation
  Q < Π(A.erase a) via Q·a < Q·m = Π(A.erase a)·a then lt_of_mul_lt_mul_right.
- Subset-product ≤ full-product: prod_dvd_prod_of_subset + Int.le_of_dvd
  (ℤ's multiplicative monoid is NOT ordered — Finset.prod_le_prod_of_subset_
  of_one_le' does not apply to ℤ; divisibility+positivity is the correct route).
- Hypothesis 1 < a essential (1 ∈ A ⟹ Π(A.erase 1) = Π A, injectivity dies);
  0 excluded a fortiori. Additive chain needed only 0 < a.
- No +1 in the bound: subsetProducts filters out the empty subset.
- Sharp: {2,4,…,2^n} products = 2^s, s ∈ [1, n(n+1)/2] (remark, not formalised).

Lean gotchas (new this session):
- Set.InjOn intro gives SET-coe memberships; convert with Finset.mem_coe.mp
  before feeding Finset lemmas (or `have ha' : a ∈ A' := ha` — defeq works).
- InjOn's hab `(fun a => …) a = (fun a => …) b` is NOT beta-reduced for rw;
  materialise `have hab' : Π(A.erase a) = Π(A.erase b) := hab` first.
- rw-order trap: rewriting haeq (R = P) before hRmul (R·a = P) destroys the
  R·a pattern — order [mul_one, hRmul, haeq] not [mul_one, haeq, hRmul].

Elementary vein now fully SATURATED (both sides individually quadratic).
Remaining: Chang |A|^k (deep); thin maybe-rung: negatives in the additive
chain (subset sums collide across sign — likely needs |·| tricks, assess
before attempting).
