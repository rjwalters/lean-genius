# Problem: Formalize Helfgott's proof of weak Goldbach without axioms

## Statement

### Plain Language

The parent gallery proof `weak-goldbach` (Weak Goldbach Conjecture, Helfgott
2013: every odd integer `n > 5` is a sum of three primes) is formalized in
`Proofs/WeakGoldbach.lean` (480 lines, 24 theorems, 0 sorries) but carries
**9 axioms** encoding the deep analytic ingredients of the proof.

This OQ asks whether — and how — these axioms can be progressively discharged
so that the gallery's `weak-goldbach` entry moves from `axiomatized` toward
`verified`. Full elimination is a multi-year effort; this OQ identifies the
tractable entry points and proposes a phased plan.

### Formal Statement

Eliminate the following 9 axioms in `Proofs/WeakGoldbach.lean` by replacing
each with a Lean-level proof or a stronger Lean-level construction:

```lean
axiom vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n
axiom helfgott_weak_goldbach : WeakGoldbachConjecture
axiom circle_method_asymptotic :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n →
      (representationCount n : ℝ) > (n : ℝ) ^ 2 / ((Real.log n) ^ 3 * 2) * (1 - ε)
axiom schnirelmann_basis_theorem (A : Set ℕ) [DecidablePred (· ∈ A)] :
    schnirelmannDensity A > 0 → ∃ h : ℕ, IsAdditiveBasis A h
axiom ramare_six_primes :
    ∀ n : ℕ, n ≥ 4 → Even n → ∃ primes : List ℕ, ...
axiom tao_five_primes :
    ∀ n : ℕ, n > 1 → Odd n → ∃ primes : List ℕ, ...
axiom chen_theorem :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Even n → ∃ p m, ...
axiom binary_goldbach_verified :
    ∀ n : ℕ, 4 ≤ n → Even n → n ≤ 4 * 10^18 → IsSumOfTwoPrimes n
axiom helfgott_explicit_bound :
    ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n
```

In addition to the 9 axioms, the parent file contains **2 theorem-level
placeholder stubs** that conclude with `True`:

```lean
theorem vinogradov_minor_arc_bound : ∀ A > 0, ∃ C > 0, ∀ N : ℕ, N ≥ 2 → True
theorem linnik_goldbach_representations : ∃ C > 0, ∀ n : ℕ, n ≥ 4 → Even n → True
```

and **1 placeholder definition**:

```lean
def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ := 0  -- placeholder
```

A "no axioms" goal includes giving real definitions for these as well.

## Classification

```yaml
tier: B
significance: 7
tractability: 5
tags:
  - seeker-selected
  - number-theory
  - goldbach
  - prime-sums
  - circle-method
  - schnirelmann-density
  - axiom-elimination
  - mathlib-Schnirelmann
```

**Significance**: 7/10 — Helfgott's proof is one of the most celebrated
results of analytic number theory in the last 30 years. A fully axiom-free
formalization would be a top-tier gallery entry and a non-trivial Mathlib
contribution (Schnirelmann basis theorem, Vinogradov's bound, the circle
method) — none of which currently exist in Mathlib v4.26.0.

**Tractability**: 5/10 — The full axiom-elimination is heroic (multi-year).
But there are *tractable entry points* (Approach A below) that can land in
1-3 sessions: replacing the placeholder `schnirelmannDensity` with Mathlib's
existing `Mathlib.Combinatorics.Schnirelmann.schnirelmannDensity`, proving
small numerical cases of `binary_goldbach_verified` via `decide`, and
upgrading the 2 `True`-stub theorems to bear genuine mathematical content
(even if the content remains modest).

## Why This Matters

1. **Single Mathlib-load-bearing path**. Of the 9 axioms, the Schnirelmann
   chain (`schnirelmannDensity` definition → `schnirelmann_basis_theorem`)
   is **explicitly on Mathlib's TODO list** at v4.26.0 (see
   `Mathlib/Combinatorics/Schnirelmann.lean` module docstring: *"Prove
   Schnirelmann's theorem and Mann's theorem on the subadditivity of this
   density"*). Closing this axiom is also a Mathlib contribution.

2. **Phased path to a verified flagship**. The 9 axioms naturally split
   into three feasibility tiers:
   - **TRACTABLE** (1-3 sessions each): Fix `schnirelmannDensity` placeholder,
     prove small-range `binary_goldbach_verified` (n ≤ 1000 via `decide`),
     give real content to the 2 `True`-stub theorems.
   - **INTERMEDIATE** (~6-12 months): Schnirelmann's theorem proper, the
     `IsAdditiveBasis` lifting argument. These are textbook results
     (Nathanson, *Additive Number Theory*).
   - **HEROIC** (multi-year): Vinogradov's exponential sum bound, the
     circle method asymptotic, Helfgott's 2013 paper, Chen's theorem,
     Tao's 5-prime, Ramaré's 6-prime.

3. **Companion gallery growth**. Each TRACTABLE/INTERMEDIATE deliverable
   can spawn its own gallery entry (Schnirelmann-density basic bounds;
   Mann's α + β theorem; Vinogradov's main term). The OQ tree under
   `weak-goldbach` can grow organically without ever needing to formalize
   Helfgott in full.

4. **First gallery entry to use `Mathlib.Combinatorics.Schnirelmann`**.
   Currently no gallery proof imports this Mathlib module. This OQ
   surfaces it as load-bearing.

## Known Results

### Already Proven (in parent `WeakGoldbach.lean`, 0 sorries)

- `goldbach_7, goldbach_9, goldbach_11, goldbach_21, goldbach_101`:
  Concrete verification by exhibiting decompositions.
- `isSumOfThreePrimesDecide_sound/_complete`: Decidable certificate for
  the ternary Goldbach representation.
- `binary_implies_weak`: Binary Goldbach ⟹ weak (ternary) Goldbach
  (constructive reduction, ~80 lines).
- `sumOfTwoPrimes_add_three`, `odd_gt_five_eq_three_plus_even`: Number-
  theoretic glue lemmas.
- `representationCount_pos_iff`: r₃(n) > 0 ↔ n is a sum of 3 primes.
- `singular_series_positive`: weak placeholder (∃ S > 0, currently `⟨1, one_pos⟩`).
- `vinogradov_from_circle_method`: Circle-method asymptotic ⟹ Vinogradov.
- `helfgott_improves_tao`: Weak Goldbach ⟹ Tao's 5-prime form (reduction).
- `binary_stronger_than_ternary`: Binary Goldbach ⟹ weak Goldbach.
- `levy_implies_weak_goldbach`: Lévy's conjecture ⟹ weak Goldbach.
- `levy_7, levy_9, levy_11`: Lévy verified for small odd integers.

### Axiomatized Results (9 axioms — this OQ targets)

| Axiom | Statement (short) | Source | Feasibility |
|-------|-------------------|--------|-------------|
| `vinogradov_ternary_goldbach` | Asymptotic ternary Goldbach (1937) | Vinogradov | HEROIC |
| `helfgott_weak_goldbach` | Helfgott's main 2013 result | Helfgott | HEROIC |
| `circle_method_asymptotic` | r₃(n) ∼ S(n)·n²/(2log³n) | Hardy-Littlewood | HEROIC |
| `schnirelmann_basis_theorem` | σ(A) > 0 ⟹ A is additive basis | Schnirelmann 1930 | INTERMEDIATE |
| `ramare_six_primes` | Every even n ≥ 4 is sum of ≤ 6 primes | Ramaré 1995 | HEROIC |
| `tao_five_primes` | Every odd n > 1 is sum of ≤ 5 primes | Tao 2014 | HEROIC |
| `chen_theorem` | Large even n = p + P₂ | Chen 1973 | HEROIC |
| `binary_goldbach_verified` | Binary Goldbach for n ≤ 4·10¹⁸ | Oliveira e Silva 2013 | TRACTABLE (small range) |
| `helfgott_explicit_bound` | Helfgott's explicit threshold 8.875·10³⁰ | Helfgott 2013 | HEROIC |

### Available Mathlib Infrastructure (pinned rev v4.26.0)

| Need | Mathlib name | Module |
|------|--------------|--------|
| Schnirelmann density (defined) | `schnirelmannDensity : Set ℕ → [DecidablePred] → ℝ` | `Mathlib.Combinatorics.Schnirelmann` |
| Basic bounds 0 ≤ σ(A) ≤ 1 | `schnirelmannDensity_nonneg`, `schnirelmannDensity_le_one` | `Mathlib.Combinatorics.Schnirelmann` |
| σ(A) = 0 if 1 ∉ A | `schnirelmannDensity_eq_zero_of_one_notMem` | `Mathlib.Combinatorics.Schnirelmann` |
| σ subadditive (Mann) | **MISSING** (on Mathlib TODO list) | n/a |
| Schnirelmann basis theorem | **MISSING** (on Mathlib TODO list) | n/a |
| Primality decidable | `Nat.decidablePrime`, `Nat.Prime` | `Mathlib.Data.Nat.Prime.Defs` |
| Prime counting function | `Nat.primeCounting` | `Mathlib.NumberTheory.PrimeCounting` |
| Circle integral / `e(x)` | `circleMap`, `Complex.exp_mul_I_add` | `Mathlib.Analysis.SpecialFunctions.Complex.Circle` |

### Open Sub-Questions (S2 candidates, sorted by tractability)

- **Q1 (TRACTABLE)**: Can the placeholder `def schnirelmannDensity ... := 0`
  in `Proofs/WeakGoldbach.lean` be replaced by an `import` of
  `Mathlib.Combinatorics.Schnirelmann` so the parent file uses Mathlib's
  real definition? Side effect: the axiom `schnirelmann_basis_theorem` becomes
  the only place σ is used non-trivially, and its statement now lines up
  with Mathlib's convention. (Approach A.)

- **Q2 (TRACTABLE)**: Can the 2 `True`-stub theorems
  (`vinogradov_minor_arc_bound`, `linnik_goldbach_representations`) be
  upgraded to bear genuine content — even modest — so the file no longer
  exposes "fake content" stubs? (Approach B.)

- **Q3 (TRACTABLE-small / HEROIC-full)**: For some explicit bound `B ≤ 10⁶`,
  can `binary_goldbach_verified` be proved for `n ≤ B` via `decide` /
  `native_decide`, replacing the all-n axiom with a finite-range theorem +
  an axiom restricted to `n > B`? This degrades but does not eliminate the
  axiom; full elimination requires Oliveira e Silva's 8-month CPU
  verification, which is out of scope. (Approach C.)

- **Q4 (INTERMEDIATE)**: Following Nathanson's *Additive Number Theory*
  Chapter 7, prove `schnirelmann_basis_theorem`: if `σ(A ∪ {0}) > 0` then
  for some `h`, every natural number is a sum of at most `h` elements of
  `A ∪ {0}`. The classical proof: from `σ(A) ≥ α > 0`, the sumset `2A`
  satisfies `σ(2A) ≥ 2α − α² = α(2 − α)`; iterating, after finitely many
  doublings `σ(2^k A) ≥ 1/2`; then the supplement to 1 finishes via
  pigeonhole. ~600 lines Lean, 3-6 sessions. (Approach D.)

- **Q5 (HEROIC, deferred)**: All other axioms — Vinogradov, circle method,
  Helfgott, Chen, Tao, Ramaré — require multi-month formalization efforts
  of well-known but technically dense analytic-number-theory results. Not
  S2-S5 candidates.

### Our Goal (S1 OBSERVE)

Survey the 9 axioms + 2 True-stub theorems + 1 placeholder definition;
classify each by feasibility tier; identify the most tractable S2 entry
points; map Mathlib's existing infrastructure. **Recommended S2: Approach A
(Mathlib `schnirelmannDensity` integration).** No Lean changes this S1.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `weak-goldbach` (parent) | The formalization with 9 axioms this OQ targets. |
| `infinitude-primes-4k1-oq-03`, `infinitude-primes-4k3-oq-03` | Arithmetic-progression prime distribution — shares circle-method / density flavor. |
| `bertrands-postulate` family | Classical prime-counting / sieve infrastructure that supports Schnirelmann-density arguments. |
| `prime-number-theorem-oq-*` | Selberg / Erdős-style prime distribution — pre-Vinogradov techniques relevant to the lower-tier axioms. |
| `infinitude-primes-4k3-oq-03` | Quadratic-form prime density results that share Mathlib's `Nat.primeCounting` consumer surface. |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Mathlib `schnirelmannDensity` integration (RECOMMENDED for S2)**.

   Replace the parent file's
   ```lean
   def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ := 0  -- placeholder
   ```
   with an `import Mathlib.Combinatorics.Schnirelmann` and use the existing
   `schnirelmannDensity` from that module. Then:
   - Restate `schnirelmann_basis_theorem` to use Mathlib's definition (the
     statement is the same; only the underlying definition changes).
   - Add 1-3 small lemmas drawn from Mathlib's existing API
     (`schnirelmannDensity_nonneg`, `schnirelmannDensity_le_one`,
     `schnirelmannDensity_eq_zero_of_one_notMem`) to demonstrate the API
     is now usable.
   - Optionally, prove `schnirelmannDensity {n | Nat.Prime n} = 0` (the
     density of primes is zero — corollary of `schnirelmannDensity_le_of_notMem`
     applied at `k = 1` since `1 ∉ {primes}`).

   **Why it might work**: The Mathlib API is stable and ready. Replacement
   is mechanical except for the namespace clash (parent file's
   `schnirelmannDensity` will shadow Mathlib's; rename one or move to a
   namespace).

   **Risk**: Namespace conflict and import-order issues. The parent file
   uses `WeakGoldbach.schnirelmannDensity` implicitly; replacing it must
   either remove the local def or rename it to a distinguishing name (e.g.,
   `schnirelmannDensity_local`) and re-route consumers.

   **Estimated effort**: 1 PR, ~50-80 lines net, single session.

2. **Approach B — Upgrade `True`-stub theorems**.

   The 2 placeholder theorems
   ```lean
   theorem vinogradov_minor_arc_bound : ∀ A > 0, ∃ C > 0, ∀ N : ℕ, N ≥ 2 → True
   theorem linnik_goldbach_representations : ∃ C > 0, ∀ n : ℕ, n ≥ 4 → Even n → True
   ```
   currently prove `True` — i.e., they prove *nothing* about minor-arc
   bounds or Linnik representations. Upgrading them to bear modest content:
   - `vinogradov_minor_arc_bound`: replace the `True` with a real
     existential statement about `exponentialSumOverPrimes`, e.g.,
     `‖exponentialSumOverPrimes N α‖ ≤ Nat.primeCounting N` (trivial via
     triangle inequality + `‖exp(...)‖ = 1` — but at least *a real
     statement*).
   - `linnik_goldbach_representations`: similarly, replace with a real
     trivial bound like `representationCount n ≤ (Nat.primeCounting n)^3`.

   **Why it might work**: Both upgrades replace fake content with weak-but-
   real content. Each is ~10-20 lines Lean.

   **Risk**: The new statements are not the "actual" Vinogradov / Linnik
   bounds, but neither was the `True` placeholder. The upgrade is
   honestly-stated — the docstring should say "trivial bound; the real
   Vinogradov/Linnik bound is HEROIC and deferred".

   **Estimated effort**: 1 PR, ~30-40 lines net, single session.

3. **Approach C — Small-range `binary_goldbach_verified` via decide**.

   Replace the all-n axiom
   ```lean
   axiom binary_goldbach_verified :
       ∀ n : ℕ, 4 ≤ n → Even n → n ≤ 4 * 10^18 → IsSumOfTwoPrimes n
   ```
   with
   ```lean
   theorem binary_goldbach_verified_small (B := 10^4) :
       ∀ n : ℕ, 4 ≤ n → Even n → n ≤ B → IsSumOfTwoPrimes n := by
     decide  -- or native_decide
   axiom binary_goldbach_verified_large :
       ∀ n : ℕ, B < n → Even n → n ≤ 4 * 10^18 → IsSumOfTwoPrimes n
   ```
   The axiom is *split*, not eliminated. The TRACTABLE portion (small `n`)
   is proven; the HEROIC portion (large `n`) remains.

   **Why it might work**: For `B = 10^3` or `10^4`, `decide` / `native_decide`
   should complete in seconds-to-minutes. The split makes the file
   "honest" about which part is computational vs. assumption.

   **Risk**: `decide` may time out at `B = 10^4`; pick `B = 10^3` and verify.
   Also, the Mathlib `Nat.decidablePrime` cost grows with primality check;
   ~10^4 might be borderline.

   **Estimated effort**: 1 PR, ~30-50 lines Lean + compile-time verification,
   single session if `B = 10^3` works.

4. **Approach D — Schnirelmann's theorem proof (INTERMEDIATE, deferred)**.

   The classical Schnirelmann argument:
   - For `A ⊆ ℕ` with `0 ∈ A`, define `σ(A) := inf_{n ≥ 1} A(n)/n` where
     `A(n) := |A ∩ [1, n]|`.
   - **Lemma (Schnirelmann inequality)**: If `α := σ(A)` and `β := σ(B)`,
     then `σ(A + B) ≥ α + β − α·β`.
   - **Consequence**: If `α > 0`, then `σ(2A) ≥ 2α − α² = 1 − (1 − α)²`,
     and iterating `σ(2^k A) ≥ 1 − (1 − α)^(2^k)`, so for some `k₀`,
     `σ(2^{k₀} A) > 1/2`.
   - **Lemma**: If `σ(A) > 1/2`, then `A + A = ℕ` (proof: pigeonhole on
     `A(n) + A(n) ≥ n + 1`).
   - **Conclusion**: `2^{k₀ + 1} A = ℕ`, i.e., `A` is an additive basis
     of order `2^{k₀ + 1}`.

   **Why it might work**: The argument is classical and well-documented
   (Nathanson 1996 Chapter 7, also Halberstam-Roth *Sequences*). All
   ingredients are real-analysis / combinatorial; no analytic number
   theory beyond the prime-related applications (which we're not
   targeting here).

   **Risk**: Mathlib has only the `schnirelmannDensity` definition and a
   handful of basic bounds at v4.26.0. The full proof must build out
   significant infrastructure: sumsets of ℕ-subsets, the Schnirelmann
   inequality, iterated sumset bounds. ~600-1000 lines Lean, 3-6
   sessions.

   **Estimated effort**: 3-6 PRs, ~600-1000 lines Lean total, 2-4 months
   wall-clock at 1 PR/week.

### Key Difficulties

- **Mathlib gap on Schnirelmann's theorem**. The module docstring at
  `Mathlib/Combinatorics/Schnirelmann.lean` explicitly lists Schnirelmann's
  theorem and Mann's theorem as TODO items. Closing these is a Mathlib
  PR opportunity, not just a gallery PR.

- **Namespace clash on `schnirelmannDensity`**. The parent file declares its
  own placeholder `schnirelmannDensity` at line 330; Mathlib's lives in the
  root namespace. Approach A must either remove the parent's def or rename it.

- **`decide` cost for `binary_goldbach_verified_small`**. Evaluating
  `Nat.Prime` for thousands of `n` and searching for `(p, q)` decompositions
  is `O(B · π(B))` in the worst case; for `B = 10⁴` this is ~10⁴ · 10³ =
  10⁷ work, well within `native_decide` reach but slow for plain `decide`.

- **`circle_method_asymptotic` requires unbuilt machinery**. The Hardy-
  Littlewood singular-series form `S(n) = ∏_p (...)` and the asymptotic
  bound on `‖exponentialSumOverPrimes‖` on minor arcs are not in Mathlib;
  formalizing them is a 1000+ line standalone effort each.

- **No Mathlib `Nat.binaryGoldbach` or `Nat.ternaryGoldbach` exist**.
  The gallery's `IsSumOfTwoPrimes` and `IsSumOfThreePrimes` are
  parent-file-local; coordinating across siblings requires choosing a
  canonical definition.

### What Would a Proof Need? (Approach A)

- **Mathlib import**: `import Mathlib.Combinatorics.Schnirelmann`.
- **Remove or rename** the parent's `def schnirelmannDensity` at line 330.
- **Update `schnirelmann_basis_theorem` statement** to use the un-namespaced
  Mathlib `schnirelmannDensity` (statement is identical except for the
  definition path).
- **Add 3 small lemmas** demonstrating the Mathlib API:
  ```lean
  -- Density of {0} is zero (vacuously)
  lemma schnirelmannDensity_singleton_zero :
      schnirelmannDensity (Set.singleton 0) = 0
  -- Density of {primes} is zero (since 1 ∉ primes)
  lemma schnirelmannDensity_primes_eq_zero :
      schnirelmannDensity {n : ℕ | Nat.Prime n} = 0
  -- Subset implies ≤
  lemma schnirelmannDensity_le_of_subset {A B : Set ℕ}
      [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
      (h : A ⊆ B) : schnirelmannDensity A ≤ schnirelmannDensity B
  ```
  (The third is *already* in Mathlib at v4.26.0 as
  `schnirelmannDensity_le_of_subset`; re-exposing as a `theorem` in the
  parent's namespace is a re-export, not a new proof.)

## Tractability Assessment

**Difficulty**: Low (Approach A) | Low (Approach B) | Low-Medium (Approach C)
| Medium-High (Approach D) | Heroic (full elimination)

**Justification**:
- **Approach A** (S2 target): Single PR, ~80 lines Lean, all stable Mathlib
  API at v4.26.0. Replaces a placeholder definition with the real one and
  exposes the parent file to Mathlib's Schnirelmann infrastructure.
- **Approach B**: Single PR, ~40 lines Lean, replaces fake `True`-stub
  content with real (modest) content.
- **Approach C**: Single PR, ~50 lines Lean + `native_decide` for `B = 10³`
  or `10⁴`. Splits the axiom into TRACTABLE-small + HEROIC-large.
- **Approach D** (deferred): Multi-PR, ~800 lines Lean, 2-4 months. The
  classical Schnirelmann argument is well-understood; the cost is
  infrastructure.
- **Heroic axioms** (`vinogradov_*`, `helfgott_*`, `circle_method_*`, Chen,
  Tao, Ramaré, `helfgott_explicit_bound`): Multi-year. Out of OQ-03 scope
  except as a long-term aspiration.

**Estimated Effort**:
- Approach A: 1 session, single PR, ~80 lines Lean.
- Approach B: 1 session, single PR, ~40 lines Lean.
- Approach C: 1 session, single PR, ~50 lines Lean + ~1 min compile.
- Approach D: 3-6 sessions, ~600-1000 lines Lean, spans weeks.
- Full elimination: multi-year, not S2-Sn candidate.

## References

### Papers and Books

- **Helfgott, H. A.** (2013). *Major arcs for Goldbach's problem*. arXiv:1305.2897.
- **Helfgott, H. A.** (2014). *Minor arcs for Goldbach's problem*. arXiv:1205.5252.
- **Vinogradov, I. M.** (1937). *Representation of an odd number as a sum
  of three primes*. Dokl. Akad. Nauk SSSR 15 (5): 291–294.
- **Schnirelmann, L. G.** (1930). *On the additive properties of numbers*.
  (German translation in *Über additive Eigenschaften von Zahlen*, Math.
  Ann. 107: 649-690, 1933.)
- **Nathanson, M. B.** (1996). *Additive Number Theory: The Classical
  Bases*. Springer GTM 164. — Chapter 7 covers Schnirelmann's theorem.
- **Halberstam, H., Roth, K. F.** (1966). *Sequences*. Oxford University Press.
  — Original combinatorial treatment of Schnirelmann density.
- **Tao, T.** (2014). *Every odd number greater than 1 is the sum of at
  most five primes*. Math. Comp. 83 (286): 997–1038.
- **Ramaré, O.** (1995). *On Šnirel'man's constant*. Ann. Scuola Norm. Sup.
  Pisa Cl. Sci. (IV) 22 (4): 645-706.
- **Chen, J.-R.** (1973). *On the representation of a larger even integer
  as the sum of a prime and the product of at most two primes*. Sci.
  Sinica 16: 157-176.
- **Oliveira e Silva, T., Herzog, S., Pardi, S.** (2014). *Empirical
  verification of the even Goldbach conjecture and computation of prime
  gaps up to 4·10¹⁸*. Math. Comp. 83 (288): 2033-2060.

### Mathlib v4.26.0

- `Mathlib.Combinatorics.Schnirelmann` — `schnirelmannDensity`,
  `schnirelmannDensity_nonneg`, `schnirelmannDensity_le_one`,
  `schnirelmannDensity_le_of_notMem`,
  `schnirelmannDensity_eq_zero_of_one_notMem`,
  `schnirelmannDensity_le_of_subset`. *TODO list mentions Schnirelmann's
  theorem and Mann's theorem.*
- `Mathlib.NumberTheory.PrimeCounting` — `Nat.primeCounting`, basic bounds.
- `Mathlib.Data.Nat.Prime.Defs` — `Nat.Prime`, `Nat.decidablePrime`.
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — circleMap,
  `Complex.exp` basics (used in circle method).

## Metadata

```yaml
tags:
  - number-theory
  - goldbach
  - prime-sums
  - circle-method
  - schnirelmann-density
  - axiom-elimination
  - seeker-selected
  - mathlib-Combinatorics-Schnirelmann
related_proofs:
  - weak-goldbach
  - prime-number-theorem
  - infinitude-primes-4k1
  - infinitude-primes-4k3
difficulty: medium
source: gallery-gap
created: 2026-05-12
```
