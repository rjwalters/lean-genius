# S7 PREP — Axiom Redundancy Audit: 7 axioms → minimum 4

**Date**: 2026-05-12
**Researcher**: researcher-1
**Phase**: PREP (orthogonal to S6 PREP `2026-05-12-s6-prep-vinogradov-helfgott-reduction.md`)
**Type**: Doc-only axiom audit. No edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, gallery `meta.json`, or research JSON.

## Rationale

S5 ACT recovery (PR #18265, merged 2026-05-12 22:18 UTC) reduced
`WeakGoldbach.lean`'s declared axiom count from **9 → 7** by
discharging `ramare_six_primes` and `tao_five_primes` from
`helfgott_weak_goldbach`. S6 PREP (PR #18368, merged 2026-05-13
02:11 UTC, ~30 min before this PREP) designed the next 1-line
discharge for `vinogradov_ternary_goldbach` (axiom 7 → 6 via
`⟨5, helfgott_weak_goldbach⟩`).

This PREP audits the **7 remaining axioms** on `origin/main` HEAD
(`0c84ce40fd1`) and identifies a **second tautological discharge
opportunity** parallel to S6 PREP's: **`helfgott_explicit_bound`
has an identical Lean type to `helfgott_weak_goldbach`** (after
unfolding `WeakGoldbachConjecture`). It is a literal 1-line
discharge.

Together with S6 PREP, this would bring the file from 7 axioms
to **5 axioms** in two trivial ACT iterations.

This PREP also catalogs the remaining 5 axioms after S6+S7 ACT
and judges Mathlib reducibility for each.

This is doc-only: no Lean changes, no `state.md` / `knowledge.md`
/ `problem.md` / gallery / research-JSON edits. Branched off
`origin/main` at `0c84ce40fd1` (post-S5 ACT recovery, post-S6 PREP,
post unrelated recent merges).

## 1. Current axiom census (origin/main HEAD `0c84ce40fd1`)

`grep -nE "^axiom " proofs/Proofs/WeakGoldbach.lean` returns 7 lines:

```
258: axiom vinogradov_ternary_goldbach :  -- S6 PREP target
262: axiom helfgott_weak_goldbach : WeakGoldbachConjecture
336: axiom circle_method_asymptotic :
379: axiom schnirelmann_basis_theorem (A : Set ℕ) [DecidablePred (· ∈ A)] :
530: axiom chen_theorem :
536: axiom binary_goldbach_verified :
605: axiom helfgott_explicit_bound :   -- NEW S7 finding: redundant w/ helfgott_weak_goldbach
```

And the definition at line 30:

```lean
def WeakGoldbachConjecture : Prop :=
  ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n
```

## 2. Finding — `helfgott_explicit_bound` is Lean-type-redundant

### 2.1 The two axiom signatures

```lean
-- Line 262:
axiom helfgott_weak_goldbach : WeakGoldbachConjecture
-- which unfolds via def at line 30 to:
--   ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n

-- Lines 605–608:
axiom helfgott_explicit_bound :
    -- The threshold N₀ in Vinogradov's theorem is at most 8.875 × 10³⁰
    -- This is small enough to check computationally below
    ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n
```

**The Lean type of `helfgott_explicit_bound` is `∀ n : ℕ, n > 5 →
Odd n → IsSumOfThreePrimes n`**, which is **definitionally equal**
to the Lean type of `helfgott_weak_goldbach` after δ-unfolding the
`def WeakGoldbachConjecture`. Two `axiom`s with the same Lean type
are mutually inter-derivable as 1-line theorems.

### 2.2 The 1-line S7 ACT

```lean
/-- Helfgott's explicit bound is the same statement as the weak
    Goldbach conjecture (modulo unfolding `WeakGoldbachConjecture`).
    The docstring describes the 8.875 × 10³⁰ threshold, but the
    Lean type captures only the universal statement that every
    odd n > 5 is the sum of three primes — exactly the body of
    `WeakGoldbachConjecture`. -/
theorem helfgott_explicit_bound :
    ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n :=
  helfgott_weak_goldbach
```

Type-checking sketch: the RHS `helfgott_weak_goldbach` has type
`WeakGoldbachConjecture`, which δ-reduces to the goal type. Lean's
elaborator handles the unfolding automatically (same mechanism that
makes `weak_goldbach` at line 265 work as `fun n hn hodd ↦ helfgott_weak_goldbach n hn hodd`).

### 2.3 The docstring-vs-type mismatch

The docstring at lines 602–604 says:

> Helfgott's explicit bound: all odd n > 5 are sums of three primes.
> The computational part verified odd n ≤ 8.875 × 10³⁰.
> The analytic part (improved Vinogradov) handled n > 8.875 × 10³⁰.

The **structural content** of "Helfgott's explicit bound" (vs.
"helfgott_weak_goldbach") is the *threshold* (`N₀ ≤ 8.875 × 10³⁰`).
But the Lean type only records the universal-quantification
statement `∀ n > 5, …` — it does **not** record the threshold.

**Two options for capturing the docstring's intent**:

* **(a)** **Discharge as 1-line theorem** (recommended). Accept
  that the Lean type as written is just the weak Goldbach
  statement; document this in the new theorem's docstring; rely
  on the *axiom* `helfgott_weak_goldbach` to carry the
  mathematical content.

* **(b)** **Restate to capture the threshold**:
  ```lean
  theorem helfgott_explicit_bound :
      ∃ N₀ : ℕ, N₀ ≤ 8875 * 10^27 ∧
        ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n :=
    ⟨5, by norm_num, helfgott_weak_goldbach⟩
  ```
  This *does* record the `N₀ ≤ 8.875 × 10³⁰` content, by witnessing
  with `N₀ := 5` (which trivially satisfies `N₀ ≤ 8.875 × 10³⁰`).
  This is the **stronger** and **honest** discharge but it changes
  the axiom's type, which could break downstream consumers.

Recommend (a) as the S7 ACT, with (b) as a follow-up rename if
needed. (a) preserves the existing axiom type for downstream
compatibility; (b) requires checking for consumers.

### 2.4 Why is `helfgott_explicit_bound` even in the file?

Historically, the slug's S1 OBSERVE (PR #18035, researcher-5)
catalogued 9 axioms by **author/year attribution**:
helfgott_weak_goldbach (2013), vinogradov_ternary_goldbach (1937),
helfgott_explicit_bound (2013), ramare_six_primes, tao_five_primes,
chen_theorem, binary_goldbach_verified, circle_method_asymptotic,
schnirelmann_basis_theorem.

The 1937 Vinogradov and 2013 Helfgott statements have identical
**Lean-encodable types** despite different mathematical content
(Vinogradov: existential `∃ N₀`; Helfgott: universal `∀ n > 5`).
**S6 PREP discharges Vinogradov as the existential-intro of Helfgott**
(`⟨5, …⟩`). **S7 ACT discharges `helfgott_explicit_bound` as
Helfgott itself** (the universal — they have the same Lean type).

The historical-attribution axioms are **proof-theoretically reducible**
to a single root: **`helfgott_weak_goldbach`**. After S6 + S7 ACT,
the file's `Helfgott chain` axiom count drops to 1 (`helfgott_weak_goldbach`
alone), with 2 derived theorems exposing the existential and explicit-bound
shapes.

## 3. Post-S6+S7 axiom census (projected)

| #   | Axiom                            | Line  | Status post-S6+S7                                                                                  |
| --- | -------------------------------- | ----- | -------------------------------------------------------------------------------------------------- |
| 1   | `vinogradov_ternary_goldbach`     | 258   | **Theorem** (S6 ACT, 1-line: `⟨5, helfgott_weak_goldbach⟩`)                                       |
| 2   | `helfgott_weak_goldbach`          | 262   | **AXIOM (root)** — irreducible, Helfgott 2013 is deep                                              |
| 3   | `circle_method_asymptotic`        | 336   | **AXIOM** — Hardy–Littlewood circle-method asymptotic; not in Mathlib                              |
| 4   | `schnirelmann_basis_theorem`      | 379   | **AXIOM** — Mathlib has `schnirelmannDensity` def but not this theorem (state.md confirms)         |
| 5   | `chen_theorem`                    | 530   | **AXIOM** — Chen 1973; not in Mathlib (verified: 0 hits for `chen_theorem` in `search/code`)        |
| 6   | `binary_goldbach_verified`        | 536   | **AXIOM** — Oliveira e Silva 2013 numerical verification; not in Mathlib                          |
| 7   | `helfgott_explicit_bound`         | 605   | **Theorem** (S7 ACT, 1-line: `helfgott_weak_goldbach`)                                              |

**Post-S6+S7 result**: 7 declared axioms → **5 declared axioms**.

## 4. Mathlib reducibility audit of remaining 5 axioms

### 4.1 `helfgott_weak_goldbach` (line 262, ROOT)

* **Mathematical status**: Deep theorem (Helfgott 2013, peer-reviewed
  but the formal proof depends on 30,000+ lines of intermediate
  computer-algebra and circle-method estimates).
* **Mathlib status**: not formalised.
* **Reduction path**: **None at the kernel level**. Helfgott's proof
  itself uses Vinogradov 1937 + computational verification up to
  `8.875 × 10³⁰`. No proper subset of the remaining axioms can
  derive helfgott_weak_goldbach.
* **Recommendation**: keep as axiom. Document the lineage in the
  docstring.

### 4.2 `circle_method_asymptotic` (line 336)

* **Lean type**:
  ```lean
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n →
    (representationCount n : ℝ) > (n : ℝ)^2 / (Real.log n^3 * 2) * (1 - ε)
  ```
* **Mathematical status**: Hardy–Littlewood asymptotic for the
  number of representations of odd `n` as a sum of three primes,
  with main term `n²/(log n)³ · S(n) / 2` where `S(n)` is the
  singular series.
* **Mathlib status**: not formalised. `Mathlib.NumberTheory.*` has
  `Nat.primeCounting` and basic asymptotic infrastructure
  (`isBigO_*`) but no Hardy–Littlewood-grade asymptotics for
  representations. Search `gh api search/code repo:leanprover-community/mathlib4`
  for `representationCount` returns 0 hits.
* **Reduction path**: **None at the kernel level**. The circle-method
  proof is a multi-month upstream Mathlib contribution.
* **Recommendation**: keep as axiom. Tag for Mathlib upstream when
  Hardy–Littlewood infrastructure lands.

### 4.3 `schnirelmann_basis_theorem` (line 379)

* **Lean type**:
  ```lean
  schnirelmannDensity A > 0 → ∃ h : ℕ, IsAdditiveBasis A h
  ```
* **Mathematical status**: Schnirelmann 1933. Every set of positive
  Schnirelmann density is an additive basis of finite order.
* **Mathlib status**: `Mathlib.Combinatorics.Schnirelmann` has the
  **definition** `schnirelmannDensity` (used in S2 by researcher-8)
  and trivial evaluation lemmas, but **not** the basis theorem
  itself. State.md S2 block confirms: "the **theorem** that
  `0 ∈ A` plus `σ(A) > 0` ⟹ `A` is an additive basis is *not* in
  Mathlib yet."
* **Reduction path**: not Mathlib-derivable in v4.26.0. The proof
  (Schnirelmann's sumset inequality + iteration) is a ~300–600
  LOC effort to formalise.
* **Recommendation**: keep as axiom. Possible **D-phase** target
  per state.md S5 candidate (Approach D-phase-1 = Schnirelmann
  sumset inequality).

### 4.4 `chen_theorem` (line 530)

* **Lean type**:
  ```lean
  ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Even n →
    ∃ p m, Nat.Prime p ∧ IsP2 m ∧ n = p + m
  ```
  where `IsP2 m := Nat.Prime m ∨ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ m = p * q`.
* **Mathematical status**: Chen 1973. Every sufficiently large even
  integer is a sum of a prime and a product of at most two primes.
* **Mathlib status**: not formalised. Search `gh api search/code
  repo:leanprover-community/mathlib4 chen_theorem extension:lean`
  returns 0 hits.
* **Reduction path**: **None**. Chen's proof uses a weighted
  Selberg sieve + Bombieri–Vinogradov; both pieces are partial in
  Mathlib (Bombieri–Vinogradov has scaffolding only). Multi-year
  upstream effort.
* **Recommendation**: keep as axiom indefinitely.

### 4.5 `binary_goldbach_verified` (line 536)

* **Lean type**:
  ```lean
  ∀ n : ℕ, 4 ≤ n → Even n → n ≤ 4 * 10^18 → IsSumOfTwoPrimes n
  ```
* **Mathematical status**: Oliveira e Silva 2013 verified binary
  Goldbach up to `4 × 10^18` by exhaustive computer search.
* **Mathlib status**: not formalised.
* **Reduction path**: For *small* ranges, S4 already proved
  `binary_goldbach_verified_small : ∀ n ≤ 30, ...` via
  `interval_cases + decide`. Extension to `n ≤ 4 × 10^18` is
  **infeasible** by kernel `decide` (too slow) and **questionable**
  by `native_decide` (would take days/weeks even with bytecode).
  The axiom records an external computer verification that is
  not practical to reproduce inside Lean.
* **Recommendation**: keep as axiom; the S4 small-range theorem
  is the right "honest" companion.

### 4.6 Summary: post-S6+S7+full Mathlib audit, 5 axioms remain irreducible

All 5 remaining axioms (`helfgott_weak_goldbach`, `circle_method_asymptotic`,
`schnirelmann_basis_theorem`, `chen_theorem`, `binary_goldbach_verified`)
require **upstream Mathlib formalisation efforts** (multi-month to
multi-year each) and cannot be discharged within this slug's
ACT/PREP scope.

The slug's S6+S7 ACT (axioms 7 → 5) is the **maximum tractable
axiom elimination**; further reduction requires Mathlib upstream
contributions (Schnirelmann basis theorem = state.md's D-phase
target; the others are deeper).

## 5. Compatibility with open PRs

* **#18245** (OPEN S5 ACT, build pending 7h stale, but superseded by merged #18265): orthogonal — same axiom-elimination angle but for `ramare_six_primes` + `tao_five_primes`, both already merged.
* **#18368** (MERGED S6 PREP, `vinogradov_ternary_goldbach` discharge): the companion this PREP rides on. Orthogonal: this PREP creates a **new** `sessions/2026-05-12-s7-prep-axiom-redundancy-audit.md` and does not edit the S6 PREP file.

This session doc creates no Lean changes, no `state.md` /
`knowledge.md` / `problem.md` / gallery / research-JSON conflicts.

## 6. Honest framing — what this PREP session does not establish

1. **No `lake build` performed.** All axiom type identifications are
   by literal `grep -nE "^axiom "` + `Read` of `WeakGoldbach.lean`.
   The Lean-type-equality claim
   `helfgott_explicit_bound ≡ helfgott_weak_goldbach (after δ-unfolding)`
   should be probed by S7 ACT author with `#check @helfgott_explicit_bound`
   + `#check @helfgott_weak_goldbach`.

2. **No verification that `(b)`-variant (stronger discharge) is consumer-safe.**
   §2.3 option (b) restates `helfgott_explicit_bound` with the threshold
   bound. If any downstream consumer pattern-matches `helfgott_explicit_bound`
   as `∀ n > 5, …` directly, (b) would break them. (a) preserves the
   signature.

3. **The S6 PREP discharge has not landed yet.** S6 PREP is a doc-only
   plan; S6 ACT (1-line theorem replacement) is pending. If S6 ACT
   is shipped before S7 ACT, the axiom count is 7 → 6 → 5. If S7 ACT
   ships first, 7 → 6 → 5. Either order works; both discharges are
   1-line and conflict-free with each other (they target different
   axioms at lines 258 and 605).

4. **No bookkeeping for state.md/knowledge.md/meta.json update.** When
   S6 ACT or S7 ACT lands, the corresponding `axiomCount` field in
   `state.md` / `meta.json` / research JSON must be decremented. This
   PREP does **not** prescribe the exact bookkeeping; that's the
   ACT author's task.

5. **§4 Mathlib reducibility judgments are by `search/code` keyword
   sampling**, not exhaustive name-pattern probes. A more
   comprehensive audit (`gh api search/code` for all 5 axiom names
   in `*Mathlib.NumberTheory.*` and `*Mathlib.Combinatorics.*`) is
   left to a future PREP if the high-confidence "not in Mathlib"
   judgments here turn out to be wrong.

6. **No comment on the open-PR state of #18245.** S5 ACT's open
   PR is superseded by the merged S5 recovery #18265; this PREP
   does not recommend closing #18245 (that's a different agent's
   concern).

## 7. Done When (this PREP session)

- [x] Axiom census of `proofs/Proofs/WeakGoldbach.lean` on `origin/main`
  HEAD `0c84ce40fd1` performed (7 axioms confirmed).
- [x] `helfgott_explicit_bound` identified as Lean-type-redundant with
  `helfgott_weak_goldbach` (1-line discharge via δ-reduction of
  `WeakGoldbachConjecture`).
- [x] Post-S6+S7 projected axiom count = 5 (`helfgott_weak_goldbach`,
  `circle_method_asymptotic`, `schnirelmann_basis_theorem`,
  `chen_theorem`, `binary_goldbach_verified`).
- [x] Mathlib reducibility audit for each of the 5 remaining axioms
  via `gh api search/code`-style keyword probes.
- [x] Recommendation: ship S6 ACT + S7 ACT (both 1-line theorem
  discharges, no Lean dependencies on each other).
- [x] Honest-framing caveats (6).
- [x] No edits to `state.md`, `knowledge.md`, `problem.md`, gallery,
  Lean file, or research JSON.

## 8. No-edit guarantee

This PR touches **only**:

```
research/problems/weak-goldbach-oq-03/sessions/
    2026-05-12-s7-prep-axiom-redundancy-audit.md
```

Branch base: `origin/main` at `0c84ce40fd1` (post S5 ACT recovery
#18265, post S6 PREP #18368, post unrelated general-quartic-oq-02 /
fodor / sperner merges). No existing file is modified.

## 9. References

* **S6 PREP companion** (`vinogradov_ternary_goldbach` discharge):
  `research/problems/weak-goldbach-oq-03/sessions/2026-05-12-s6-prep-vinogradov-helfgott-reduction.md`
  (PR #18368, merged 2026-05-13 02:11 UTC, researcher-5).
* **S5 ACT (recovery)** (`ramare_six_primes` + `tao_five_primes` discharge):
  PR #18265, merged 2026-05-12 22:18 UTC.
* **S1 OBSERVE** (9-axiom catalog): PR #18035, merged 2026-05-12 11:06 UTC, researcher-5.
* **WeakGoldbach.lean current axioms** (line numbers refer to `origin/main` HEAD):
  `vinogradov_ternary_goldbach` (258), `helfgott_weak_goldbach` (262),
  `circle_method_asymptotic` (336), `schnirelmann_basis_theorem` (379),
  `chen_theorem` (530), `binary_goldbach_verified` (536),
  `helfgott_explicit_bound` (605).
* **Helfgott, H. A.** (2013). *The ternary Goldbach problem*. arXiv:1501.05438.
* **Vinogradov, I. M.** (1937). *Representation of an odd number as a sum of three primes*.
* **Oliveira e Silva, T., Herzog, S., & Pardi, S.** (2013). *Empirical verification of the
  even Goldbach conjecture and computation of prime gaps up to 4·10¹⁸*.
* **Schnirelmann, L.** (1933). *Über additive Eigenschaften von Zahlen*.
* **Chen, J. R.** (1973). *On the representation of a larger even integer as the sum of a
  prime and the product of at most two primes*.
* `Mathlib.Combinatorics.Schnirelmann` — has `schnirelmannDensity` definition.
* `Mathlib.NumberTheory.Primorial` — primorial bounds; not used by this slug directly.
