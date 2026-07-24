# Knowledge — weak-goldbach-oq-03

## S1 (researcher-5, 2026-05-12) — OBSERVE survey

### Parent context

The parent gallery proof `weak-goldbach` (Weak Goldbach Conjecture, Helfgott
2013) is formalized in `proofs/Proofs/WeakGoldbach.lean` (480 lines, 24
theorems, 15 definitions, 0 sorries). Despite the 0-sorry count, the file
carries **9 axioms** plus **2 theorem-level `True`-stub placeholders** plus
**1 placeholder definition** (`schnirelmannDensity := 0`), so the
sorry-free claim is misleading without the axiom audit.

### Full axiom + stub audit

| # | Declaration | Line | Form | Feasibility |
|---|-------------|------|------|-------------|
| 1 | `vinogradov_ternary_goldbach` | 236 | axiom | HEROIC |
| 2 | `helfgott_weak_goldbach` | 240 | axiom | HEROIC |
| 3 | `circle_method_asymptotic` | 301 | axiom | HEROIC |
| 4 | `schnirelmann_basis_theorem` | 340 | axiom | INTERMEDIATE (Mathlib gap) |
| 5 | `ramare_six_primes` | 350 | axiom | HEROIC |
| 6 | `tao_five_primes` | 355 | axiom | HEROIC |
| 7 | `chen_theorem` | 389 | axiom | HEROIC |
| 8 | `binary_goldbach_verified` | 395 | axiom | TRACTABLE (small range) / HEROIC (full) |
| 9 | `helfgott_explicit_bound` | 425 | axiom | HEROIC |
| 10 | `singular_series_positive` | 286 | theorem returning trivial `⟨1, one_pos⟩` | TRACTABLE (give real content) |
| 11 | `vinogradov_minor_arc_bound` | 292 | theorem with `True` conclusion | TRACTABLE (give real content) |
| 12 | `linnik_goldbach_representations` | 406 | theorem with `True` conclusion | TRACTABLE (give real content) |
| 13 | `schnirelmannDensity` | 330 | placeholder def := 0 | TRACTABLE (use Mathlib) |

Counting: **9 axioms** in the technical sense, but 4 additional declarations
(items 10-13) carry placeholder/trivial content that should be upgraded
before any "axiom-free" claim is honest.

### Three feasibility tiers

#### TRACTABLE (1-3 sessions each, S2-S5 candidates)

- **(A) Mathlib `schnirelmannDensity` integration**: Replace the placeholder
  `def schnirelmannDensity ... := 0` with `import Mathlib.Combinatorics.Schnirelmann`
  and use Mathlib's real definition. Update `schnirelmann_basis_theorem`
  statement accordingly. Add 1-3 small lemmas (e.g., density of primes is 0,
  density of {0} is 0). **~80 lines Lean, single S2 session.**

- **(B) Upgrade `True`-stub theorems**: Replace
  - `vinogradov_minor_arc_bound : ... → True` with
    `‖exponentialSumOverPrimes N α‖ ≤ Nat.primeCounting N` (triangle inequality + `‖exp‖ = 1`).
  - `linnik_goldbach_representations : ... → True` with
    `representationCount n ≤ (Nat.primeCounting n)^3` (cardinality of the
    triple-product underlying `representationCount`).
  - `singular_series_positive`: replace the trivial `⟨1, one_pos⟩` with an
    actual constant tied to `n`, or fold this into a real `S(n)` definition.

  **~40-60 lines Lean, single S2/S3 session.**

- **(C) Small-range `binary_goldbach_verified` via `native_decide`**:
  Split the axiom at `B = 10³` or `10⁴`:
  - `theorem binary_goldbach_verified_small : ∀ n ≤ B, ...` by `native_decide`.
  - `axiom binary_goldbach_verified_large : ∀ n with B < n ≤ 4·10¹⁸, ...`
    (remains axiomatic; the actual Oliveira e Silva computation is 8 CPU-
    months out of scope).
  **~50 lines Lean + native_decide compile time, single S2/S3 session.**

#### INTERMEDIATE (multi-session, weeks to months)

- **(D) Schnirelmann's theorem proper**. Classical proof via:
  1. **Schnirelmann inequality**: `σ(A + B) ≥ α + β − αβ` where `α := σ(A)`,
     `β := σ(B)`. Provable from the elementary bound
     `(A + B)(n) ≥ A(n) + B(n) − min(A(n), B(n))`.
  2. **Iteration**: `σ(2A) ≥ 2α − α² = 1 − (1 − α)²`; inductively
     `σ(2^k A) ≥ 1 − (1 − α)^(2^k)`, so for some `k₀`,
     `σ(2^{k₀} A) > 1/2`.
  3. **Density-half basis**: If `σ(A) > 1/2` then `A + A ⊇ ℕ⁺`. Proof:
     for any `n ≥ 1`, `A(n) > n/2`, so by pigeonhole `A(n) + (n − A(n))`-
     style cardinality argument, the sumset covers.
  4. **Conclusion**: `A` is an additive basis of order `2^{k₀ + 1}`.

  Reference: Nathanson, *Additive Number Theory* (Springer GTM 164),
  Chapter 7 (Schnirelmann's theorem).

  **~600-1000 lines Lean, 3-6 sessions, 2-4 months wall-clock.**

#### HEROIC (multi-year, not S2-Sn candidates)

- (E) `vinogradov_ternary_goldbach`, `helfgott_weak_goldbach`,
  `circle_method_asymptotic`, `ramare_six_primes`, `tao_five_primes`,
  `chen_theorem`, `helfgott_explicit_bound`: All require the **circle
  method machinery** (major/minor arcs, Vinogradov's exponential-sum
  bound on minor arcs, the Hardy-Littlewood singular series) plus
  specific paper-length analytic arguments. Each is a 6-12 month
  formalization project at the level of full Mathlib contributions.

  None of these are S2-Sn candidates under OQ-03; the OQ should be
  understood as "make progress on the TRACTABLE/INTERMEDIATE axioms;
  HEROIC ones are aspirational."

### Recommended path: Approach A in S2

Approach A is the right S2 target:
- Single PR, ~80 lines Lean.
- Uses only stable Mathlib API at v4.26.0.
- Removes the file's only placeholder *definition* (item 13), upgrading
  one of the file's hidden flaws.
- Exposes `Mathlib.Combinatorics.Schnirelmann` as the first gallery
  consumer of that module — a Mathlib-coverage win.
- Sets up Approach D (Schnirelmann's theorem proper) as the natural S3+
  followup once Mathlib's TODO list closes that gap (either via this
  OQ contributing back to Mathlib, or independently).

### Load-bearing Mathlib API

#### Mathlib.Combinatorics.Schnirelmann (v4.26.0)

```lean
-- The Schnirelmann density of a set A ⊆ ℕ
noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ

lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A
lemma schnirelmannDensity_le_one : schnirelmannDensity A ≤ 1
lemma schnirelmannDensity_le_div {n : ℕ} (hn : n ≠ 0) :
    schnirelmannDensity A ≤ #{a ∈ Ioc 0 n | a ∈ A} / n
lemma schnirelmannDensity_mul_le_card_filter {n : ℕ} :
    schnirelmannDensity A * n ≤ #{a ∈ Ioc 0 n | a ∈ A}
lemma schnirelmannDensity_le_of_le {x : ℝ} (n : ℕ) (hn : n ≠ 0)
    (hx : #{a ∈ Ioc 0 n | a ∈ A} / n ≤ x) :
    schnirelmannDensity A ≤ x
lemma schnirelmannDensity_le_of_notMem {k : ℕ} (hk : k ∉ A) :
    schnirelmannDensity A ≤ 1 - (k⁻¹ : ℝ)
lemma schnirelmannDensity_eq_zero_of_one_notMem (h : 1 ∉ A) :
    schnirelmannDensity A = 0
lemma schnirelmannDensity_le_of_subset {B : Set ℕ} [DecidablePred (· ∈ B)]
    (h : A ⊆ B) : schnirelmannDensity A ≤ schnirelmannDensity B
```

**Mathlib TODO** (from the module docstring): "Prove Schnirelmann's
theorem and Mann's theorem on the subadditivity of this density." —
This OQ's Approach D contribution lines up directly with this TODO.

#### Mathlib.NumberTheory.PrimeCounting

```lean
def Nat.primeCounting (n : ℕ) : ℕ  -- π(n) = |{p prime : p ≤ n}|
```

#### Mathlib.Data.Nat.Prime.Defs

```lean
def Nat.Prime (n : ℕ) : Prop
instance Nat.decidablePrime : DecidablePred Nat.Prime
```

### Key insights

1. **"0 sorries" ≠ "0 assumptions"**. The parent file's 0-sorry count is
   misleading: 9 axioms + 2 `True`-stub theorems + 1 placeholder definition
   sum to 12 unverified pieces of content. Any "axiom-free" claim must
   address all 12.

2. **The Mathlib gap on Schnirelmann's theorem is explicit**. The
   `Mathlib.Combinatorics.Schnirelmann` module docstring lists this as
   TODO. The OQ's Approach D doubles as a Mathlib contribution opportunity.

3. **The placeholder definition `schnirelmannDensity := 0` is fixable
   immediately**. Mathlib has the real definition; the parent file just
   needs to import it. This is item 13 and dovetails with Approach A.

4. **The 2 `True`-stub theorems are not "lies", they are placeholders**.
   `vinogradov_minor_arc_bound` and `linnik_goldbach_representations`
   currently prove nothing useful, but each can be upgraded to a *real*
   (modest) bound via Mathlib API in 10-20 lines. The full Vinogradov
   minor-arc bound is HEROIC, but a trivial-but-real bound is TRACTABLE.

5. **Computational verification has a tractable lower tier**. Oliveira e
   Silva verified binary Goldbach up to 4·10¹⁸ (8 CPU-months). We can't
   reach that bound in Lean, but `native_decide` can comfortably handle
   `n ≤ 10³` or `10⁴`, splitting the axiom into a TRACTABLE-small
   theorem + a HEROIC-large residual axiom.

6. **The Schnirelmann proof is well-documented**. Nathanson's *Additive
   Number Theory* GTM 164 gives a complete combinatorial proof in
   Chapter 7. The proof uses no analytic number theory beyond
   elementary inequalities and the Cauchy-Schwarz-style density
   manipulation. Estimated ~600-1000 Lean lines, all combinatorial.

7. **No gallery proof currently imports `Mathlib.Combinatorics.Schnirelmann`**.
   This OQ would be the first. The lack of consumers may explain why
   Schnirelmann's theorem itself has been on Mathlib's TODO list for
   years — no downstream pressure.

8. **The OQ scope is asymmetric across axioms**. Of the 9 axioms,
   ~80% (7/9) are HEROIC (multi-year), ~10% (1/9) is INTERMEDIATE
   (months), and ~10% (1/9 — `binary_goldbach_verified`) is partly
   TRACTABLE (small range) but HEROIC for full elimination. The S2-Sn
   path must focus on the TRACTABLE items and the INTERMEDIATE
   `schnirelmann_basis_theorem` (Approach D); the HEROIC tier is
   long-term aspiration only.

### Mathlib gaps identified

1. **Schnirelmann's theorem** (`σ(A) > 0 → ∃ h, IsAdditiveBasis A h`):
   On Mathlib TODO list (`Mathlib/Combinatorics/Schnirelmann.lean`
   module docstring). Estimated ~600-1000 Lean lines. Approach D target.

2. **Schnirelmann inequality** (`σ(A + B) ≥ α + β − αβ`): On the same
   Mathlib TODO list (Mann's theorem is a sharpening). Approach D
   sub-lemma.

3. **Density-half basis** (`σ(A) > 1/2 → A + A ⊇ ℕ⁺`): Not in Mathlib;
   sub-lemma of Approach D.

4. **Vinogradov's exponential-sum bound** (the minor-arc inequality
   `sup |S(α)| ≤ N / (log N)^A`): Not in Mathlib. HEROIC tier; would
   require the Mathlib analytic-number-theory infrastructure (singular
   series, Gauss sums, etc.) to be built first.

5. **Hardy-Littlewood singular series**: Not in Mathlib. HEROIC tier;
   parent file's `singular_series_positive` is a `⟨1, one_pos⟩`
   placeholder, so even the trivial Mathlib statement is missing.

### Edge cases / potential pitfalls

- **Namespace clash**: Parent's `def schnirelmannDensity` (line 330) and
  Mathlib's `schnirelmannDensity` will clash on `import Mathlib.Combinatorics.Schnirelmann`.
  Approach A must remove the local def OR rename it. Removing is cleaner;
  renaming risks confusion.

- **`schnirelmann_basis_theorem` statement now refers to a different `σ`**:
  After Approach A's import, the axiom's `schnirelmannDensity` resolves
  to Mathlib's, not the placeholder's. The statement still typechecks
  (both have type `Set ℕ → ℝ`), but the *content* is now meaningful (the
  axiom asserts something real, not vacuously about a constant-0 function).

- **`IsAdditiveBasis` is also parent-file-local**. If a future Mathlib
  contribution defines `Mathlib.Combinatorics.IsAdditiveBasis`, we'd
  prefer to use that. Currently the parent's definition is fine.

- **`decide` vs `native_decide` for `binary_goldbach_verified_small`**:
  Plain `decide` may stack-overflow at `B = 10⁴`; `native_decide` is the
  safe choice. Need to verify `B = 10³` first as a baseline.

- **`representationCount` is a triple product over `Finset.range (n + 1)`**:
  For Approach B's `linnik_goldbach_representations` upgrade, the bound
  `representationCount n ≤ (Nat.primeCounting n)^3` uses
  `Finset.card_le_card` on `(primesUpTo n)^3 ⊇ {(p,q,r) : p+q+r=n, primes}`.
  Should be straightforward.

### Next session expectations (S2 candidate)

**S2 (any researcher): Approach A** — Mathlib `schnirelmannDensity` integration.
Three changes to `proofs/Proofs/WeakGoldbach.lean`:

1. Add `import Mathlib.Combinatorics.Schnirelmann` at the top.

2. Remove the placeholder
   ```lean
   def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ := 0
   ```
   (lines ~329-332).

3. Add 1-3 small lemmas using the Mathlib API:
   ```lean
   /-- The Schnirelmann density of the set of primes is 0
       (since 1 ∉ {primes}). -/
   lemma schnirelmannDensity_primes_eq_zero :
       schnirelmannDensity {n : ℕ | Nat.Prime n} = 0 :=
     schnirelmannDensity_eq_zero_of_one_notMem (by decide : ¬ Nat.Prime 1)
   ```

4. (Optional, defer to S3) Re-verify that `schnirelmann_basis_theorem`
   axiom statement still parses and that downstream lemmas using it (if
   any) still typecheck.

**S2 deliverable**: 1 PR, ~80 lines net (1 import + 1 removal + 1-3 lemmas),
single session, build-verified via `./proofs/scripts/docker-build.sh
Proofs.WeakGoldbach` (Mathlib import requires fresh build given the new
module dependency).

**S3+ candidates**: Approach B (True-stub upgrades), Approach C
(`native_decide` for small range), then Approach D (Schnirelmann's
theorem proper, multi-session).

## S2 (researcher-8, 2026-05-12) — ACT (Approach A delivery)

### What was done

Delivered all three S1-prescribed changes to `proofs/Proofs/WeakGoldbach.lean`:

1. **Import**: `import Mathlib.Combinatorics.Schnirelmann` added at top.
2. **Placeholder replaced**: `def schnirelmannDensity ... := 0` (5 lines)
   replaced by `noncomputable abbrev schnirelmannDensity ... := _root_.schnirelmannDensity A`
   (2 lines + 7 lines of docstring).
3. **Lemma added**:
   ```lean
   lemma schnirelmannDensity_primes_eq_zero :
       schnirelmannDensity {n : ℕ | Nat.Prime n} = 0 :=
     _root_.schnirelmannDensity_eq_zero_of_one_notMem
       (fun h => Nat.not_prime_one h)
   ```

### Key API confirmations (via Mathlib `master` lookup)

`Mathlib.Combinatorics.Schnirelmann` at v4.26.0 exports the following
in root namespace (no `Schnirelmann` wrapper):

```lean
noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  ⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n

lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A
lemma schnirelmannDensity_le_one : schnirelmannDensity A ≤ 1
lemma schnirelmannDensity_eq_zero_of_one_notMem (h : 1 ∉ A) :
    schnirelmannDensity A = 0
lemma schnirelmannDensity_le_of_notMem {k : ℕ} (hk : k ∉ A) :
    schnirelmannDensity A ≤ 1 - (k⁻¹ : ℝ)
lemma schnirelmannDensity_le_div {n : ℕ} (hn : n ≠ 0) :
    schnirelmannDensity A ≤ #{a ∈ Ioc 0 n | a ∈ A} / n
lemma schnirelmannDensity_empty : schnirelmannDensity ∅ = 0
lemma schnirelmannDensity_finite {A : Set ℕ} (hA : A.Finite) :
    schnirelmannDensity A = 0
lemma schnirelmannDensity_univ : schnirelmannDensity Set.univ = 1
lemma schnirelmannDensity_setOf_mod_eq_one {m : ℕ} (hm : m ≠ 1) :
    schnirelmannDensity {n | n % m = 1} = (m⁻¹ : ℝ)
```

The definition is `noncomputable`, so any local alias must also be
`noncomputable` (we used `noncomputable abbrev`).

### Design decisions

**Why `abbrev` instead of deleting the local def?** Three reasons:

1. **Backwards compatibility**: The local `axiom schnirelmann_basis_theorem`
   (and any future references) continue to read `schnirelmannDensity A`
   without qualification. Inside `namespace WeakGoldbach`, this resolves
   to `WeakGoldbach.schnirelmannDensity` (our abbrev), which transparently
   unfolds to `_root_.schnirelmannDensity` (Mathlib's). No risk of accidental
   shadowing if a downstream user `open`s a different namespace.

2. **Documentation**: The abbrev carries a docstring explaining the
   transition from placeholder to real density. Deletion would leave a
   silent semantic change with no visible audit trail.

3. **Cost**: Zero — `abbrev` is `reducible`, so unfolding is automatic.

**Why `(fun h => Nat.not_prime_one h)` rather than `Nat.not_prime_one`
directly or `by decide`?**

- `Nat.not_prime_one h` would be the "η-equivalent" form. The explicit
  lambda is slightly safer because `Set.mem_setOf_eq` is reflexive
  (definitional) but not always normalized by elaboration; the lambda
  forces Lean to unfold `(1 ∈ {n | Nat.Prime n})` to `Nat.Prime 1`
  during type-checking of the body, where `Nat.not_prime_one : ¬ Nat.Prime 1`
  exactly matches.

- `by decide` would also work but is heavier (it kernel-evaluates
  primality of 1) and produces a more opaque proof term.

### Counts delta

| Metric | S1 (pre) | S2 (post) | Δ |
|--------|----------|-----------|---|
| `lineCount` (parent file) | 480 | 497 | +17 |
| `axiomCount` (parent file) | 9 | 9 | 0 |
| `definitionCount` (parent file) | 15 | 15 | 0 |
| `theoremCount` (parent file) | 24 | 25 | +1 |
| Sorries (parent file) | 0 | 0 | 0 |
| `True`-stub placeholders | 2 | 2 | 0 |

### What S2 does NOT accomplish

- **Axiom count is unchanged.** `schnirelmann_basis_theorem` remains
  axiomatized. S2 only makes its hypothesis non-vacuous; eliminating it
  is Approach D's multi-session task.
- **`True`-stub theorems** at lines 292 and 406 are unchanged. Approach
  B (S3 target) addresses those.
- **The placeholder `def schnirelmannDensity := 0`** was a logical bug:
  it trivialized `schnirelmann_basis_theorem`'s hypothesis (the hypothesis
  was `0 > 0`, always false, so the axiom was vacuous). S2's replacement
  fixes this bug, so a downstream agent attempting to *prove*
  `schnirelmann_basis_theorem` will now face the real mathematical content.

### Next session (S3)

**Approach B**: Upgrade `vinogradov_minor_arc_bound` (line 292) and
`linnik_goldbach_representations` (line 406) from `True`-stub form to
real (modest) content.

For `linnik_goldbach_representations` specifically:
- Goal shape:
  `∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → Even n → ...`
- Trivial real-content bound: `representationCount n ≤ (Nat.primeCounting n)^3`
  via `Finset.card_le_card` applied to the product
  `(primesUpTo n) × (primesUpTo n) × (primesUpTo n) ⊇ {(p,q,r) : p+q+r = n}`.

For `vinogradov_minor_arc_bound`:
- Goal shape: `True` currently. Upgrade to:
  `∃ C : ℝ, ∀ N : ℕ, N ≥ 2 → |exponentialSumOverPrimes N α| ≤ C * N`
  (trivial bound, not the deep Vinogradov bound). The deep
  `N / (log N)^A` bound is HEROIC and stays.

---

## S5 ACT Session (researcher-5, 2026-05-12)

### Strategy chosen

**Axiom elimination over multi-session Schnirelmann work.** The seeker
recommended Approach D-phase-1 (Schnirelmann sumset inequality, multi-
session 600–1000 LOC) as the canonical S5+ direction. S5 instead
implemented a narrow axiom-elimination pass on two routine-derivable
axioms (`ramare_six_primes`, `tao_five_primes`), both of which follow
trivially from `helfgott_weak_goldbach` and never had real reason to be
separate axiomatic claims — they predate Helfgott historically but are
all subsumed by his unconditional 3-prime result.

Per `researcher.md` axiom-elimination priority:
> "A file with 100 theorems and 50 axioms is weaker than a file with 20
> theorems and 2 axioms. Every axiom is an unverified assumption."

The S5 reduction (9 → 7 explicit axioms) is real progress by this
metric. The underlying assumption set is unchanged (still depends on
helfgott_weak_goldbach), but the file's axiom surface is cleaner: the
remaining 7 axioms are *genuine* assumptions (deep results not subsumed
by Helfgott) rather than historical attribution markers.

### Mechanical pattern (Helfgott corollary)

Both proofs share the structure:
1. `by_cases hLarge : <large enough for Helfgott>` (`n > 5` for tao;
   `n ≥ 10` for ramare).
2. Large branch: `obtain ⟨p, q, r, hp, hq, hr, heq⟩ := helfgott_weak_goldbach _ _ _`
   gives 3 primes; refine with `[p, q, r]` or `[3, p, q, r]`.
3. Small branch: `push_neg at hLarge; rcases hOddOrEven with ⟨k, rfl⟩;
   interval_cases k` enumerates the residual cases; explicit witnesses.

For the prime-membership obligation `∀ p ∈ primes, Nat.Prime p`, the
unfold pattern is:
```lean
intro p hp
simp at hp        -- reduces `p ∈ [a, b, ...]` to `p = a ∨ p = b ∨ ...`
rcases hp with rfl | rfl | ... <;> assumption  -- or exact specific prime lemmas
```

For the sum-equals-`n` obligation, `simp; omega` reliably closes after
`List.sum` unfolds and Helfgott's `heq` is in scope.

### Reusable lemma observation

`Even n` in Mathlib v4.26.0 unfolds to `∃ r, n = r + r` (additive,
not multiplicative). For Nat-subtraction reasoning where we need
`Odd (n - 3)` from `Even n` with `n ≥ 10`, destructuring `Even` as
`n = k + k` first (so `n - 3 = k + k - 3 = 2*(k - 2) + 1`) puts `omega`
in friendly territory. Destructuring inside a sub-tactic block left
the outer goal in a slightly fragile state in early drafts; doing it
at the top of each `by_cases` branch is cleaner.

### Counts delta

| Field | Before S5 | After S5 | Delta |
|-------|-----------|----------|-------|
| `axiomCount` | 9 | 7 | −2 |
| `theoremCount` (broad `^(theorem\|lemma) `) | 26 | 28 | +2 |
| `lineCount` | 543 | 627 | +84 |
| `definitionCount` | 15 | 15 | 0 |
| Sorries | 0 | 0 | 0 |

### Insights for S6+

- **`vinogradov_ternary_goldbach` is similarly routine** — it asserts
  `∃ N₀, ∀ n > N₀, Odd n → IsSumOfThreePrimes n`, which is satisfied by
  `N₀ := 5` via Helfgott. Another ~5 LOC axiom elimination available.
  Would bring `axiomCount` to 6.
- **`helfgott_explicit_bound`** (line ~488) is also potentially
  derivable from `helfgott_weak_goldbach`, depending on its precise
  statement — needs inspection.
- The remaining "genuinely separate" axioms after these eliminations
  would be: `helfgott_weak_goldbach` (the central deep result),
  `circle_method_asymptotic` (Hardy-Littlewood circle method),
  `schnirelmann_basis_theorem` (Schnirelmann density implies basis),
  `chen_theorem` (Chen 1973), `binary_goldbach_verified` (Oliveira e
  Silva 2013 computational). These are 5 genuinely distinct deep claims.

### Honesty note

These eliminations do **not** mathematically advance the formalization —
the proofs are routine corollaries of an already-formalized stronger
result. They make the *axiom surface* cleaner (better honesty signal
in meta.json: 7 deep claims vs 9 mixed historical-and-deep claims) but
do not contribute new mathematical content. Per `researcher.md`'s
"Honesty Standards" the value is in the gallery-integrity improvement,
not in any new theorem-power.

---

## S9 ACT Session (researcher-1, 2026-07-24)

### Situation on arrival

- Tracker had been BLOCKED since 2026-06-13 (Docker blackout). Docker is
  back (`docker info` OK); flag lifted.
- **Census drift**: sibling weak-goldbach-oq-01 (PR #34353, 2026-07-03)
  proved `schnirelmann_basis_theorem` outright
  (`SchnirelmannTheorem.schnirelmann_basis`, assembled from
  `SchnirelmannCounting.schnirelmann_inequality` +
  `SchnirelmannBasis` covering bookkeeping). The axiom floor is **4**,
  not the 5 recorded by S7/S8 PREP, and the planned S9 Approach D
  (density-to-basis machinery) was consumed wholesale by the sibling.
- Gallery meta (`src/data/proofs/weak-goldbach/meta.json`) was already
  synced to 4 axioms / 764 LOC by the sibling's PR; only this tracker's
  state.md was stale.

### What S9 built (the bridge)

With the basis theorem now genuine, Schnirelmann's classical 1930
argument for "every n ≥ 2 is a sum of a bounded number of primes"
becomes formalizable end-to-end **modulo one input**: σ({0,1} ∪ (P+P)) > 0
(Brun sieve, unformalized HEROIC). S9 formalizes exactly that
implication, keeping the density input a *hypothesis* — axiom count
unchanged.

Pieces (all in `WeakGoldbach.lean`, lines 498–675):

1. `goldbachSumset := {0, 1} ∪ {n | IsSumOfTwoPrimes n}` +
   `mem_goldbachSumset` + decidable membership via the file's existing
   `decidableIsSumOfTwoPrimes` (needed because both the local
   `schnirelmannDensity` abbrev and Mathlib's definition demand
   `[DecidablePred (· ∈ A)]`).
2. `exists_two_three_multiset (m ≥ 2)`: multiset of primes from {2,3}
   with card ≤ m and sum m. **No strong induction needed**: parity
   split with `Multiset.replicate` witnesses (`k` copies of 2, or
   `3 ::ₘ replicate (k-1) 2`). `Multiset.sum_replicate` produces `n • a`;
   add `smul_eq_mul` to the simp set so `omega` can finish.
3. `goldbachSumset_multiset_decomp`: ∀ S with elements in G,
   ∃ r ≤ S.card and prime multiset T with T.card ≤ 2·S.card and
   S.sum = r + T.sum. `Multiset.induction_on` (case names
   `empty`/`cons`); each cons case closes with
   `simp only [Multiset.card_cons / sum_cons]; omega`.
4. `BoundedPrimeSums` (Prop) and `schnirelmann_goldbach_bridge`:
   σ(G) > 0 → BoundedPrimeSums with k = 3h+2. Apply basis at n−2,
   decompose, absorb 2+r (≤ h+2) into 2s and 3s, `U + T` via
   `Multiset.card_add`/`sum_add` + omega.
5. `sum_of_at_most_four_primes` (unconditional, k = 4, via the
   axiomatized Helfgott): odd n > 5 → {p,q,r}; even n ≥ 10 → Helfgott
   at n−3 (Odd (k+k−3) witness `⟨k−2, by omega⟩`) plus a 3 → 4 primes;
   n ∈ [2,9] by `interval_cases` + literal multiset witnesses, each
   closed by three `by decide`s (`Multiset.decidableDforallMultiset`
   makes `∀ p ∈ {2,7}, Nat.Prime p` decidable).
   `boundedPrimeSums_of_helfgott := ⟨4, sum_of_at_most_four_primes⟩`.

### Lean idioms that worked first-try (docker-verified, 8579 jobs)

- `decidable_of_iff` + existing sound/complete pair for set-membership
  instances: `decidable_of_iff (n = 0 ∨ n = 1 ∨ IsSumOfTwoPrimes n)
  mem_goldbachSumset.symm`.
- `Multiset.eq_of_mem_replicate` to prove all-elements-prime for
  replicate witnesses.
- Multiset literals `{3, p, q, s}` with variables: normalize with
  `Multiset.insert_eq_cons` before `Multiset.mem_cons`/`sum_cons` simp.
- `Even n` destructures to `n = k + k` (not `2*k`); omega copes.

### Counts delta

| Field | Before S9 | After S9 |
|-------|-----------|----------|
| lineCount | 764 | 943 |
| axiomCount | 4 | 4 (unchanged) |
| theoremCount (meta) | 32 | 38 |
| definitionCount | 15 | 17 |
| sorries | 0 | 0 |

Gallery meta: sections re-anchored (Part III split into III/III(b)
bridge/III(c) cascade; Parts IV+ shifted +179). NOTE: annotations.json
ranges were already stale before S9 (anchored to a ~481-line ancestor,
max endLine 451) — left untouched; that is enricher re-anchoring work,
not researcher scope.

### S10+ options

- (a) Any piece of σ(G) > 0: Brun/Selberg sieve — multi-quarter HEROIC;
  Mathlib has no sieve infrastructure as of v4.31.
- (b) Quantitative bookkeeping: from a hypothesized explicit lower bound
  σ(G) ≥ δ, extract an explicit basis order h(δ) and hence explicit k —
  requires making `SchnirelmannTheorem.schnirelmann_basis` quantitative
  (inspect whether its h is already computable from the proof).
  Moderate, ~150–250 LOC.
- (c) Park: the elementary tier is genuinely saturated now — the 4
  remaining axioms are all HEROIC-or-computational.
