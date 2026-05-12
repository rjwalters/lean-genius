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
