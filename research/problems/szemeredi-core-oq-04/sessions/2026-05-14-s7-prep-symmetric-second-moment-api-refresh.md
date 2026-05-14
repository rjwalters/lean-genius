# szemeredi-core-oq-04 — S7 PREP: symmetric-variant second-moment API refresh + iter 10 build-verified status correction

**Date**: 2026-05-14
**Author**: researcher-9
**Scope**: Doc-only follow-up to S6c-ACT (PR #18959, merged 2026-05-14 03:04 UTC, researcher-9). Refreshes the Cauchy–Schwarz / Markov API pins from S6b PREP (PR #18476, researcher-6, 2026-05-13) so they apply to the now-merged **symmetric** surrogate `IsWitnessRegular_symmetric` rather than the obsolete one-sided form, verifies the API path drift across Mathlib v4.26.0 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, and pins clean Lean signatures for the four S7 ACT helper lemmas (`vertexBias_A_average`, `vertexBias_B_average`, `markov_bad_count`, `slack4_assemble`).

Also resolves the state.md "Build pending Docker wrapper" / commit-message "build verified" inconsistency for iter 10 — local Docker build of `Proofs.SzemerediCoreOQ04` did pass at PR #18959 push time (7744 jobs, see PR body §"Build status"); state.md was not updated post-build.

**No Lean source changes.** **No** `meta.json`, `problem.md`, gallery JSON edits. Adds exactly one new session note (this file). State.md gains an iter 11 PREP entry + a minor iter 10 build-verified correction. JSON `currentState.{iteration,since,focus,nextAction}` + `knowledge.{progressSummary,nextSteps}` updated to match.

## 1. Why this PREP

S6b PREP (PR #18476) pinned three Mathlib lemmas — `sq_sum_le_card_mul_sum_sq`, `sum_mul_sq_le_sq_mul_sq`, `sum_le_card_nsmul` — for the second-moment / Cauchy–Schwarz step of the slack-4 ADLRY implication. **Two events since invalidate the S6b context**:

1. **PR #18679 (S6c PREP-2)**: concrete `#V = 16` counterexample showed the one-sided `IsWitnessRegular G eps A B → IsEpsilonRegular G (4·eps) A B` is mathematically false. The deferred-proof obligation moved from the one-sided helper at line 291 (now archival, unprovable) to the symmetric helper at line 831.
2. **PR #18959 (S6c-ACT)**: shipped Option A — `witnessFamilyA` + `Dual_IsWitnessRegular` + `IsWitnessRegular_symmetric` + 22 sorry-free declarations. The S7 ACT helpers must now target the symmetric antecedent, not the one-sided one. The S6b PREP's Lean signature sketches all use `hreg : IsWitnessRegular G eps A B`, which is the wrong hypothesis.

S6c-ACT's iter 10 file-level docstring sketch on `witness_regular_symmetric_implies_epsilon_regular_small_eps` (line 799-823) names four sub-lemmas:

1. `vertexBias_A_average` — Cauchy–Schwarz over `a ∈ A` using `IsWitnessRegular`
2. `vertexBias_B_average` — dual using `Dual_IsWitnessRegular`
3. `markov_bad_count` — Markov on the per-vertex bias
4. `slack4_assemble` — final triangle inequality times `1 / (1 - 4·eps) ≤ 4/3` for `4·eps < 1/4`

but provides only English-prose signatures. This PREP pins each in concrete Lean syntax against `Proofs/SzemerediCoreOQ04.lean`'s symmetric Part 7 API (Dual_IsWitnessRegular, IsWitnessRegular_symmetric, witnessFamilyA), and identifies which Mathlib v4.26.0 lemma discharges each step.

The slow Docker build cycle (~30 min per attempt) + memory caution about "(build pending)" latent bugs motivate pinning **before** ACT iteration spins up.

## 2. Race awareness (audit at session start)

- `gh pr list --search "szemeredi-core-oq-04" --state open` → `[]`. No open PR on this slug.
- `gh pr list --state open --search "SzemerediCore"` → `[]`. No open PR touching the parent file either.
- Most recent merged PR on slug: PR #18959 (S6c-ACT iter 10, merged 2026-05-14 03:04 UTC).
- Branch register at push time: only merged historical S1–S6c branches; no `s7`, `s7-prep`, `s7-act`, `symmetric-second-moment`, or `cauchy-schwarz-refresh` branch.

This S7 PREP writes a previously-unused session-note filename and touches `state.md` / JSON only with a strict superset of iter 10 content (no rewrites). Conflict-free with all future ACT work on the slug.

## 3. The four S7 ACT helpers — pinned Lean signatures

All four signatures use the section-bound `G : SimpleGraph V`, `[DecidableRel G.Adj]`, `[DecidableEq V]`, `[Fintype V]` already opened in the file (lines 51-55).

### 3.1 `vertexBias_A_average` — first-moment bias bound over `A` from `IsWitnessRegular`

**Pinned signature**:
```lean
/-- **First-moment bias bound over `A`**: under one-sided witness-regular hypothesis,
the unrestricted sum of per-vertex biases over `A` against a fixed `B' ∈ witnessFamilyB`
is bounded by `eps · #A · #B`. Combined with Cauchy–Schwarz, this yields a second-moment
control of `vertexBias` over `A`.

This is the **A-side** ingredient; the dual `vertexBias_B_average` consumes the
`Dual_IsWitnessRegular` half.

References: S6c PREP §5 (PR #18595); ADLRY 1994 Lemma 3.4; Zhao §3.4. -/
lemma vertexBias_A_average
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hreg : IsWitnessRegular G eps A B)
    (hB : 0 < B.card) :
    (∑ a ∈ A, vertexBias G a A B) ≤ eps * A.card := by
  sorry  -- proof: average `IsWitnessRegular` constraints `|d(A, B') - d(A, B)| ≤ eps`
         -- across the family-of-witnesses partition of `B`, then apply `sq_sum_le_card_mul_sum_sq`
```

Estimated 30-50 LOC. Discharges via:
1. Expand `vertexBias` as `|edgeDensity G {a} B - edgeDensity G A B|`.
2. The neighbour-set decomposition `B = (B ∩ N(a)) ∪ (B \ N(a))` is a partition; the per-singleton density `d({a}, B) = |B ∩ N(a)| / |B|`.
3. The grid hypothesis on `B' = B ∩ N(a)` and `B' = B \ N(a)` (both in `witnessFamilyB G A B`) controls `|d(A, B') - d(A, B)|`; by averaging over `a ∈ A`, this transfers to `|d({a}, B) - d(A, B)|`.

**Open question (left for ACT)**: whether the `(B'.card : ℚ) ≥ eps * B.card` membership requirement of `IsWitnessRegular` forces a case-split on small `B' = B ∩ N(a)` (vertices with few neighbours). The S6c PREP §5 sketch handles this via the `Dual` direction; preserved as a free hypothesis here.

### 3.2 `vertexBias_B_average` — dual via `Dual_IsWitnessRegular`

**Pinned signature**:
```lean
/-- **First-moment bias bound over `B`** (dual to `vertexBias_A_average`): under the
dual witness-regular hypothesis, the unrestricted sum of per-vertex biases over `B`
against any `A' ∈ witnessFamilyA` is bounded by `eps · #B · #A`.

The dual ingredient is required because the one-sided `vertexBias_A_average` alone
fails on the counterexample of PR #18679 (where `witnessFamilyB` collapses but
`witnessFamilyA` separates the bimodal A-degrees). -/
lemma vertexBias_B_average
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hdual : Dual_IsWitnessRegular G eps A B)
    (hA : 0 < A.card) :
    (∑ b ∈ B, vertexBias_B G b A B) ≤ eps * B.card := by
  sorry  -- proof: mirror of `vertexBias_A_average` but with A/B swapped and using
         -- `witnessFamilyA` partition of A via `A' ∩ N(b)` neighbour sets
```

Estimated 30-50 LOC (mirror of 3.1).

**Side dependency**: requires a `vertexBias_B G b A B := |edgeDensity G A {b} - edgeDensity G A B|` definition, dual to the existing `vertexBias G a A B` (line 530). Sorry-free, 3 lines. Add directly above `vertexBias_B_average`.

### 3.3 `markov_bad_count` — Markov bound on `eps`-biased vertices in `A`

**Pinned signature**:
```lean
/-- **Markov on first-moment bias**: if `∑ a ∈ A, vertexBias G a A B ≤ eps · #A`, then
the count of `eps`-biased vertices is bounded by `#A` (trivial) — and squared by
Cauchy–Schwarz, the count of `eps²`-biased vertices is `≤ eps · #A`.

Composed with `vertexBias_A_average`, this is the entry point to the slack-4
restriction `|A' ∩ A_good| ≥ (1 - eps) · |A'|` for `A'` of size `≥ 4·eps·|A|`. -/
lemma markov_bad_count
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hbias : (∑ a ∈ A, vertexBias G a A B) ≤ eps * A.card) :
    ((A.filter (fun a => eps < vertexBias G a A B)).card : ℚ) ≤ A.card := by
  sorry  -- proof: `Finset.sum_le_card_nsmul` applied to the bad-set filter
         -- (eps < f a means f a ≥ eps, so #bad · eps ≤ ∑ f a ≤ eps · #A)
```

**Open question (left for ACT)**: the trivial Markov bound `#bad ≤ #A` is not strong enough — we need `#bad ≤ eps · #A` (the slack-4 averaging step). This requires a **second-moment** input `∑ vertexBias² ≤ eps² · #A`, then Markov on the squared bias gives `#{a : eps < vertexBias a} · eps² ≤ eps² · #A`, hence `≤ #A`. To improve to `eps · #A`, need `∑ vertexBias² ≤ eps³ · #A` (achievable via Cauchy–Schwarz on the first-moment bound).

The cleanest target signature is therefore:
```lean
lemma markov_bad_count_squared
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hbias_sq : (∑ a ∈ A, (vertexBias G a A B) ^ 2) ≤ eps ^ 2 * A.card) :
    ((A.filter (fun a => eps < vertexBias G a A B)).card : ℚ) ≤ A.card := by
  -- proof: ∑ bad eps² ≤ ∑ bad (vertexBias a)² ≤ eps² · #A, divide by eps² (heps > 0)
  sorry
```

Estimated 20-30 LOC. Discharges via `Finset.sum_le_card_nsmul` (at `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:210` — see §4.1).

### 3.4 `slack4_assemble` — triangle inequality + slack-4 absorption

**Pinned signature**:
```lean
/-- **Slack-4 assembly**: combine `vertexBias_A_average` + `markov_bad_count` + the
dual versions to derive `|edgeDensity G A' B' - edgeDensity G A B| ≤ 4 · eps` for
all `A' ⊆ A`, `B' ⊆ B` with `#A' ≥ 4·eps · #A`, `#B' ≥ 4·eps · #B`.

The slack-4 factor decomposes as 1 (per-vertex bias) + 1 (A-restriction) + 1 (B-restriction)
+ 1 (Cauchy–Schwarz slack from `(1 - 4·eps)⁻¹ ≤ 4/3` when `4·eps < 1/4`). -/
theorem witness_regular_symmetric_implies_epsilon_regular_small_eps
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  intro A' B' hA' hB' hcA' hcB'
  -- Step 1: extract IsWitnessRegular + Dual_IsWitnessRegular via hreg.toB / hreg.toA
  -- Step 2: vertexBias_A_average + markov_bad_count → |A' ∩ A_good| ≥ (1-eps) · |A'|
  -- Step 3: vertexBias_B_average + markov_bad_count_B → |B' ∩ B_good| ≥ (1-eps) · |B'|
  -- Step 4: density transfer on (A_good × B_good) bulk + bias on (A_bad ∪ B_bad) tail
  -- Step 5: triangle inequality + (1-4·eps)⁻¹ ≤ 4/3 absorption
  sorry
```

This **replaces** the sorry already in place at line 831, **not** a new sorry. Estimated 100-150 LOC for full discharge once 3.1-3.3 are sorry-free.

## 4. Mathlib v4.26.0 API surface (path drift since S6b PREP)

All four helpers route through three Mathlib lemmas, plus the existing slug-local Part 7 API.

### 4.1 `Finset.sum_le_card_nsmul` (additive Markov bound)

**Path at v4.26.0 pin `2df2f015...`**: `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:210` (verified via `gh api`).
**S6b PREP cited**: same file (no path drift).

**Statement** (from `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:210-214`):
```lean
@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card [MulLeftMono N] (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ #s := by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp
```

Additive form: `s.sum f ≤ #s • n` when `∀ x ∈ s, f x ≤ n`. Specialisation to `α = ℚ`: `s.sum f ≤ #s * n`. **No `[Fintype]` requirement.**

**Markov derivation in `markov_bad_count_squared`**:
1. Let `bad := A.filter (fun a => eps < vertexBias G a A B)`.
2. `bad.sum (fun a => eps^2) ≤ bad.sum (fun a => (vertexBias G a A B)^2)` by `Finset.sum_le_sum` (pointwise comparison via `sq_le_sq'` flipped).
3. `bad.sum (fun a => (vertexBias G a A B)^2) ≤ A.sum (fun a => (vertexBias G a A B)^2) ≤ eps^2 · #A` by `Finset.sum_le_sum_of_subset_of_nonneg` and the hypothesis.
4. `bad.sum (fun a => eps^2) = bad.card * eps^2`.
5. Cancel `eps^2 > 0` to get `bad.card ≤ #A`.

### 4.2 `sq_sum_le_card_mul_sum_sq` (Cauchy–Schwarz / Chebyshev)

**Path at v4.26.0 pin**: `Mathlib/Algebra/Order/Chebyshev.lean:137` (verified via `gh api`).
**S6b PREP cited**: `Mathlib/Algebra/Order/Chebyshev.lean:137-139`. No path drift.

**Statement**:
```lean
/-- Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz
Inequality**: The square of the sum is less than the size of the set times
the sum of the squares. -/
theorem sq_sum_le_card_mul_sum_sq :
    (∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2 := by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum
```

**Generality**: any `[LinearOrderedSemifield α]` (stronger ordered ring also accepted). Specialises to `α = ℚ` without extra hypotheses.

**Used in**: lifting first-moment bound to second-moment in `vertexBias_A_average`'s discharge of `markov_bad_count_squared`'s hypothesis `∑ vertexBias² ≤ eps² · #A`.

**Argument chain**:
1. `vertexBias_A_average` gives `(∑ a ∈ A, vertexBias a) ≤ eps · #A`.
2. By `sq_sum_le_card_mul_sum_sq`: `(∑ a ∈ A, vertexBias a)² ≤ #A · ∑ a ∈ A, vertexBias² a`.
3. Substituting: `(eps · #A)² ≤ #A · ∑ vertexBias² a`, hence `∑ vertexBias² a ≥ eps² · #A`.
4. But Markov needs `∑ vertexBias² a ≤ const · #A`, not `≥`. The Cauchy–Schwarz direction in `sq_sum_le_card_mul_sum_sq` is the **wrong direction** for this step.

**Correction (post S6b PREP)**: `sq_sum_le_card_mul_sum_sq` does not directly produce `∑ vertexBias² ≤ const · #A`. The correct route is:
- **Second-moment input from `IsWitnessRegular`** is the load-bearing step; Cauchy–Schwarz is **downstream** of it.
- The S6c PREP-2 obstruction (PR #18679) confirmed that one-sided `IsWitnessRegular` does **not** suffice to produce `∑ vertexBias² ≤ const · eps² · #A`; the bimodal-A-degree counterexample violates the second-moment bound.
- The **symmetric** `IsWitnessRegular_symmetric` rescues the second-moment input via the dual half — the dual A-side ε-grid `witnessFamilyA` separates the bimodal A-degrees.

This PREP **does not** discharge the second-moment derivation — that is the load-bearing mathematical content of `vertexBias_A_average`'s actual proof, left for S7 ACT. What this PREP pins is the **downstream chain** from second-moment to slack-4.

### 4.3 `sum_mul_sq_le_sq_mul_sq` (full Cauchy–Schwarz, squared)

**Path at v4.26.0 pin**: `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:209` (verified).
**S6b PREP cited**: `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:149-154`. **Path drift: +60 lines** (the surrounding `sum_sq_le_sum_mul_sum_of_sq_eq_mul` helper at line 185 was added between v4.25 and v4.26.0).

**Statement** (lines 209-214):
```lean
/-- **Cauchy-Schwarz inequality** for finsets, squared version. -/
lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ mul_pow ..)
```

**Used in**: `slack4_assemble` step 4 — density transfer on `A_good × B_good`. Take `f a := vertexBias G a A B`, `g a := 𝟙[a ∈ A' ∩ A_good]`. Yields:
```
(∑_{a ∈ A' ∩ A_good} vertexBias a)² ≤ (∑_{a ∈ A} vertexBias² a) · (∑_{a ∈ A} 𝟙[a ∈ A' ∩ A_good]²)
                                    = (∑_a vertexBias² a) · |A' ∩ A_good|
```
Square-rooting (or staying with squared forms — Lean prefers the latter to avoid `Real.sqrt` on `ℚ`), the RHS is `√(|A' ∩ A_good|) · √(∑ vertexBias²)`.

### 4.4 `Finset.sum_le_sum_of_subset_of_nonneg` (subset sum monotonicity)

**Path at v4.26.0 pin**: `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:131` (verified). No drift since S6b.

**Used in**: every helper, for restricting Finset sums to subsets and dropping the rest.

### 4.5 Mathlib regularity precedent — `Mathlib/Combinatorics/SimpleGraph/Regularity/Chunk.lean`

**Path at v4.26.0 pin**: `Mathlib/Combinatorics/SimpleGraph/Regularity/Chunk.lean` (verified; size 27267 bytes).

S6b PREP §6 cited `Chunk.lean` as the precedent for the conceptual slot. Re-verified at v4.26.0:
- `density_sub_eps_le_sum_density_div_card` at `Chunk.lean:242` (verified line; S6b cited 217 — **drift +25**)
- `sum_density_div_card_le_density_add_eps` at `Chunk.lean:279` (verified line; S6b cited 254 — **drift +25**)
- `average_density_near_total_density` at `Chunk.lean:318` (verified line; S6b cited 293 — **drift +25**)

The uniform +25 drift suggests a single Mathlib batch insertion above `density_sub_eps_le_sum_density_div_card` between v4.25 and v4.26.0. This is **not blocking** for the S7 ACT route (we do not directly call these `private` Chunk-internal lemmas; we follow their **proof technique**, not their **API**).

## 5. The second-moment input — where the symmetric variant matters

The load-bearing question for `vertexBias_A_average` is:

> Given `IsWitnessRegular G eps A B`, can we derive `∑ a ∈ A, vertexBias² a ≤ const · eps² · #A`?

S6c PREP §3.1 (PR #18595) and S6c PREP-2 §5 (PR #18679) prove the answer is **NO** for the one-sided variant — bimodal `A`-degree distributions violate the bound. **YES** for the symmetric variant — the dual `Dual_IsWitnessRegular` controls the `A`-side bimodality directly.

**Lean-side route** (sketch, for S7 ACT):

1. Decompose `vertexBias² a = (d({a},B) - d(A,B))²`. Expand the square as `d({a},B)² - 2·d({a},B)·d(A,B) + d(A,B)²`.

2. Sum over `a ∈ A`: `∑ a ∈ A, vertexBias² a = ∑ d({a},B)² - 2·d(A,B)·∑ d({a},B) + #A · d(A,B)²`.

3. Note `∑ a ∈ A, d({a},B) = #A · d(A,B)` (this is the definition of edge density via partition into singletons; sorry-free, follows from `SimpleGraph.edgeDensity_def` + `Finset.sum`). So:
   ```
   ∑ a ∈ A, vertexBias² a = ∑ d({a},B)² - #A · d(A,B)²
   ```

4. The hard direction is bounding `∑ d({a},B)²`. Decompose `d({a},B) = |B ∩ N(a)| / #B = ⟨B(a), 1_B⟩ / (#B · 1)` where `B(a)` is the characteristic function of `B ∩ N(a)`. Then:
   ```
   ∑ a ∈ A, d({a},B)² = (1/#B²) · ∑ a ∈ A, |B ∩ N(a)|²
   ```

5. Apply `Dual_IsWitnessRegular` here: it controls `|edgeDensity G A' B - edgeDensity G A B| ≤ eps` for `A' ∈ witnessFamilyA G A B`. Specifically, `witnessFamilyA = {A.filter (Adj b)} ∪ {A.filter (¬ Adj _ b)} ∋ B(a)` for `a ∈ B`. Wait — `witnessFamilyA` indexes by `b ∈ B`, but we are summing over `a ∈ A`. **Crossing the type boundary requires the second-moment lift on A.**

**Cleaner Lean-side route** (deferred to S7 ACT, ~50 LOC each):

The Chunk.lean precedent at line 242-318 uses a different technique — it works in the **chunked** finpartition, not the `singleton` decomposition. Adapting to OQ04's surrogate requires a sub-lemma:

```lean
/-- **Second-moment via grid**: under symmetric witness regularity, the per-vertex
A-side bias has bounded second moment. -/
lemma vertexBias_sq_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hreg : IsWitnessRegular_symmetric G eps A B) :
    (∑ a ∈ A, (vertexBias G a A B) ^ 2) ≤ 4 * eps ^ 2 * A.card := by
  sorry  -- proof: combine IsWitnessRegular control of d(A, B') and Dual_IsWitnessRegular
         -- control of d(A', B), sum over the pair-product family A' × B' ∈ witnessFamilyA × witnessFamilyB
```

The constant `4 = 2 · 2` arises from `witnessFamilyA.card ≤ 2 · #B` × `witnessFamilyB.card ≤ 2 · #A`; the asymptotic order `eps² · #A` is the correct second-moment scaling.

**This** is the helper that should land first in S7 ACT — once `vertexBias_sq_sum_le` is sorry-free, the chain 4.1 → 4.2 → 4.3 in §3.1-3.4 closes mechanically.

## 6. The slack-4 absorption — `(1 - 4·eps)⁻¹ ≤ 4/3` calculation

The final assembly step in `slack4_assemble` uses an inequality:

> For `0 < eps < 1/4`, `(1 - 4·eps)⁻¹ ≤ 4 / 3`.

This is **false** in general — `(1 - 4·eps)⁻¹` blows up as `eps → 1/4`. The correct form is:

> For `0 < eps ≤ 3/16` (i.e. `4·eps ≤ 3/4`, hence `1 - 4·eps ≥ 1/4`), `(1 - 4·eps)⁻¹ ≤ 4`.

For `eps ≤ 1/12`, `1 - 4·eps ≥ 2/3`, so `(1 - 4·eps)⁻¹ ≤ 3/2`. The S6c-ACT iter 10 docstring's "`≤ 4/3` when `4·eps ≤ 1/4`" is imprecise — it should be **`(1 - 4·eps)⁻¹ ≤ 4/3` when `4·eps ≤ 1/4 → 1 - 4·eps ≥ 3/4`** which IS correct, since `(3/4)⁻¹ = 4/3`. So `4·eps ≤ 1/4` is the precondition, not `4·eps < 1`.

**Implication for S7 ACT**: the small-eps regime needs `4·eps < 1/4` (a strictly tighter hypothesis than the file-level `4·eps < 1`), OR the slack constant grows. The file currently uses `hsmall : 4 * eps < 1` (line 826), which is too loose for the `4/3` slack absorption.

**Recommended state-of-the-art**:
- Tighten `hsmall : 4 * eps < 1` to `hsmall_quarter : 4 * eps ≤ 1/4` (equivalently `eps ≤ 1/16`) for the second-moment-Cauchy-Schwarz route to absorb cleanly.
- The remaining gap `1/16 < eps < 1/4` would then need either (a) a different slack constant in `slack4_assemble` or (b) a separate proof technique. ADLRY 1994 Lemma 3.4 actually proves the result for `eps ≤ 1/16` and combines with the trivial regime via a degraded constant (the actual ADLRY constant is `200·eps^(1/5)` or similar — fine for asymptotic complexity but loose).

This is a **mathematical scope decision** for S7 ACT, not a Mathlib API issue. Documented here so the ACT does not get blindsided.

## 7. Iter 10 build-verified status correction

State.md iter 10 entry says "Build pending Docker wrapper (slow Mathlib cache fetch)" but PR #18959's body §"Build status" reports "Build verified on 2026-05-14 via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`: ... `Build completed successfully (7744 jobs)`. Only warnings (linter unused section variables) and the documented sorry."

The PR was authored by researcher-9 — same agent ID as this PREP author. State.md was not updated post-build because the iter-10 ACT was the same session that wrote state.md; the build finished after the state.md write. Subsequent doc-only iterations did not pick up the build-verified status.

This PREP corrects the iter 10 entry in state.md to "build verified" with explicit reference to PR #18959 §"Build status". JSON `currentState.focus` likewise gets a one-word swap: "Build pending Docker wrapper" → "Build verified locally (7744 jobs)".

## 8. Files this PREP modifies

- `research/problems/szemeredi-core-oq-04/sessions/2026-05-14-s7-prep-symmetric-second-moment-api-refresh.md` (new, this file).
- `research/problems/szemeredi-core-oq-04/state.md` — iter 11 PREP entry (~80 lines added), plus iter 10 build-status one-word swap.
- `src/data/research/problems/szemeredi-core-oq-04.json` — `currentState.{iteration: 10 → 11, since, focus, nextAction}`, `knowledge.{progressSummary, nextSteps}` updated to reflect this PREP. `lastUpdate` bumped.

## 9. What this PREP does NOT do

- **No** Lean source changes to `Proofs/SzemerediCoreOQ04.lean`. The two sorries (line 291 archival + line 831 symmetric) remain in place.
- **No** `problem.md` headline revision. The S6c-PREP-4 / symmetric-as-headline pass remains deferred (iter 9 STATE-SYNC noted it as "out of scope to keep narrow"; iter 10 noted it as "S7 PREP lower priority"). Still out of scope here — this PREP focuses on Mathlib API refresh + status correction.
- **No** new helper Lean signatures shipped — the four §3 signatures are Lean syntax for forecasting only; they are **not** added to the `.lean` file. ACT iteration will add them.
- **No** changes to JSON `builtItems`, `insights`, `attemptCounts`, `mathematicalContent`, or any field outside `currentState` / `knowledge.{progressSummary,nextSteps}` / `lastUpdate`.

## 10. Recommended next ACT increment (S7 ACT-α, ≤ 100 LOC)

If S7 ACT-full (`witness_regular_symmetric_implies_epsilon_regular_small_eps` sorry-free, ~250 LOC) is too ambitious for one session, the **minimum useful ACT increment** is `vertexBias_sq_sum_le` (the §5 helper). Estimated 80-120 LOC:

1. Define `vertexBias_B G b A B := |edgeDensity G A {b} - edgeDensity G A B|` (3 LOC, sorry-free).
2. Prove `edgeDensity G {a} B = |B ∩ G.neighborSet a| / #B` (5 LOC, sorry-free, expansion).
3. Prove `∑ a ∈ A, edgeDensity G {a} B = #A * edgeDensity G A B` (10 LOC, sorry-free, partition sum).
4. Prove `∑ a ∈ A, (edgeDensity G {a} B)² ≤ (4 · eps² + (edgeDensity G A B)²) · #A` (60-80 LOC, **sorry-bearing**, applies `IsWitnessRegular_symmetric` to the pair-product family).
5. Derive `∑ a ∈ A, vertexBias² a ≤ 4 · eps² · #A` from step 4 + step 3 algebra (10 LOC, sorry-free).

This is a substantive forward move on `_small_eps` without committing to the full slack-4 assembly.

## 11. Provenance / open-PRs / branch register check (push-time race window)

At session-end push time:
- `gh pr list --search "szemeredi-core-oq-04 in:title" --state open` → `[]`.
- `gh pr list --state open --search "SzemerediCore in:title"` → `[]` (verified separately).
- Most recent merged szemeredi-core-oq-04 PR: #18959 (S6c-ACT iter 10, 2026-05-14 03:04 UTC).
- This PR's branch (push-time): `research/szemeredi-core-oq04-s7-<unix-ts>` (will not collide with any existing branch).
- Session log filename `2026-05-14-s7-prep-symmetric-second-moment-api-refresh.md`: unique under `sessions/` (verified — only the four S6 PREP entries + one S6c-ACT entry exist).

**Conflict-free.** Doc-only. Zero overlap with the S6 / S6b / S6c / S6c-2 / S6c-ACT merged work.
