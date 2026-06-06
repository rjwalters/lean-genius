# Session 4 — Iter 4 PREP-1 — Mathematical correctness analysis of the proposed S4 ACT iff (Sub-Milestone B+)

**Date**: 2026-06-05 (researcher-1, T+3d post-iter-3 metadata cleanup)
**Branch**: `research/bertrands-postulate-oq-02-iter4-gap-bound-asymmetry`
**Type**: PREP / doc-only (no Lean edits)
**Result**: The proposed S4 iff statement is **NOT a true equivalence** at the level of pure logic from `LegendreConjecture`. Reverse direction holds; forward direction is provably weaker. Concrete corrected plan below.

## 1. Background

Iter 3 (2026-06-02, researcher-1) was a metadata-cleanup OBSERVE that left a single concrete S4 ACT recommendation in `state.md` and the canonical JSONs:

> **S4 ACT — Sub-Milestone B+ — `LegendreConjecture` ↔ prime-gap bound.**
>
> State and prove:
>
> ```lean
> theorem legendre_iff_primeGap :
>     LegendreConjecture ↔
>       ∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
>         ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1
> ```

This PREP-1 audits the mathematical statement before committing ~100–180 LOC of Lean to formalize a potentially false claim. The audit was prompted by a routine "does each direction actually go through?" pre-flight check, standard for any proposed iff.

## 2. Audit method

For each direction, derive the bound from the hypothesis using only the abstract statements (Legendre at `n` = "∃ prime in `(n², (n+1)²)`"). No appeal to specific small-prime computations; the question is what is **logically derivable** from `LegendreConjecture` alone.

## 3. Reverse direction — PROVABLE (gap bound ⟹ Legendre)

**Claim**: `(∀ k, p_{k+1} - p_k ≤ 2 * Nat.sqrt p_k + 1) → LegendreConjecture`.

**Proof sketch** (for any `n ≥ 1`, find a prime in `(n², (n+1)²)`):

- **Case `n = 1`**: prime `2` lies in `(1, 4)` ✓ (one-line witness, no gap-bound use needed).
- **Case `n ≥ 2`**: `n²` is composite (since `n² = n · n` with `1 < n < n²`). Let `p_k` be the
  largest prime with `p_k ≤ n²`. Then `p_k ≤ n² - 1` (strict, since `n²` is not prime) and
  no prime sits in `(p_k, n²]`, hence the next prime `p_{k+1}` satisfies `p_{k+1} > n²`.

  Applying the gap-bound hypothesis at this `k`:

  ```
  p_{k+1} ≤ p_k + 2 · Nat.sqrt p_k + 1
        ≤ (n² - 1) + 2 · Nat.sqrt (n² - 1) + 1
        = n² + 2 · Nat.sqrt (n² - 1)
        ≤ n² + 2(n - 1)        [since Nat.sqrt (n² - 1) ≤ n - 1 for n ≥ 1]
        = n² + 2n - 2
        < n² + 2n + 1
        = (n + 1)².
  ```

  Combined with `p_{k+1} > n²`, we have `n² < p_{k+1} < (n+1)²` with `p_{k+1}` prime,
  i.e., `LegendreAt n` holds. ✓

**Verdict**: the reverse direction is correct. The 2√p+1 bound is **sufficient** for Legendre.

## 4. Forward direction — NOT provable from `LegendreConjecture` alone

**Claim under audit**: `LegendreConjecture → ∀ k, p_{k+1} - p_k ≤ 2 * Nat.sqrt p_k + 1`.

**Best one can derive from Legendre alone**: gap ≤ `4 * Nat.sqrt p_k + 2`. Sketch:

Take any prime `p_k`. Let `m := Nat.sqrt p_k`, so `m² < p_k < (m+1)²` (strict on both
sides: `p_k > m²` because primes ≥ 2 are never perfect squares, and `p_k < (m+1)²`
by definition of `Nat.sqrt`).

Legendre at `m` gives a prime `q ∈ (m², (m+1)²)`. Two subcases:

### Subcase A: `q > p_k`

Then `p_{k+1} ≤ q < (m+1)² = m² + 2m + 1`, so

```
p_{k+1} - p_k < (m+1)² - p_k ≤ (m+1)² - (m² + 1) = 2m,
```

giving `p_{k+1} - p_k ≤ 2m - 1 ≤ 2 · Nat.sqrt p_k + 1`. ✓ (this subcase satisfies the
proposed bound)

### Subcase B: `q ≤ p_k`

Legendre at `m` is satisfied by some prime `q ≤ p_k` (possibly `q = p_k` itself, possibly
one of `p_{k-1}, p_{k-2}, …` lying in `(m², (m+1)²)`). It does **not** follow that any prime
exists in `(p_k, (m+1)²)`. The smallest prime `> p_k` could lie at or beyond `(m+1)²`.

Falling back to Legendre at `m+1`: there is a prime `q' ∈ ((m+1)², (m+2)²)`, so
`p_{k+1} ≤ q' ≤ (m+2)² - 1 = m² + 4m + 3`, giving

```
p_{k+1} - p_k ≤ m² + 4m + 3 - p_k ≤ 4m + 2 = 4 · Nat.sqrt p_k + 2.
```

In Subcase B, the proposed bound `≤ 2 · Nat.sqrt p_k + 1` is exceeded by up to a factor
of `~2`. **`LegendreConjecture` does not rule out Subcase B**: the abstract conjecture
only asserts *some* prime exists in each `(n², (n+1)²)`, not that *every* prime is
followed by another prime in the same square interval.

### Concrete witness that Subcase B is logically consistent with Legendre

Consider the hypothetical "prime distribution" (purely as a logical scenario over `Nat.Prime`-like predicates):

- Primes ≤ `m² + 1` are some set `{…, p_k = m² + 1}`.
- No primes in `(m² + 1, (m+1)²]`.
- Primes in `((m+1)², (m+2)²]` start at, say, `(m+1)² + δ` for small `δ ≥ 1`.

For this scenario:
- Legendre at `m`: satisfied (by `p_k = m² + 1`).
- Legendre at `m + 1`: satisfied (by `(m+1)² + δ`).
- Gap `p_{k+1} - p_k = (m+1)² + δ - (m² + 1) = 2m + δ`, which for `δ ≥ 2` exceeds
  `2 · Nat.sqrt p_k + 1 = 2m + 1`.

Of course, the **actual** primes (as predicates on `ℕ`) might or might not contain
such a configuration. Empirically they do not (max known prime gap for `p_k ≤ 10^18`
is ≤ 1550, while `2√p_k + 1 ≈ 2 · 10^9 + 1`). But this empirical fact is **stronger
than `LegendreConjecture`** and cannot be derived from the abstract conjecture in Lean.

### Why this is not a Mathlib API gap

The obstruction is mathematical, not formal-Lean. No Mathlib lemma "Legendre implies
no large prime-gap" exists because the implication is not true at the abstract level.
The actual primes happen to satisfy strong gap bounds, but proving any specific gap
bound requires direct analytic-number-theory tools (Hoheisel, Huxley, BHP), not the
abstract Legendre hypothesis.

## 5. Corrected statement of the equivalence

The clean mathematical equivalence (precisely as it appears in Granville 1995,
re-derived here):

```
LegendreConjecture
  ↔ ∀ n ≥ 1, (the smallest prime > n²) < (n + 1)²
  ↔ ∀ n ≥ 1, ∃ k, p_k ≤ n² ∧ p_{k+1} < (n + 1)²
```

These are obvious **restatements** of Legendre (changing `∃ prime` to "some prime in
the gap" or "next prime"); they do not bridge to a gap bound `g(p_k) ≤ f(p_k)` in
either direction without losing logical content.

The **prime-gap bound** `g(p_k) ≤ 2√p_k + 1` is **strictly stronger** than Legendre.
A clean Lean record of this would be a **one-way** implication:

```lean
theorem prime_gap_sqrt_bound_implies_legendre
    (h : ∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
            ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1) :
    LegendreConjecture
```

with a paired **non-implication note** (Lean comment, not a theorem) that
`LegendreConjecture` does *not* logically imply this gap bound.

## 6. Implications for the next picker — corrected S4 plan

### 6.1 Corrected S4-ACT-α (the salvageable Lean deliverable)

Replace the iff by the one-way implication

```lean
theorem prime_gap_sqrt_bound_implies_legendre :
    (∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
          ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1) →
    LegendreConjecture
```

Expected size: **~80–130 LOC** in a new file
`proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`. 0 new axioms expected.

Lean dependencies (all already in repo or Mathlib):
- `Nat.nth Nat.Prime k`, `Nat.nth_count`, `Nat.count_nth_of_infinite` — Mathlib
- `Nat.primeCounting`, `Nat.exists_prime_le`, `Nat.findGreatest_*` API
- iter-2 `Proofs.LegendreGapEquivalence` bridge (`legendreAt_iff_halfOpen`)

Main risk: the "largest prime ≤ n²" idiom needs careful Mathlib API navigation
(`Nat.findGreatest` over `Nat.primeCounting`, or equivalent via `Nat.nth Nat.Prime`).
Two-three iterations to land cleanly is plausible.

### 6.2 NEW — Comment / docstring deliverable

In the same file, record the **non-implication direction** as a structured comment
(NOT a theorem):

```lean
/-! ## Non-equivalence note

`LegendreConjecture` does NOT imply this gap bound. The worst case under Legendre
yields only `g(p_k) ≤ 4 * Nat.sqrt p_k + 2`. See
`research/problems/bertrands-postulate-oq-02/sessions/2026-06-05-iter4-prep-1-gap-bound-asymmetry.md`
for the audit. -/
```

This preserves the mathematical finding in the Lean source for any reader who
picks up the file expecting an iff.

### 6.3 Anti-candidates promoted from S4 backlog

- **`legendre_iff_primeGap`** (the original iff) — promoted from
  TARGET → **ANTI-CANDIDATE**. Not formalizable: forward direction is mathematically
  false at the level of `LegendreConjecture` alone.

### 6.4 Status of S5 (Cramér ⇒ Legendre)

Sub-Milestone A (Cramér's conjecture ⇒ Legendre, for sufficiently large `n`) is
**unaffected** by this PREP-1. It remains a candidate for a later iteration after
the corrected S4-ACT-α lands.

## 7. Deliverables (this PR — doc-only)

1. **THIS session memo** (new): `sessions/2026-06-05-iter4-prep-1-gap-bound-asymmetry.md`.
2. `state.md`: prepend a Session 4 head block summarizing this PREP-1 finding and the
   corrected S4 plan.
3. `meta.json`: `currentState.iteration` 3 → 4; `currentState.since`, `currentState.focus`,
   `currentState.nextAction` updated; `attemptCounts.total` 3 → 4;
   `attemptCounts.currentApproach` 1 → 2 (PREP is a new approach within S4);
   `attemptCounts.approachesTried` 2 → 3 (corrected-plan PREP is approach #3).
4. `src/data/research/problems/bertrands-postulate-oq-02.json`: same `currentState`
   updates; `knowledge.progressSummary` prepend with the PREP-1 finding;
   `knowledge.nextSteps[0]` rewritten from the wrong iff to the corrected one-way
   implication; `knowledge.insights[]` prepend the asymmetry observation;
   `lastUpdate` 2026-05-30 → 2026-06-05.
5. No Lean edits. No gallery `meta.json` edits (Bertrand-family entries unaffected).
6. No `pnpm build` (no gallery deltas in this PREP).

## 8. Why this PREP is worth its own iteration slot

The naive read of state.md after iter 3 would have a researcher commit ~150 LOC of
Lean trying to prove a false implication, then either (a) reach a wall during the
forward direction and `sorry` it, (b) accidentally bake a strong gap hypothesis into
the Lean proof and present it as derived from Legendre, or (c) circle back to this
analysis after wasting a session.

A 10-minute audit before committing is the standard pre-flight for any iff. The
slug's anti-axiom policy and 0-sorries posture make accidental scaffolding around a
false forward direction especially expensive — it would either inflate the axiom
count (path b) or leave a sorry blot in an otherwise clean file (path a). PREP-1
catches the issue at zero Lean cost.

## 9. Honest size assessment

- This PR: ~250 LOC of markdown + JSON diff. 0 Lean. 0 axioms. 0 sorries.
- Mathematical content: catches an error in the proposed S4 plan and replaces it
  with a corrected one-way implication of comparable Lean-LOC budget (~80–130 LOC,
  still feasible single-cycle for the next picker).
- This is a **PREP**, not an ACT — the Lean iff `prime_gap_sqrt_bound_implies_legendre`
  remains the next picker's slot.

## 10. References

- Granville, A. "Harald Cramér and the distribution of prime numbers,"
  *Scand. Actuar. J.* (1995). The careful reading shows Granville's "Legendre is
  equivalent to" wording is used in the loose "morally equivalent / motivated by"
  sense, not a strict logical iff.
- Tao, T. "Structure and randomness in the prime numbers" (2007). Same observation:
  Legendre is *not* implied by RH, and conversely RH + Cramér-type gap bounds are
  not implied by Legendre.
- `proofs/Proofs/LegendrePartial.lean:148` — declares `legendre_conjecture` as the
  single axiom this slug carries forward.
- `proofs/Proofs/LegendreGapEquivalence.lean` — iter-2 deliverable; the three pointwise
  reformulations of Legendre (gap, distance, half-open). All structural; no gap-bound
  content. The `legendreAt_iff_halfOpen` lemma at line 97 will be reused by the
  corrected S4-ACT-α implementation.
- `proofs/Proofs/PrimeGapBounds.lean:123` — `nth_prime_succ_le_of_prime_gt`, the
  order-preserving enumeration lemma used by the forward step of the
  to-be-corrected S4-ACT-α proof.
