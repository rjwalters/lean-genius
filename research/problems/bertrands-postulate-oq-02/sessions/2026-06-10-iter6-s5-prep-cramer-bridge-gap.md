# Session 6 — Iter 6 S5 PREP — Cramér⇒Legendre bridging gap & refined iter-5 variant

**Date**: 2026-06-10 (researcher-9, T+4d post-iter-5 S4-ACT-α)
**Branch**: `research/bertrands-postulate-oq-02-iter6-s5-prep-cramer-bridge`
**Type**: PREP / doc-only (no Lean edits)
**Result**: The previous picker's claim that "Cramér ⇒ Legendre cleanly
factors through `prime_gap_sqrt_bound_implies_legendre`" is **incomplete**.
A structural mismatch exists between Cramér's "eventually" quantifier and
iter-5's `∀ k` hypothesis. The bridge is closable (no mathematical gap),
but requires a **refined variant of iter-5** taking `∀ k ≥ k₀`, which
this memo specifies. A concrete numerical analysis confirms the
`legendre-partial` n = 1..20 finite-tail covers the post-threshold regime
with margin.

## 1. Background

Iter 5 (2026-06-06, researcher-1) shipped `LegendrePrimeGapSqrtBoundSuffices.lean`:

```lean
def PrimeGapSqrtBound : Prop :=
  ∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
       ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1

theorem prime_gap_sqrt_bound_implies_legendre :
    PrimeGapSqrtBound → LegendreConjecture
```

The iter-5 session memo recommended S5 ACT — Cramér ⇒ Legendre — and
asserted (§7 next picker's slot):

> Now that `prime_gap_sqrt_bound_implies_legendre` is in place, the route
> to Cramér⇒Legendre **cleanly factors**:
> ```
> Cramér's conjecture
>   ⟹ (for sufficiently large k) p_{k+1} - p_k ≤ C·(log p_k)² ≤ 2·√p_k + 1
>   ⟹ LegendreConjecture (via prime_gap_sqrt_bound_implies_legendre, modulo
>                           the finite tail for small k handled by legendre-partial)
> ```

This PREP-2 audit is a pre-flight check on that asserted clean factorisation,
in the same spirit as iter-4 PREP-1 (which caught the asymmetry of the
iter-3 proposed iff). The motivation is identical: before committing
+200-250 LOC of Lean, verify that the type signatures actually compose.

## 2. The structural mismatch

**iter-5's hypothesis is `∀ k`** (universally quantified over all prime
indices, k = 0, 1, 2, …):

```lean
def PrimeGapSqrtBound : Prop :=
  ∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
       ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1
```

**Cramér's conjecture is `∀ k ≥ k₀`** (asymptotic / eventually):

> *Cramér (1936, strong form)*: there exists `C ≥ 1` such that for every
> `ε > 0` there exists `k₀ = k₀(ε)` with
> `p_{k+1} - p_k ≤ (C + ε) · (log p_k)²` for all `k ≥ k₀`.

(Granville 1995 refines the optimal constant to `C = 2 · e^{-γ} ≈ 1.1229`,
but the existential `k₀` is intrinsic to *every* form of Cramér — there is
no "for all k" form. The bound fails at small k: p₀ = 2, p₁ = 3, gap = 1,
but `1 · (log 2)² ≈ 0.48 < 1`, so even C = 1 doesn't dominate the small-k gap.)

The iter-5 hypothesis says nothing about an "eventually": the bound is
asked to hold at *every* k. So a hypothetical proof of Cramér does *not*
directly satisfy `PrimeGapSqrtBound` — it satisfies only the restriction
to `k ≥ k₀(C)` for the chosen `C` and the asymptotic threshold.

## 3. Numerical analysis: where does C·log²p ≤ 2·√p + 1 hold?

The "second step" `C · (log p_k)² ≤ 2·√p_k + 1` is the arithmetic step
the previous picker glossed over. Concrete values (Python; `p` in primes is
representative, the inequality is monotone in `p`):

| p    | log²p      | C=1: C·log²p | C=2e^{-γ}: C·log²p | 2·√p + 1 | OK (C=1) | OK (Granville) |
|------|-----------:|-------------:|-------------------:|---------:|---------:|---------------:|
| 50   |   15.30    |       15.30  |             17.19  |    15.14 | ✗        | ✗              |
| 100  |   21.21    |       21.21  |             23.81  |    21.00 | ✗        | ✗              |
| 121  |   23.04    |       23.04  |             25.87  |    23.00 | ✓        | ✗              |
| 150  |   25.11    |       25.11  |             28.19  |    25.49 | ✓        | ✗              |
| 250  |   30.49    |       30.49  |             34.23  |    32.62 | ✓        | ✗              |
| 358  |   34.36    |       34.36  |             38.59  |    38.85 | ✓        | ✓              |
| 400  |   35.90    |       35.90  |             40.31  |    41.00 | ✓        | ✓              |
| 500  |   38.62    |       38.62  |             43.37  |    45.72 | ✓        | ✓              |
| 1000 |   47.72    |       47.72  |             53.58  |    64.25 | ✓        | ✓              |

**Threshold `p₀(C)`** (smallest `p` with `C · log²p ≤ 2·√p + 1`, computed
by linear search):

| C                         | p₀(C) | corresponding k₀ (≈ π(p₀) - 1, 0-indexed) |
|---------------------------|------:|------------------------------------------:|
| 1.0     (Cramér original) | 121   | π(121) - 1 = 30 - 1 = **29** (p₂₉ = 113)   |
| 1.1229  (Granville opt.)  | 358   | π(358) - 1 = 71 - 1 = **70** (p₇₀ = 353)   |

So:

- With the optimistic Cramér constant `C = 1`, the asymptotic bound holds
  for primes `p_k ≥ 121`, i.e. for `k ≥ 29`.
- With the (conjecturally optimal) Granville constant `C = 2e^{-γ}`, the
  asymptotic bound holds for primes `p_k ≥ 358`, i.e. for `k ≥ 70`.

The `(log p)²` vs `√p` race is asymptotic in `p`, not arithmetic in `k`;
both constants give thresholds well within reach.

## 4. Compatibility with `legendre-partial`

`legendre-partial` (`proofs/Proofs/LegendrePartial.lean`) currently
discharges `LegendreAt n` for **n = 1, 2, …, 20** via `native_decide` on
explicit witnesses (e.g. `legendre_20 : LegendreAt 20 := ⟨401, by native_decide⟩`).

What does iter-5 actually *need* the gap bound at?

The proof for `LegendreAt n` (`n ≥ 2`) picks
`k(n) := Nat.findGreatest (fun k => p_k ≤ n²) n²`, i.e. the index of the
largest prime ≤ n². So the gap bound is used at exactly one `k(n)` per
`n ≥ 2`. Numerically:

| n  | n²  | k(n) = π(n²) - 1 | p_{k(n)} (largest prime ≤ n²) |
|----|----:|------------------:|------------------------------:|
| 2  |   4 |  1                |    3                          |
| 3  |   9 |  3                |    7                          |
| 10 | 100 | 24                |   97                          |
| 20 | 400 | 77                |  397                          |
| 21 | 441 | 84                |  439                          |
| 25 | 625 | 113               |  619                          |
| 30 | 900 | 153               |  887                          |

So `k(n)` is strictly increasing in `n`. **For `n ≥ 21`, `k(n) ≥ 84`**, which
exceeds both numerical thresholds k₀(C=1) = 29 and k₀(Granville) = 70.

**The finite-tail/asymptotic split is therefore consistent**:

- **legendre-partial covers `n = 1..20`** (closed-form witnesses; no
  appeal to the gap bound needed).
- **iter-5 + Cramér's eventual gap bound covers `n ≥ 21`** (`k(n) ≥ 84`,
  well above the Cramér threshold for any plausible `C`).

There is **no mathematical gap**. The existing `n = 1..20` coverage in
`legendre-partial` already overlaps the asymptotic regime with room to
spare. The previous picker was correct that the route works *as a route*;
what they missed is that the iter-5 *theorem* as stated does not directly
accept the Cramér output, due to the quantifier mismatch.

## 5. Concrete remediation: refined iter-5 variant

The cleanest fix is a new theorem next to the existing iter-5 result —
the existing `prime_gap_sqrt_bound_implies_legendre` is preserved as a
special case.

### 5.1. Type signature (recommended)

```lean
/-- **Refined iter-5**: if the gap bound holds at every prime index `k`
    *with `p_k ≥ M`*, and `LegendreAt n` is verified for every `n` with
    `n² < 2·M`, then `LegendreConjecture` holds.

    Specialises to iter-5's `prime_gap_sqrt_bound_implies_legendre` when
    `M = 0` (the gap-above hypothesis becomes `∀ k`, and the
    finite-tail hypothesis is vacuous since `n² < 0` is false for `n ≥ 1`). -/
theorem prime_gap_sqrt_bound_above_implies_legendre
    (M : ℕ)
    (h_gap_above : ∀ k, M ≤ Nat.nth Nat.Prime k →
                   Nat.nth Nat.Prime (k+1) - Nat.nth Nat.Prime k
                     ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1)
    (h_legendre_below : ∀ n, 1 ≤ n → n^2 < 2*M → LegendreAt n) :
    LegendreConjecture
```

### 5.2. Proof outline

Fix `n ≥ 1`. Two cases:

1. **`n² < 2·M`**: directly apply `h_legendre_below n hn this`.
2. **`n² ≥ 2·M`** (and `n ≥ 2`, since `n = 1, M = 0` reduces to case 1
   when M = 0, and otherwise is a small special case):
   - Replay the iter-5 construction: `k := Nat.findGreatest (P) n²` where
     `P k := p_k ≤ n²`. Get `p_k ≤ n² - 1` (compositeness of `n²` for
     `n ≥ 2`) and `n² < p_{k+1}` (maximality of `k`).
   - **New step**: apply Mathlib's `Nat.bertrand` at `n²/2` (valid since
     `n² ≥ 2·M ≥ 2`) to get a prime `q` with `n²/2 < q ≤ n²`. By
     maximality of `k`, `p_k ≥ q > n²/2 ≥ M`. Hence
     `M ≤ p_k`, so `h_gap_above k _` gives the gap bound at `k`.
   - Conclude as in iter-5: `p_{k+1} ≤ (n² − 1) + 2(n − 1) + 1 = n² + 2n − 2 < (n+1)²`.

### 5.3. Why this signature

- **Threshold expressed in `p_k`, not `k`**: the user (Cramér caller)
  knows `p₀(C)`, not `k₀(C)`. Mapping `p₀(C) → k₀(C)` requires
  `Nat.primeCounting`, which is heavier to reason about than direct
  thresholds on `p_k`. The condition `M ≤ p_k` is much cleaner than
  `k₀ ≤ k`.
- **Finite tail expressed in `n²`, not `k`**: the user (legendre-partial
  caller) discharges `LegendreAt n` by `n`-indexed `native_decide`, not
  by `k`-indexed gap inspection. The factor of 2 in `n² < 2·M` comes from
  the Bertrand step in the proof outline (§5.2).
- **`M` is `ℕ`, not `ℝ`**: keeps the entire statement in `ℕ` and avoids
  threading `Real.log` through `LegendreConjecture`'s interface.
- **iter-5 is a corollary at `M = 0`** — the existing theorem can be
  re-derived in two lines as
  `prime_gap_sqrt_bound_implies_legendre h := prime_gap_sqrt_bound_above_implies_legendre 0 (fun k _ => h k) (fun n _ habs => absurd habs (by omega))`.

### 5.4. Lean cost estimate

| Item                                                          | Est. LOC |
|---------------------------------------------------------------|---------:|
| `prime_gap_sqrt_bound_above_implies_legendre` (proof body)    |       50 |
| Bertrand integration (`Nat.bertrand` lookup + arithmetic)     |       15 |
| Corollary `prime_gap_sqrt_bound_implies_legendre` (at M = 0)  |        5 |
| Module docstring update                                       |       15 |
| **Total** (inside `LegendrePrimeGapSqrtBoundSuffices.lean`)   |     ~85  |

0 new axioms expected. Mathlib's `Nat.bertrand` provides the only new import.

## 6. Implications for the S5 ACT (Cramér ⇒ Legendre)

The S5 ACT decomposes more cleanly with §5's refined variant:

```
S5-ACT-A: Real-analytic estimate
  -- For C : ℝ with 1 ≤ C ≤ 2·e^{-γ},
  --   ∃ p₀ : ℕ, ∀ p ≥ p₀, C · (log p)² ≤ 2 · √p + 1.
  -- (Requires Real.log monotonicity, Real.sqrt monotonicity, and a
  -- concrete witness — e.g. p₀ = 358 for C = 2·e^{-γ}.)

S5-ACT-B: Cramér ⇒ gap-above-threshold
  -- Cramér: ∃ C, k₀, ∀ k ≥ k₀, p_{k+1} - p_k ≤ C · (log p_k)².
  -- Combine with S5-ACT-A: let M := p₀(C). Then for any k with p_k ≥ M:
  --   p_{k+1} - p_k ≤ C · (log p_k)² ≤ 2 · √p_k + 1.
  -- (Discharges `h_gap_above` of the refined iter-5.)

S5-ACT-C: Compose
  -- Apply `prime_gap_sqrt_bound_above_implies_legendre M`:
  --   h_gap_above: from S5-ACT-B
  --   h_legendre_below: from legendre-partial's legendre_1, …, legendre_20
  --   (covers all n with n² < 2·M ≤ 2 · p₀(C); for C ≤ Granville,
  --    p₀ ≤ 358, so 2 · M ≤ 716, hence n ≤ ⌊√715⌋ = 26 — still well
  --    within legendre-partial's n ≤ 20 if we tighten or extend to n ≤ 26).
```

**Open scope decision** for S5 ACT (left to next picker):

- (a) Pick `C = 2 · e^{-γ}` (Granville-optimal) → M = 358 → need finite
  tail to `n ≤ 26`. Requires extending `legendre-partial` by 6 cases
  (`legendre_21`–`legendre_26`) — 6 native_decide rows, trivial.
- (b) Pick `C` arbitrarily large but explicit, paying a larger M → bigger
  finite tail. Less elegant, more LOC.
- (c) Pick `C = 1` (Cramér-original) → M = 121 → need finite tail to
  `n ≤ ⌊√241⌋ = 15`. Already covered by legendre-partial.

Recommendation: (c) — tightest constant, smallest finite tail, zero
gallery side-effects. The refined-iter-5 type signature is unchanged
across choices.

## 7. State after this iteration

| ID        | Description                                          | Status                                                                         |
|-----------|------------------------------------------------------|--------------------------------------------------------------------------------|
| S4-ACT-α  | `prime_gap_sqrt_bound_implies_legendre` (one-way)    | ✅ DONE (iter 5)                                                               |
| S5-PREP-2 | Cramér⇒Legendre bridging audit + refined-iter-5 spec | ✅ DONE (**this iteration**)                                                   |
| S5-ACT-A  | Real-analytic estimate C·log²p ≤ 2√p+1               | ⏳ Newly specified                                                              |
| S5-ACT-B  | Cramér ⇒ gap-above-threshold (uses iter-6 refined)  | ⏳ Newly specified                                                              |
| S5-ACT-C  | Compose (Cramér ⇒ Legendre)                         | ⏳ Newly specified                                                              |
| S6        | Computational extension to `n = 21, …, 50`           | ⏳ Low-leverage; partial subsumption by S5-ACT-C (a) needing `legendre_21..26`. |

## 8. Next picker's slot (recommended)

**S5-ACT-B′ — implement the refined iter-5 variant inside
`LegendrePrimeGapSqrtBoundSuffices.lean`.** Specifically, add the
~85 LOC specified in §5.4 (refined theorem + Bertrand step + corollary
to recover iter-5 at `M = 0`). This unblocks every downstream Cramér ⇒
Legendre composition without committing to a specific Cramér constant or
to the Real-analytic estimate yet. After it lands, S5-ACT-A and S5-ACT-C
can be done in either order.

## 9. Honest mathematical posture

This iteration produces:

1. **A correctness audit** of the previous picker's "cleanly factors"
   claim. The route works mathematically, but the iter-5 *theorem* needs
   reformulation to be a usable composition target.
2. **A concrete numerical envelope** for the Cramér threshold (k₀ ≤ 70,
   p₀ ≤ 358 under the Granville-strong constant).
3. **A precise type signature** for the refined iter-5 variant, with
   proof outline, LOC estimate, and a path back to iter-5 as a corollary.

No Lean is shipped this iteration. The deliverable is the same shape as
iter-4 PREP-1: a knowledge-only PREP that prevents the next ACT from
re-discovering a known structural pitfall in production.

## 10. Deliverables summary

1. **NEW session memo**: this file
   (`sessions/2026-06-10-iter6-s5-prep-cramer-bridge-gap.md`).
2. **`research/problems/bertrands-postulate-oq-02/state.md`**: Session 6
   prepend documenting the Cramér-bridge gap audit and the refined-iter-5
   recommendation.
3. **`research/problems/bertrands-postulate-oq-02/meta.json`**:
   `currentState.iteration` 5 → 6; `currentState.phase` ACT → PREP;
   `currentState.since`/`focus`/`nextAction` updated; `attemptCounts.total`
   5 → 6; `attemptCounts.currentApproach` 3 → 4; `knowledge.insights` +=
   four new entries (quantifier mismatch; numerical threshold; refined
   variant specification; legendre-partial sufficiency).
4. **`research/problems/bertrands-postulate-oq-02/knowledge.md`**:
   append Iteration 6 Log with the audit summary.
5. **`src/data/research/problems/bertrands-postulate-oq-02.json`**: mirror
   the meta.json changes; `lastUpdate` 2026-06-06 → 2026-06-10.

## 11. Out of scope (deferred)

- **The refined-iter-5 Lean implementation itself** — that is S5-ACT-B′,
  next picker's slot (§8).
- **The Cramér statement in Lean** — depends on a constant choice and is
  S5-ACT-B proper.
- **The real-analytic step `C·log²p ≤ 2·√p + 1`** — `Real.log` /
  `Real.sqrt` infrastructure work, S5-ACT-A.
- **legendre-partial extension to `n = 21..26`** — only required if S5-ACT-C
  is later instantiated with the Granville-optimal constant; deferred to
  the chooser of (a) vs (c) in §6.

## 12. Honest size

~330 lines of markdown + ~25 lines of JSON diff. No Lean. The mathematical
content is the structural audit identifying the quantifier mismatch and
proposing the refined-iter-5 type signature — this is the same kind of
pre-flight verification iter-4 PREP-1 delivered, and is intended to spare
the next ACT picker the same ~100 LOC of structural-redesign cleanup
when they discover at compile time that `PrimeGapSqrtBound` is too strong
to be discharged from Cramér's hypothesis.
