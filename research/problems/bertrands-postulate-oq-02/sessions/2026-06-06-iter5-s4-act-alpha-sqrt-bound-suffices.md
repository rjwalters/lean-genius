# Session 5 — Iter 5 S4-ACT-α — Sqrt prime-gap bound suffices for Legendre (one-way, axiom-free)

**Date**: 2026-06-06 (researcher-1, T+1d post-iter-4 PREP-1 audit)
**Branch**: `research/bertrands-postulate-oq-02-iter5-sqrt-bound-suffices`
**Type**: ACT (Lean implementation)
**Result**: Formalized the salvageable (reverse) direction of the iter-3
proposed iff. 0 new axioms, 0 sorries, Docker build verified.

## 1. Goal

Implement the **corrected S4-ACT-α** identified by the iter-4 PREP-1 audit:

```lean
theorem prime_gap_sqrt_bound_implies_legendre :
    (∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
          ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1) →
    LegendreConjecture
```

The PREP-1 audit established that the iff `LegendreConjecture ↔ ∀ k, p_{k+1} -
p_k ≤ 2·Nat.sqrt p_k + 1` is **not** a true equivalence — the forward
direction `Legendre ⟹ gap bound` is provable only up to `4·Nat.sqrt p_k + 2`
in the worst case. The salvageable reverse direction is the actual
mathematical content; this session formalizes it.

## 2. Deliverable

**New file**: `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean` (227 LOC).

**Public surface**:

| Name | Type | Notes |
|------|------|-------|
| `PrimeGapSqrtBound` | `Prop` | Definition: `∀ k, p_{k+1} - p_k ≤ 2·√p_k + 1` |
| `not_prime_sq_of_ge_two` | `2 ≤ n → ¬ Nat.Prime (n^2)` | Aux: `n²` composite for `n ≥ 2` |
| `nth_prime_ge` | `k + 2 ≤ Nat.nth Nat.Prime k` | Aux: nth prime is at least `k + 2` |
| **`prime_gap_sqrt_bound_implies_legendre`** | `PrimeGapSqrtBound → LegendreConjecture` | **Main theorem** |
| `prime_gap_sqrt_bound_implies_gap_form` | `PrimeGapSqrtBound → LegendreGapForm` | Corollary via iter-2 |
| `prime_gap_sqrt_bound_implies_distance_form` | `PrimeGapSqrtBound → LegendreDistanceForm` | Corollary via iter-2 |
| `prime_gap_sqrt_bound_implies_halfOpen_form` | `PrimeGapSqrtBound → LegendreHalfOpenForm` | Corollary via iter-2 |

**Imports** (Mathlib + project):
- `Mathlib.Data.Nat.Prime.Nth` — for `Nat.nth Nat.Prime`
- `Mathlib.NumberTheory.PrimeCounting` — for `Nat.primeCounting`
- `Mathlib.Tactic` — `omega`, `nlinarith`, `positivity`
- `Proofs.LegendrePartial` — `LegendreConjecture`, `LegendreAt`
- `Proofs.LegendreGapEquivalence` — `LegendreGapForm` etc.
- `Proofs.PrimeGapBounds` — `first_prime`, `nth_prime_is_prime`

## 3. Proof strategy (formalized)

For each `n ≥ 1`, exhibit a prime in `(n², (n+1)²)`:

* **Case `n = 1`**: prime `2` witnesses `LegendreAt 1` directly (one-line
  refine with `Nat.prime_two` plus `norm_num`).

* **Case `n ≥ 2`**: take `k := Nat.findGreatest (fun k => p_k ≤ n²) n²`,
  the index of the largest prime `≤ n²`.

  Key Lean techniques:

  - `Nat.findGreatest_spec` (with witness `k = 0`, since `p_0 = 2 ≤ n²`)
    establishes `P k`, i.e. `p_k ≤ n²`.
  - `Nat.findGreatest_le` establishes `k ≤ n²`.
  - `nth_prime_ge` (k ≤ p_k - 2) plus `p_k < n²` gives `k + 1 ≤ n²`,
    needed to apply the "is_greatest" axis.
  - `Nat.findGreatest_is_greatest` (with `k+1 > k` and `k+1 ≤ n²`)
    establishes `¬ P (k+1)`, i.e. `p_{k+1} > n²`.
  - `not_prime_sq_of_ge_two` shows `n²` is composite for `n ≥ 2`, hence
    `p_k ≤ n² ⟹ p_k ≠ n² ⟹ p_k < n²`.
  - Gap-bound hypothesis at `k`: `p_{k+1} - p_k ≤ 2·√p_k + 1`.
  - Strict monotonicity (`Nat.nth_strictMono Nat.infinite_setOf_prime`)
    converts the ℕ-subtraction into addition.
  - Sqrt monotonicity (`Nat.sqrt_le_sqrt`) and `Nat.sqrt_lt'` give
    `√p_k ≤ √(n²-1) ≤ n-1`.
  - omega closes the final linear assembly `p_{k+1} ≤ (n²-1) + 2(n-1) + 1
    = n² + 2n - 2 < n² + 2n + 1 = (n+1)²`.

* **Corollaries**: lift through `legendre_iff_gap_form` etc. from
  iter-2's `LegendreGapEquivalence.lean` to get equivalent statements in
  gap/distance/half-open forms.

## 4. Honest mathematical posture

This iteration produces a **conditional implication**, not progress on the
open conjecture itself. The hypothesis `PrimeGapSqrtBound` is essentially
equivalent in strength to Legendre (and is open: it would imply Legendre by
exactly this theorem). The value lies in:

1. **Closing the salvageable half** of the broken iff identified in PREP-1.
   Future readers see in Lean source which direction is provable and which
   is not.
2. **Three free corollaries** via iter-2's equivalences — the same gap-bound
   hypothesis suffices for each reformulation.
3. **A clean prime-gap-suffices statement** in Lean. Useful as a hypothesis
   "drop-in" for future work on Cramér-style or BHP-style refinements.

The iter-4 PREP-1 memo (`2026-06-05-iter4-prep-1-gap-bound-asymmetry.md`)
remains the canonical document for why the **other** direction can't be
proved — it is referenced from the docstring of the new file.

## 5. Axiom delta

| Before iteration 5 | After iteration 5 |
|--------------------|-------------------|
| 1 axiom (`legendre_conjecture` in `LegendrePartial.lean`) | 1 axiom (unchanged) |

The new file adds **0 new axioms** and **0 new sorries**. Docker build:

```
✔ [3074/3074] Built Proofs.LegendrePrimeGapSqrtBoundSuffices (6.8s)
Build completed successfully (3074 jobs).
```

## 6. State after this iteration

| ID | Description | Status after iter 5 |
|---|---|---|
| S4-ACT-α | `prime_gap_sqrt_bound_implies_legendre` (one-way) | ✅ **DONE** (this iteration) |
| S4-iff (original) | `legendre_iff_primeGap` (proposed iff) | 🚫 ANTI-CANDIDATE (PREP-1 verdict, unchanged) |
| S5 | Cramér ⇒ Legendre (sub-Milestone A) | ⏳ Now newly tractable: combine with this iteration's `prime_gap_sqrt_bound_implies_legendre` via a Cramér ⇒ sqrt-bound bridge. |
| S6 | Computational extension to `n = 21, …, 50` (sub-Milestone C) | ⏳ low-leverage padding; remains valid filler |

## 7. Next picker's slot (recommended)

**S5 ACT — Cramér ⇒ Legendre.** Now that `prime_gap_sqrt_bound_implies_legendre`
is in place, the route to Cramér⇒Legendre cleanly factors:

```
Cramér's conjecture
  ⟹ (for sufficiently large k) p_{k+1} - p_k ≤ C·(log p_k)² ≤ 2·√p_k + 1
  ⟹ LegendreConjecture (via prime_gap_sqrt_bound_implies_legendre, modulo
                          the finite tail for small k handled by legendre-partial)
```

Hard parts:
- Stating Cramér's conjecture (no Mathlib statement; would be a new `def Prop`).
- The arithmetic `C·(log p_k)² ≤ 2·√p_k + 1` for sufficiently large k (true
  since √ grows faster than log²; may need Mathlib's `Real.log` and
  asymptotic estimates).
- Bridging the finite-tail base cases.

Estimated size: +200-250 LOC. 0 new axioms expected (only Cramér as a
hypothesis, not an axiom).

## 8. Deliverables summary (this PR)

1. **NEW Lean file**: `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`
   (227 LOC, 0 axioms, 0 sorries, build verified).
2. **`proofs/Proofs.lean`** import line added for the new file.
3. **NEW session memo**: this file
   (`sessions/2026-06-06-iter5-s4-act-alpha-sqrt-bound-suffices.md`).
4. **`research/problems/bertrands-postulate-oq-02/state.md`**: Session 5
   prepend documenting S4-ACT-α completion and S5 recommendation.
5. **`research/problems/bertrands-postulate-oq-02/meta.json`**:
   `currentState.iteration` 4 → 5; `currentState.since`/`focus`/`nextAction`
   updated; `attemptCounts.total` 4 → 5; `attemptCounts.currentApproach`
   2 → 3; `knowledge.builtItems` += new file entry; `knowledge.insights`
   += "sqrt-gap-bound suffices for Legendre (this iteration)".
6. **`research/problems/bertrands-postulate-oq-02/knowledge.md`**:
   appended Iteration 5 Log with the result summary.
7. **`src/data/research/problems/bertrands-postulate-oq-02.json`**: mirror
   the meta.json changes; `lastUpdate` 2026-06-05 → 2026-06-06.

## 9. Out of scope (deferred)

- Gallery `meta.json` numerics — this is research output, not a gallery
  proof; no `src/data/proofs/` entry.
- `pnpm build` — no gallery deltas.
- Cramér ⇒ Legendre formalization (S5 ACT-β; future iteration).

## 10. Honest size

~230 LOC Lean + ~250 LOC markdown + ~15 lines JSON diff. The mathematical
content is the one-way implication; corollaries are mechanical via iter-2
equivalences. PREP-1 memo (iter-4) did the conceptual heavy lifting; this
iteration is the implementation.
