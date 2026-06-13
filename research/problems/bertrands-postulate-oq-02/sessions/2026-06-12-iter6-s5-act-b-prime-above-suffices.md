# iter6 S5-ACT-B′ — `prime_gap_sqrt_bound_above_implies_legendre` landed

**Slug:** `bertrands-postulate-oq-02` (Legendre's conjecture for square intervals)
**Researcher:** researcher-2
**Date:** 2026-06-12
**Phase:** ACT (Lean diff, Docker-verified)
**Predecessor:** iter5 S4 ACT (alpha sqrt-bound-suffices, the global-hypothesis
`prime_gap_sqrt_bound_implies_legendre`); iter6 S5 PREP (Cramér bridge gap).
**File:** `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`

## Result

Implements the iter-5 PREP refinement (the `S5-ACT-B′` next-action): a strictly
stronger **eventually-suffices** conditional reduction for Legendre's
conjecture, and re-derives the previous theorem as its `M = 0` corollary.

```lean
theorem prime_gap_sqrt_bound_above_implies_legendre (M : ℕ)
    (h_gap_above : ∀ k, M ≤ nth Prime k → p_{k+1} - p_k ≤ 2·√p_k + 1)
    (h_legendre_below : ∀ n, 1 ≤ n → n² < 2·M → LegendreAt n) :
    LegendreConjecture
```

Docker: `./proofs/scripts/docker-build.sh Proofs.LegendrePrimeGapSqrtBoundSuffices`
→ **Build succeeded (3074 jobs)**, first try. 0 sorries, 0 new axioms.

## Why it is stronger

The previous `prime_gap_sqrt_bound_implies_legendre` required the sqrt gap
bound for **every** `k`. The new form only needs it for primes `p_k ≥ M`
(an *eventual* / asymptotic hypothesis — the realistic shape of any
analytic gap input, e.g. a Cramér-type bound that holds past some
threshold), with the finitely-many small `n` (those with `n² < 2M`)
discharged separately by `h_legendre_below` (e.g. `native_decide`, as the
`legendre_k` facts in `LegendrePartial.lean` already do).

## Proof structure

`intro n hn`, then:

1. `n = 1`: prime `2 ∈ (1,4)` directly (unchanged).
2. `n ≥ 2`, `n² < 2M`: `exact h_legendre_below n hn _`.
3. `n ≥ 2`, `n² ≥ 2M`: the iter-5 `Nat.findGreatest` construction for the
   largest prime `p_k ≤ n²`, **plus** the new step establishing `M ≤ p_k`:
   - `Nat.bertrand (n²/2)` gives a prime `q` with `n²/2 < q ≤ 2·(n²/2) ≤ n²`;
   - `q`'s prime index `j = Nat.count Nat.Prime q` satisfies `P j` and
     `j ≤ n²`, so `Nat.le_findGreatest` gives `j ≤ k`, hence (by
     `Nat.nth_monotone`) `q ≤ p_k`;
   - `n² ≥ 2M ⇒ n²/2 ≥ M`, so `M ≤ q ≤ p_k`.

   With `M ≤ p_k`, apply `h_gap_above k`; the rest (sqrt bound `≤ n−1`,
   `p_{k+1} < (n+1)²`) is verbatim the iter-5 argument.

`prime_gap_sqrt_bound_implies_legendre` is now the one-liner
`prime_gap_sqrt_bound_above_implies_legendre 0 (fun k _ => h k) (fun _ _ hlt => absurd hlt (by omega))`,
so the three downstream equivalence corollaries (gap / distance / half-open
forms) are unchanged and still build.

## Axiom status

0 new axioms. The ambient `Legendre.legendre_conjecture` axiom in
`LegendrePartial.lean` is untouched; this file remains a pure conditional
reduction (`hypothesis → LegendreConjecture`).

## Next

S5-ACT-A (the genuinely hard analytic half): supply an actual `M` and a proof
of `h_gap_above` from a real prime-gap theorem (Cramér / known unconditional
bounds give `gap = O(√p · log p)`, which does **not** beat `2√p+1` — so this
reduction is currently a conditional statement, not a path to an unconditional
Legendre proof; that obstacle is unchanged and inherent to the OQ).
