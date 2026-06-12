# Iter 7 — S5-ACT-B′: refined threshold-gated sqrt-gap ⇒ Legendre

**Agent**: researcher-2
**Date**: 2026-06-12
**Phase**: ACT
**File**: `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`
**Build**: Docker-verified (`Proofs.LegendrePrimeGapSqrtBoundSuffices`, 3074 jobs, ✔)

## What was done

Implemented the refined iter-5 variant specified by the iter-6 PREP-2 audit
(`2026-06-10-iter6-s5-prep-cramer-bridge-gap.md`):

```lean
theorem prime_gap_sqrt_bound_above_implies_legendre (M : ℕ)
    (h_gap_above : ∀ k, M ≤ Nat.nth Nat.Prime k →
      Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
        ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1)
    (h_legendre_below : ∀ n, 1 ≤ n → n^2 < 2 * M → LegendreAt n) :
    LegendreConjecture
```

The original unrestricted theorem is now derived as the **`M = 0`
specialization**:

```lean
theorem prime_gap_sqrt_bound_implies_legendre (h : PrimeGapSqrtBound) :
    LegendreConjecture :=
  prime_gap_sqrt_bound_above_implies_legendre 0
    (fun k _ => h k)
    (fun _ _ hlt => absurd hlt (by omega))
```

The three downstream corollaries (`..._gap_form`, `..._distance_form`,
`..._halfOpen_form`) are unchanged and still build.

## Proof structure

`intro n hn`, then a two-way split on `n² < 2*M`:

- **Below threshold** (`n² < 2*M`): discharged directly by `h_legendre_below`.
- **Above threshold** (`n² ≥ 2*M`): subdivide on `n < 2`.
  - `n = 1`: prime `2 ∈ (1,4)` as before.
  - `n ≥ 2`: identical `Nat.findGreatest` construction as iter-5, with one
    **new threshold bridge** before applying the gap hypothesis:

### Threshold bridge (the only new mathematical content)

To license `h_gap_above k`, we must show `M ≤ p_k` where `p_k` is the largest
prime `≤ n²`. Bertrand's postulate (`Nat.bertrand (n²/2)`, valid since
`n ≥ 2 ⇒ n²/2 ≥ 2 ≠ 0`) yields a prime `q` with

```
M ≤ n²/2 < q ≤ 2·(n²/2) ≤ n².
```

(`M ≤ n²/2` from `2*M ≤ n²` via floor division; both inequalities closed by
`omega` treating `n²` as an atom — omega natively models `·/2`.) Writing
`q = p_j` for `j := Nat.count Nat.Prime q` (`Nat.nth_count`), `j ≤ n²` from
`nth_prime_ge`, so `Nat.le_findGreatest` gives `j ≤ k`, and monotonicity of
`Nat.nth Nat.Prime` gives `q ≤ p_k`. Hence `M ≤ q ≤ p_k`. The rest of the
chain (`p_{k+1} ≤ p_k + 2√p_k + 1 < (n+1)²`) is unchanged from iter-5.

## Axiom / sorry delta

- **0 new axioms**, **0 sorries**. Ambient `Legendre.legendre_conjecture`
  (declared in `LegendrePartial.lean`) is untouched.
- Net LOC ≈ +70 (general theorem body + bridge; original 65-line proof
  replaced by a 4-line corollary).

## Why this matters / what it unblocks

The unrestricted `PrimeGapSqrtBound` (`∀ k`) provably **cannot** accept
Cramér's eventually-quantified output (`∀ k ≥ k₀`) — the sqrt bound fails for
small `k` (iter-6 PREP-2: smallest `p` with `C·log²p ≤ 2√p+1` is `p₀=121` for
`C=1`, `p₀=358` for `C=2e^{-γ}`). The threshold form takes the gap bound only
for `p_k ≥ M` and absorbs the small-`k` regime into the finite
`h_legendre_below` obligation, which `legendre-partial`'s `n=1..20` cases
cover with margin. This is the missing structural lemma for the Cramér ⇒
Legendre composition.

## Next steps (unchanged from iter-6, now unblocked)

- **S5-ACT-A** — real-analytic `∃ p₀, ∀ p ≥ p₀, C·log²p ≤ 2√p+1`
  (`Real.log`/`Real.sqrt`; witness `p₀ = 121` for `C=1`).
- **S5-ACT-C** — compose `prime_gap_sqrt_bound_above_implies_legendre` (this
  deliverable) + S5-ACT-A + `legendre-partial` to obtain Cramér ⇒ Legendre.
  With `C = 1` no gallery extension is needed; `C = 2e^{-γ}` would need
  `legendre_21..26` (6 trivial `native_decide` rows).
