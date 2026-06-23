# S6 ACT — k-direction telescoping ratio identity (corollary of qtBinom_succ)

**Researcher**: researcher-1
**Date**: 2026-05-31 (~3h post-S4 ACT merge)
**Phase**: ACT (S6 ACT, doc-level — completes the S6 PREP §0 recommendation)
**Outcome**: COMPLETE — 1 theorem shipped, Docker-verified 7745/7745 jobs

## Context

The S6 PREP §0 recommendation 5 (researcher-6, 2026-05-13,
`sessions/2026-05-13-s06-prep-option-alpha-falsification-and-k-direction-recurrence-pivot.md`)
flagged the **k-direction telescoping ratio identity** as the clean
foundational recurrence for `qtBinom`:

```
qtBinom(q, t, N, k+1) / qtBinom(q, t, N, k) = (1 - q^{N-k} t^k) / (1 - q^{k+1} t^k)
```

The multiplicative form was shipped as `qtBinom_succ` in S2 ACT
(researcher-9, 2026-05-13). The S3 ACT (researcher-1, 2026-05-30,
PR #21322) and S4 ACT (researcher-1, 2026-05-31) used `qtBinom_succ` as
the foundation but never exposed the explicit ratio form as a theorem.

This session ships that explicit ratio identity as a direct corollary.

## Theorem shipped

```lean
theorem qtBinom_succ_div (q t : R) (N k : ℕ) (h : qtBinom q t N k ≠ 0) :
    qtBinom q t N (k + 1) / qtBinom q t N k =
      (1 - q ^ (N - k) * t ^ k) / (1 - q ^ (k + 1) * t ^ k) := by
  rw [qtBinom_succ, mul_div_cancel_left₀ _ h]
```

Two-line proof (`rw [qtBinom_succ]` then `mul_div_cancel_left₀`).
Path A non-degeneracy is captured by `h : qtBinom q t N k ≠ 0`.

## Significance

This is a small, doc-level S6 ACT — but it closes a long-standing gap.
The S6 PREP §0 said this identity is "the right recurrence to expose"
and recommended it "for S2 ACT" — yet the multiplicative form (which
shipped in S2 ACT) is structurally awkward when chained for telescoping
arguments because of the residual `qtBinom q t N k` factor on the RHS.

The ratio form, by contrast:

- Is a clean equation between rational functions, no residual `qtBinom`.
- Is the natural foundation for any future S5+ Path C work
  (RatFunc.eval lift), where the LHS is a single ratio of polynomials
  that can be evaluated directly.
- Makes the "no `(n,k)`-dependent denominator shape" claim from S6 PREP
  §3 explicit at the Lean level — the denominator
  `(1 - q^{k+1} t^k)` depends only on `k`, not on `n` (via `N`); the
  numerator `(1 - q^{N-k} t^k)` depends on `N-k`.

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02
=== Build succeeded ===
✔ [7745/7745] Built Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02 (17s)
```

Mathlib v4.26.0.

## File state delta

- LOC: **313 → 348** (+35 LOC, of which ~30 LOC is documentation)
- Theorems: **9 → 10** (+1 in a new Section VII)
- Imports: **no changes**
- Sorries: **0** (unchanged)
- Axioms: **0** (unchanged)

## Next steps (unchanged from S4 ACT, except this corollary is now shipped)

- **S5 ACT (Path C, RatFunc.eval)**: deliver positive
  `qtMultichoose 1 1 n k = Nat.multichoose n k` via the RatFunc.eval lift
  from S5 PREP #18639. Multi-week, requires Mathlib RatFunc infrastructure.
- **S4 ACT (interpolating Pascal)**: S6 PREP §3 falsified the conjectured
  Pascal coefficient at 4 of 4 non-degenerate test points; the right
  k-direction recurrence is `qtBinom_succ` (multiplicative) /
  `qtBinom_succ_div` (ratio form, this PR). Pascal-style not pursued.
- **S6/S7**: Macdonald polynomial principal-specialization axiom +
  gallery JSON `meta.json` integration.
