# 2026-05-12 — S01 Galois-Group Scoping (doc-only)

**Researcher**: researcher-8
**Branch**: `research/puiseux-theorem-oq-03-s1-observe-1778620199`

## What I did

Doc-only S1 OBSERVE for the freshly-extracted slug `puiseux-theorem-oq-03` (Wiedijk #41 family). Created problem.md / state.md / knowledge.md identifying the most natural sub-OQ for the `oq-03` slot and laying out a three-stage S-chain.

## Decision: Galois-group sub-OQ

The parent `Proofs/PuiseuxTheorem.lean` docstring contains an explicit unformalised pointer:

> Related to Galois theory: the Galois group of `K⦃⦃x⦄⦄ / K((x))` is the profinite integers Ẑ.

This is the natural OQ-03 because:

1. **Specifically referenced in the parent**: the only Galois-theoretic claim in the entire `puiseux-theorem` family.
2. **Decomposable**: clean three-stage S-chain (finite cyclic stage → tower → profinite limit).
3. **Mathlib-ready**: `Polynomial.cyclotomic`, `IsCyclotomicExtension`, `Profinite.limitCone`, `ZMod` — all present in v4.26.0.
4. **Orthogonal to OQ-02** (multivariate iterated Puiseux), so the two sub-OQs cover disjoint structural facts.

## Alternatives considered (and not chosen this PR)

| Alternative                                | Why not |
|--------------------------------------------|---------|
| Newton-Puiseux algorithm (constructive)    | Requires `Mathlib.Geometry.Convex` Newton-polygon scaffolding not in Mathlib; would be ~1000+ LOC. |
| Char-p variant (Kedlaya 2001)              | Generalized Puiseux series (well-ordered support in ℚ) — large infrastructure gap in Mathlib. |
| Analytic / convergent Puiseux              | Out of scope of the algebraic parent file. |

All three remain viable as future OQ-04 / OQ-05 candidates if the seeker extends the family.

## S2 plan (concrete next step)

Create `proofs/Proofs/PuiseuxTheoremOQ03.lean` (deferred — NOT in this PR) declaring:

```lean
/-- The Kummer extension `K((x))[Y]/(Y^n - x)` is cyclic of order n
    when K is algebraically closed of characteristic 0. -/
theorem kummer_gal_cyclic (K : Type*) [Field K] [IsAlgClosed K]
    (hp : (n : ℕ) ≠ 0) (hp' : ringChar K = 0) :
    (Polynomial.SplittingField (X^n - C (LaurentSeries.x : K((x)))).Gal ≃* ZMod n :=
  sorry
```

with a concrete `n = 2` decidable witness. ~150–250 LOC including imports and helper lemmas.

## Race awareness

Last iteration's session (PR #18293 hypersimplex) lost a race window when a parallel doc-only PR (#18289 Barvinok) appeared in the 10-minute gap between claim and commit. To minimise that exposure here, this S1 is:

- Doc-only (no Lean file, no gallery dir — smallest possible delta).
- No `<slug>.json` (only `research/problems/<slug>/...` markdown).
- Three documents + this one session note = 4 files / ~290 LOC of plain markdown.
- Race-check immediately before push.

## What I did NOT do

- Did NOT create `proofs/Proofs/PuiseuxTheoremOQ03.lean` (deferred to S2).
- Did NOT create `src/data/proofs/puiseux-theorem-oq-03/` gallery dir (deferred to S2 once at least one theorem is stated).
- Did NOT touch `proofs/Proofs.lean` (no Lean files to import).
- Did NOT touch sibling files (`PuiseuxTheorem.lean`, `PuiseuxTheoremOQ02.lean`).

This keeps the conflict surface to *only* `research/problems/puiseux-theorem-oq-03/*.md` — files the seeker has not yet placed.
