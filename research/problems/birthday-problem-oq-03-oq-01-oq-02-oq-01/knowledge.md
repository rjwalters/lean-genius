# Knowledge Base: birthday-problem-oq-03-oq-01-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Remove `axiom poisson_approx_birthday3` from `BirthdayProblemOQ03OQ01OQ02.lean`
by proving the Chen-Stein Poisson approximation bound:

```
|triple_prob n d - (1 - exp(-C(n,3)/d²))| ≤ C · n⁴/d³
```

The axiom captures a Poisson limit theorem for birthday triple coincidences. The standard
proof uses the Chen-Stein method (Arratia-Goldstein-Gordon 1989) for indicator sums of
positively associated random variables.

**Critical block**: Chen-Stein is entirely absent from Mathlib 4.

---

## Session 2026-04-21 (Session 1) - Infrastructure Gap Assessment

**Mode**: FRESH (EMPTY knowledge tier, score 2)
**Outcome**: BLOCKED — Chen-Stein method absent from Mathlib 4; n=3 base case proved

### What I Did

1. Read `BirthdayProblemOQ03OQ01OQ02.lean` (419 lines) — confirmed axiom location and signature
2. Searched Mathlib for PoissonDistribution, totalVariation, BernoulliDistribution, chenStein
3. Found Mathlib has `poissonPMFReal`, `poissonMeasure` — but NO approximation theorems
4. Assessed elementary alternatives: union bound, second moment method, direct computation
5. Proved `bad_count_n3` and `good_count_n3` as concrete provable n=3 lemmas
6. Added §7 Elementary Counting Bound to `BirthdayProblemOQ03OQ01OQ02.lean`

### Key Findings

**Primary blocker**: Chen-Stein method not in Mathlib 4. Would require:
- Stein's operator for Poisson distribution
- Local dependency graph construction
- Total variation distance formulation compatible with `poissonMeasure`
- Estimated: 500-800 lines of probability infrastructure

**Elementary alternatives fall short**:
- Union bound: gives P(triple) ≤ C(n,3)/d² (correct order) but not the tight limit theorem
- Second moment method: proves P(triple) ≥ (1-ε)C(n,3)/d² asymptotically, no explicit bound
- Direct computation: proves exact formula for specific n, not the general bound

**What was proved (n=3 base case)**:

```lean
-- bad_count_n3: |{f: Fin 3 → Fin d | f 0 = f 1 ∧ f 1 = f 2}| = d
-- (bijection: bad function ↔ its common value)

-- good_count_n3: |{f: Fin 3 → Fin d | ¬(f 0=f 1 ∧ f 1=f 2)}| = d³ - d
-- (complement via filter_card_add_filter_neg_card_eq_card)
```

These confirm P(no triple | n=3) = (d³-d)/d³ = 1 - 1/d², matching exp(-1/d²) ≈ 1 - 1/d² for large d.

**Mathlib probability infrastructure found**:
- `Mathlib.Probability.Distributions.Poisson`: `poissonPMFReal`, `poissonMeasure`
- `Mathlib.MeasureTheory.Measure.MeasureSpace`: total variation distance (`MeasureTheory.totalVariation`)
- Missing: approximation theorems, Chen-Stein, Stein's method

### Files Modified

- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (+45 lines: §7 with 2 proved lemmas)

### Next Steps

1. **If Chen-Stein becomes available in Mathlib**: Immediately applicable — axiom signature matches
2. **Alternative**: Build Chen-Stein locally (500-800 lines) — high value but large scope
3. **Partial progress**: Prove elementary bounds that constrain the approximation error
4. **Consider**: Submitting a Mathlib PR for Chen-Stein lemma (long-term, high impact)

---

## Dead Ends

- **Chen-Stein from scratch this session**: Too large (~500-800 lines of measure theory infrastructure)
- **Second moment → exact bound**: Second moment proves asymptotics, not explicit error bounds
- **Union bound as proof of main axiom**: Only proves one direction, not the bilateral approximation bound
