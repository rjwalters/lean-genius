# Knowledge Base: birthday-problem-oq-03-oq-01-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Remove `axiom poisson_approx_birthday3` from `BirthdayProblemOQ03OQ01OQ02.lean`.

### Actual Axiom (Lean source, lines 325–334)

```lean
axiom poisson_approx_birthday3 (c : ℝ) (hc : 0 < c) :
    let n : ℕ → ℕ := fun d => ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
    Filter.Tendsto
      (fun d : ℕ =>
        (Finset.univ.filter (fun f : Fin (n d) → Fin d =>
          ∀ i j k : Fin (n d), i ≠ j → j ≠ k → i ≠ k →
            ¬(f i = f j ∧ f j = f k))).card /
        (Fintype.card (Fin (n d) → Fin d) : ℝ) -
        Real.exp (-(n d).choose 3 / (d : ℝ) ^ 2))
      Filter.atTop (nhds 0)
```

This is a **qualitative** convergence statement — the difference between
P(no triple) and `exp(−C(n d, 3)/d²)` tends to 0 along `d → ∞`.

It is NOT the quantitative Chen-Stein bound `|...| ≤ C·n⁴/d³` shown in
the JSON `problemStatement.formal` — that field had drifted from the
actual Lean source and caused Session 1 to over-scope the work.

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

---

## Session 2026-04-27 (Session 2) - Reframing and Decomposition

**Mode**: REVISIT (WEAK knowledge tier, score 5)
**Outcome**: ORIENT — JSON drift corrected; axiom decomposed into sublemmas A/B/C

### Why Revisit

Per a saved feedback note from a prior session, the JSON `problemStatement.formal`
field stated a **stronger goal** than the actual Lean axiom. Session 1 (2026-04-21)
worked from the misleading JSON and concluded "BLOCKED on Chen-Stein, ~500-800 LoC".
This session re-reads the Lean source as authoritative and re-scopes accordingly.

### What I Did

1. Read `BirthdayProblemOQ03OQ01OQ02.lean:325-334` directly to extract the actual axiom
   signature; confirmed it is a qualitative `Filter.Tendsto ... atTop (nhds 0)` along
   the threshold scaling `n d = ⌊c · d^(2/3)⌋`, not a quantitative `|...| ≤ C·n⁴/d³`.
2. Updated `src/data/research/problems/<slug>.json`:
   - Corrected `problemStatement.formal` to the actual Tendsto statement.
   - Phase advanced NEW → ORIENT.
   - Title changed from "Chen-Stein method for Poisson approximation" to
     "Qualitative Poisson convergence for birthday triples" — matches what the
     axiom actually claims.
3. Decomposed the axiom into three sublemmas (below).

### Decomposition Strategy (the main contribution of this session)

Let `n_c(d) = ⌊c · d^(2/3)⌋` and `λ_c(d) = C(n_c(d), 3) / d²`. The axiom says
`P_no_triple(n_c(d), d) − exp(−λ_c(d)) → 0`. Decompose:

- **Lemma A (`lambda_tendsto`)**: `λ_c(d) → c³/6` as `d → ∞`.
  - Routine asymptotic analysis: `C(n,3) = n(n-1)(n-2)/6` and `n_c(d) ~ c·d^(2/3)`,
    so `λ_c(d) = n_c(d)·(n_c(d)−1)·(n_c(d)−2) / (6·d²) → c³ · d² / (6·d²) = c³/6`.
  - Mathlib tooling: `Filter.Tendsto.div`, `Filter.Tendsto.mul`, `Nat.floor`
    asymptotics already present (e.g., `Nat.floor_div_nat_eq_div`).
  - Estimated size: 30–50 lines.

- **Lemma B (`exp_lambda_tendsto`)**: `exp(−λ_c(d)) → exp(−c³/6)`.
  - One-line proof: `Real.continuous_exp.tendsto.comp (Lemma A composed with neg)`.
  - Estimated size: 5–10 lines.

- **Lemma C (`p_no_triple_tendsto`)**: `P_no_triple(n_c(d), d) → exp(−c³/6)`.
  - The genuine Poisson convergence — the only place Mathlib infrastructure is missing.
  - Two known qualitative paths:
    1. Method of factorial moments: `E[(X_d)_k] → (c³/6)^k` for each fixed `k`,
       where `(X)_k = X(X−1)…(X−k+1)`. The factorial moments uniquely characterize
       the Poisson distribution.
    2. Coupling: define independent Bernoulli(1/d²) indicators on the same triples,
       show their sum converges to Poisson(c³/6) by classical CLT-for-Bernoullis,
       and bound coupling discrepancy → 0.
  - Estimated size in Lean: ~200–400 lines (much smaller than Chen-Stein because
    we don't need explicit error bounds — just convergence).

The original axiom follows from A ∧ B ∧ C: if both `P_no_triple` and `exp(−λ)`
converge to the same limit `exp(−c³/6)`, their difference converges to 0.

### Why This Is Real Progress

- **Session 1 framed the gap as Chen-Stein** (~500–800 lines of total-variation
  machinery, including Stein's operator and dependency-graph constructions).
- **The actual axiom is strictly weaker** and admits a decomposition where two
  sublemmas (A, B) are routine and the third (C) is the classical Poisson
  convergence by method of moments — substantially smaller than full Chen-Stein.
- The Mathlib gap shrinks from "Chen-Stein quantitative bound" to
  "method-of-factorial-moments → Poisson, qualitative form".

### Files Modified

- `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json`
  (formal statement, phase, knowledge fields all updated to reflect actual axiom)
- `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/knowledge.md` (this file)

### Files NOT Modified

- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` — no Lean changes this session.
  Disk space at 89%/1.6 GB free flagged Docker builds as risky per saved guidance,
  so sublemmas A/B/C are deferred to a session with adequate disk.

### Honest Assessment

This session did **not** prove any Lean theorems. The contribution is a corrected
research framing that prevents future sessions from repeating Session 1's
over-scope error and a concrete decomposition that breaks the remaining Mathlib
gap into a smaller, more focused target. Subsequent sessions can implement A and
B mechanically (a few dozen lines each) and then attack only the genuine Poisson
convergence statement C.

### Next Steps

1. **Next ACT session (when disk allows Docker builds)**:
   - Add `lambda_tendsto` (Lemma A) — Filter.Tendsto.{mul,div} composition.
   - Add `exp_lambda_tendsto` (Lemma B) — one-liner via continuous_exp.
   - Restate the axiom as the simpler `p_no_triple_tendsto` (Lemma C only).
2. **Future session**:
   - Attack Lemma C via factorial-moment method — the primary new infrastructure
     is `Finset.sum`-based factorial-moment computations for indicator sums and
     a method-of-moments → Poisson lemma.
3. Cross-reference `birthday-problem-oq-03-oq-01-oq-01` (n=2 baseline) to see if
   any factorial-moment scaffolding there can be reused or generalized.
