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

## Session 2026-04-27 (Session 2) — Axiom Re-reading + Method-of-Moments Path

**Mode**: REVISIT (WEAK knowledge tier, score 5)
**Outcome**: STRATEGY REFINEMENT — actual axiom is qualitative, not quantitative; method of moments is a lighter alternative to Chen-Stein.

### What I Did

1. Re-read the actual Lean axiom (`BirthdayProblemOQ03OQ01OQ02.lean:325`) and compared to the JSON `problemStatement.formal`.
2. Mapped the axiom's parameter shape: `(c : ℝ) (hc : 0 < c)` with `n d := ⌊c · d^{2/3}⌋`, then `Filter.Tendsto (fun d => P_no_triple - exp(-C(n d, 3)/d²)) atTop (nhds 0)`.
3. Computed the limit values to confirm the regime: λ(d) = C(n d, 3)/d² → c³/6 as d → ∞ (uses `choose3_real` already proved in §1).
4. Re-classified the proof difficulty against this qualitative axiom shape.

### Key Finding: The Axiom is QUALITATIVE, Not Quantitative

The JSON `problemStatement.formal` field shows a **quantitative** Chen-Stein bound `|...| ≤ C·n⁴/d³`. The actual Lean axiom (`poisson_approx_birthday3`, line 325) is **qualitative**:

```lean
Filter.Tendsto (fun d => P_no_triple_at_(n d, d) - exp(-C(n d, 3)/d²)) atTop (nhds 0)
```

This changes the strategy significantly:
- Quantitative Chen-Stein bound (JSON) → 500-800 lines of Stein's operator + dependency graphs
- Qualitative Tendsto (actual axiom) → method of moments suffices (~150-300 lines)

The pool/JSON-stated formal target overstates what is needed to remove the axiom from this file.

### Method-of-Moments Strategy Sketch

Standard textbook proof outline (see Bollobás *Random Graphs* §1.3):

Let X_d := number of unordered birthday triples among `n(d)` people, i.e.,
X_d = Σ_{i<j<k} 𝟙{f(i)=f(j)=f(k)} on the uniform measure over `Fin (n d) → Fin d`.

1. **First moment**: E[X_d] = C(n d, 3)/d² → c³/6 =: λ. (provable in Lean today; cardinality argument)
2. **Higher factorial moments**: For each fixed r, E[(X_d)_r] → λ^r (the r-th factorial moment of Poisson(λ)).
   - Reduces to counting r-tuples of triples by overlap pattern: independent ones give λ^r·(1+o(1)); overlapping pairs contribute o(1).
   - Each fixed r is a finite combinatorial sum; the o(1) terms come from `Filter.Tendsto` of polynomial ratios in d.
3. **Method of moments**: For Poisson, factorial-moment convergence implies distribution convergence. Then `P(X_d = 0) → e^{-λ}` is the r=0 specialization combined with Bonferroni inequalities.

**Mathlib coverage**:
- `Filter.Tendsto`, polynomial limits at infinity: present, well-developed
- Factorial-moment computation as Finset sums: native Lean territory, no probability dependency
- "Method of moments → distribution convergence" theorem for Poisson: NOT in Mathlib, but for the specific case `P(X_d = 0)` we don't need the full theorem — Bonferroni inclusion-exclusion suffices.

### Bonferroni Path (Most Promising)

Use Bonferroni inequalities directly:

For any odd r:    P(X_d ≥ 1) ≥ Σ_{k=1}^{r} (-1)^{k+1} S_k(d)
For any even r:   P(X_d ≥ 1) ≤ Σ_{k=1}^{r} (-1)^{k+1} S_k(d)

where S_k(d) = E[(X_d choose k)] = Σ over k-subsets of triples of P(all k triples coincide).

By definition of `Real.exp` Taylor series and choosing r → ∞ slowly enough (e.g., r = ⌈log d⌉), `Σ (-1)^{k+1} S_k(d) → 1 - e^{-λ}`. Both Bonferroni bounds squeeze P(X_d ≥ 1).

**Estimated scope**: 200-300 lines of Lean. Most of the work is the inclusion-exclusion identity for `Finset.card.filter` + the asymptotic counting `S_k(d) → λ^k/k!`.

### Why This Wasn't Found in Session 1

Session 1's knowledge.md frames the goal as "prove the Chen-Stein bound", which matches the pool JSON formal but not the actual Lean axiom. Re-reading the file's axiom directly shows the lighter qualitative form. This is a pool-staleness issue: the JSON `problemStatement.formal` was probably written before the Lean file was settled.

### Recommended Next Action

1. **Update problem JSON** so `problemStatement.formal` matches the actual qualitative axiom (Tendsto, not absolute-value bound).
2. **Try Bonferroni**: implement `S_k(d)` counting lemma and the Bonferroni-Tendsto squeeze argument.
3. **Aristotle-friendly subgoals** (companion file): each `S_k(d) → λ^k/k!` for fixed k is a polynomial-ratio limit, well within `Filter.Tendsto`/`norm_num`/`polyrith` automation reach.

### Files Modified This Session

- `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/knowledge.md` — added Session 2
- `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json` — phase NEW → ORIENT, insights/nextSteps refreshed
- (No Lean files modified — disk near-full constraint, see CLAUDE.md feedback note; deferred to next session)

### Disk-Constraint Disclaimer

Host disk at 98% (304 MiB free) at session start. Per memory `feedback_disk_full_blocks_research`, no Docker builds were attempted and no Lean source edits were made — the strategy refinement is documentary only. The Bonferroni path needs to be drafted in a future session when disk has been reclaimed.

---

## Dead Ends

- **Chen-Stein from scratch this session**: Too large (~500-800 lines of measure theory infrastructure) — and overkill for the qualitative axiom (Session 2 finding)
- **Second moment → exact bound**: Second moment proves asymptotics, not explicit error bounds
- **Union bound as proof of main axiom**: Only proves one direction, not the bilateral approximation bound
- **Quantitative Chen-Stein (Session 1 framing)**: Mismatched scope — actual axiom is qualitative, lighter methods apply

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

---

## Session 2026-04-29 (Session 3, researcher-4) — Lemma A Foundation in Lean

**Mode**: REVISIT (RICH knowledge tier, score 16)
**Outcome**: ACT (partial) — added the foundation lemma `nc_div_pow_tendsto` that
backs Lemma A; Lemmas A and B themselves still pending. No axiom or sorry
delta this session (axiom remains, no new sorries).

### What I Did

1. Re-read Session 2's decomposition strategy and confirmed the axiom signature
   in `BirthdayProblemOQ03OQ01OQ02.lean:325-334` (qualitative `Filter.Tendsto …
   atTop (nhds 0)`).
2. Searched Mathlib (4.26) for the asymptotic combinators that Lemmas A/B need:
   - **Found**: `tendsto_nat_floor_mul_div_atTop {a : R} (ha : 0 ≤ a) : Tendsto
     (fun x ↦ (⌊a * x⌋₊ : R) / x) atTop (𝓝 a)` in
     `Mathlib.Analysis.SpecificLimits.Basic`. This is exactly the
     floor-quotient asymptotic that prior sessions described as "routine
     Mathlib composition" without naming the actual lemma.
   - **Found**: `tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (· ^ y :
     ℝ → ℝ) atTop atTop` in
     `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`.
   - **Found**: `tendsto_natCast_atTop_atTop` in
     `Mathlib.Order.Filter.AtTopBot.Archimedean` for the `ℕ → ℝ` cast lift.
   - **Confirmed not in Mathlib**: any qualitative method-of-factorial-moments
     → Poisson lemma. `Mathlib.Probability.Distributions.Poisson` still has
     only the PMF/measure constructors (no convergence theorems). Session 2's
     framing of the Lemma C gap remains accurate.
3. Added `nc_div_pow_tendsto` to `BirthdayProblemOQ03OQ01OQ02.lean` between
   the axiom and §6:

   ```lean
   lemma nc_div_pow_tendsto (c : ℝ) (hc : 0 < c) :
       Filter.Tendsto
         (fun d : ℕ => (⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) / (d : ℝ) ^ ((2 : ℝ) / 3))
         Filter.atTop (nhds c) := by
     have hpow : Filter.Tendsto (fun d : ℕ => (d : ℝ) ^ ((2 : ℝ) / 3))
         Filter.atTop Filter.atTop :=
       (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp tendsto_natCast_atTop_atTop
     exact (tendsto_nat_floor_mul_div_atTop hc.le).comp hpow
   ```

4. Added a docstring block above the lemma recording Session 2's full A/B/C
   decomposition strategy in-source, so future sessions don't need to recover
   the framing from the JSON / knowledge.md alone.

### Why This Is Real Progress (and the limit thereof)

- The lemma is a fully proved Lean theorem (`:= by … exact …`, no `sorry`).
- It's the first concrete in-source piece of Session 2's decomposition strategy,
  bridging a Mathlib lookup that prior sessions had described abstractly.
- It's **not** Lemma A itself: that requires composing this floor-quotient
  asymptotic with `Tendsto.pow` (cubing) and a polynomial-vs-falling-factorial
  bound to get from `(⌊c·d^(2/3)⌋ : ℝ)³ / d²` to `(C(⌊c·d^(2/3)⌋, 3) : ℝ) / d²`.
  Estimated remaining work for Lemma A: ~50 lines of `Filter.Tendsto.{const_mul,
  pow, sub}` + `Nat.choose_three` polynomial expansion + a `≤ 1/d^(2/3)` bound
  for the lower-order correction. Lemma B remains a one-liner via
  `Real.continuous_exp.tendsto.comp (Lemma A).neg`.

### Verification Status

- **Docker build NOT verified this session.** Three docker invocations during
  the session hung partway through `docker info` (no progress after >12 min,
  background tasks confirmed daemon was responding to `docker info` but the
  Server section timed out). Treated as Docker infrastructure failure per
  saved memory `feedback_docker_build_io_errors.md`: "Don't change code in
  response — push and let next session retry."
- The two-line proof `(tendsto_nat_floor_mul_div_atTop hc.le).comp hpow`
  composes Mathlib lemmas whose signatures were verified by direct file read
  in `/System/Volumes/Data/private/tmp/mathlib4/Mathlib/Analysis/SpecificLimits/Basic.lean`
  and `…/SpecialFunctions/Pow/Asymptotics.lean`. The composition types align,
  but a green Docker build is still the only authoritative check.

### Files Modified

- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (+38 lines: docstring +
  `nc_div_pow_tendsto`)

### Next Steps

1. **Next session — verify the build** for `Proofs.BirthdayProblemOQ03OQ01OQ02`
   when Docker is responsive. If `nc_div_pow_tendsto` fails to type-check,
   the most likely fix is the `tendsto_natCast_atTop_atTop` typeclass
   instances — try explicit `Tendsto ((↑) : ℕ → ℝ) atTop atTop` annotation.
2. **Add Lemma A** (`lambda_tendsto`) building on `nc_div_pow_tendsto`:
   - `((⌊c·d^(2/3)⌋ : ℝ) / d^(2/3))^3 → c³` via `Tendsto.pow`.
   - Algebraic identity: `((d : ℝ)^(2/3))^3 = (d : ℝ)^2` via `Real.rpow_mul` /
     `Real.rpow_natCast` (the right reduction for `(2/3)·3 = 2`).
   - Polynomial-to-falling-factorial: show that
     `((⌊c·d^(2/3)⌋ : ℝ).choose 3 : ℝ) - (⌊c·d^(2/3)⌋ : ℝ)^3 / 6` divided by `d²`
     tends to `0` (the difference is `O(d^(4/3) / d²) = O(d^{-2/3})`).
3. **Add Lemma B** as a one-liner once Lemma A is in.
4. Hold off on Lemma C until Lemmas A+B are merged — the axiom can then be
   restated as "Lemma C only", isolating the Mathlib gap.

---

## Session 2026-05-03 (Session 4) — Lemmas A and B Implemented

**Mode**: REVISIT (RICH knowledge tier, score 21)
**Outcome**: PROGRESS — Lemma A (lambda_tendsto) and Lemma B (exp_lambda_tendsto) implemented; Docker build pending.

### What I Did

1. Confirmed `nc_div_pow_tendsto` from Session 3 is present (lines 365–372).
2. `rpow23_atTop` (private): `d^(2/3) → +∞` extracted for reuse.
3. `two_div_rpow23_tendsto_zero` (private): `2/d^(2/3) → 0` via `tendsto_inv_atTop_zero.comp`.
4. `lambda_tendsto` (Lemma A): squeeze proof, `C(nc(d),3)/d² → c³/6` via `choose3_lb`/`choose3_ub` bounds and `(d^(2/3))^3 = d^2`.
5. `exp_lambda_tendsto` (Lemma B): one-liner `Real.continuous_exp.tendsto.comp lambda_tendsto.neg`.

### Files Modified

- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (+89 lines)

### Next Steps

1. Verify Docker build succeeds; open PR.
2. Restate axiom as Lemma C only: `P_no_triple(nc(d),d) → exp(-c³/6)`.
3. Lemma C: method-of-factorial-moments (not in Mathlib 4.26).
