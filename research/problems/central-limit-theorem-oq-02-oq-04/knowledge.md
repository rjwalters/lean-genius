# Knowledge: central-limit-theorem-oq-02-oq-04

## Session log

### Session 1 (researcher-12, 2026-05-11) — S1 OBSERVE

**Mode**: FRESH (pristine tier-B slug, knowledgeScore = 0).
**Outcome**: Survey + scaffolding only.  No Lean changes.

#### Parent file state (`CentralLimitTheoremOQ02.lean`)

- 17 proved theorems, 2 axioms, 3 sorries (per its tail comment, lines 696–727).
- The two relevant existing declarations:
  - `alphaMixingCoeff` (line 419): `noncomputable def` of the α-mixing
    coefficient as a nested supremum over measurable sets.
  - `AlphaMixingSequence` (line 427): structure carrying a sequence,
    past/future σ-algebras, a numeric bound `α : ℕ → ℝ`, mixing decay
    `Tendsto α atTop (nhds 0)`, and `mixing_bound` linking the abstract
    coefficient to the sequence's quantitative bound.
- `longRunVariance` (line 462): defined as
  `∫ X 0 ω² ∂μ + 2 · ∑' k, ∫ X 0 ω · X (k+1) ω ∂μ` —
  exactly the right object for OQ-02-OQ-04.
- Ibragimov's CLT is **stated in docstring (lines 447–454) only** —
  there is no theorem declaration named `mixing_clt` or `ibragimov_clt`.
- `independent_implies_zero_mixing` (line 480) has a `sorry` at the
  nested-ciSup-of-zeros step (noted by author as a `ConditionallyCompleteLattice`
  elaboration issue, not a mathematical issue).

#### Mathlib state (queried 2026-05-11)

- `grep -rln "α-mixing\|StronglyMixing\|StrongMixing\|MixingCoefficient" Mathlib/Probability/` ⇒ **no hits**.
- `grep -rln "alphaMixingCoeff" Mathlib/` ⇒ **no hits**.
- Mathlib has no α-mixing API.  This means OQ-02-OQ-04's Lean statement must
  reuse the parent's `alphaMixingCoeff` / `AlphaMixingSequence` definitions
  rather than importing from Mathlib.

  Closest existing Mathlib infrastructure:
  - `Mathlib.MeasureTheory.Measure.MeasureSpace` — generic measure spaces.
  - `Mathlib.Probability.IdentDistrib` — identically distributed predicate
    (useful for *stationarity*: `X k =ᵈ X 0`).
  - `Mathlib.Probability.Independence.Basic` — `iIndep` family
    (the α = 0 endpoint).
  - `Mathlib.Probability.Variance` — `Var[X]`, `Covariance`.
  - `Mathlib.Probability.IntegrableExpectation` — moment integrability.
  - `Mathlib.MeasureTheory.Function.LpSpace` — `‖X‖_{p}` norms used by
    Davydov inequality.

#### Key mathematical objects to scaffold (S2 ORIENT target)

1. `Stationary X μ : Prop` — `∀ k, IdentDistrib (X k) (X 0) μ μ` *plus*
   joint stationarity for finite tuples (the parent file has no
   stationarity predicate; this is the missing ingredient).
2. `PolynomialMixingRate (α : ℕ → ℝ) (C r : ℝ) : Prop` —
   `∀ n, α n ≤ C * (n : ℝ) ^ (-r)`.
3. `MomentBound (X : ℕ → Ω → ℝ) (μ : Measure Ω) (p : ℝ) : Prop` —
   `∀ k, ∫⁻ ω, |X k ω|^p ∂μ < ∞`.
4. `IbragimovHypotheses` — bundle (1)+(2)+(3) with consistency
   `r > (p / (p - 2))` where `p = 2 + δ`.
5. `mixing_clt_ibragimov` — the theorem statement, currently an `axiom`
   in S1 / promoted to `theorem ... := by sorry` in S2.

#### Mathlib gaps

- **No α-mixing primitive.**  Plan: keep building on parent's
  `alphaMixingCoeff` until the API stabilizes, then propose to upstream.
- **No Davydov / Ibragimov covariance inequality.**  Needs
  `Mathlib.MeasureTheory.Function.LpSpace` Hölder-style proof.  A
  standalone helper `davydov_cov_bound` could live in the proof file
  or a companion `…Aristotle.lean`.
- **No Bernstein block lemma.**  Block decomposition is bespoke; it
  would live in this proof file.
- **No quantitative variance-of-sum bound for stationary sequences.**
  Parent has `variance_sum_bounded_of_converges` (line 662) but only
  for sequences with a *limit* of variances, not for a sum of
  stationary covariances.  This is a self-contained lemma worth
  having (and is a candidate Aristotle target).

#### Open subproblems with tractability estimates

| Subproblem | Mathlib gap | Difficulty | Path |
|---|---|---|---|
| Davydov / Hölder-type covariance bound | Yes | Medium | LpSpace + Hölder |
| `α(n) ≤ C n^{-r}` ⇒ `∑ α(n)^{δ/(2+δ)} < ∞` | No | Easy | `Real.rpow` arithmetic |
| Long-run variance is absolutely convergent under poly. mixing | Partial | Medium | Davydov + Real.summable_of_le |
| Bernstein block sizing satisfies all four asymptotic constraints | No | Easy | Real-analysis bookkeeping |
| Lindeberg condition for large blocks | No | Hard | Truncation + (2+δ)-moment |
| Characteristic-function convergence | No | Very hard | Lévy continuity |
| Negligibility of small blocks | No | Medium | Variance bookkeeping |
| Recovery of i.i.d. CLT | Indirect | Easy (once others done) | Specialize `α ≡ 0` |

#### Decision: scope of OQ-02-OQ-04

This slug should produce, over several sessions:

- **S1 OBSERVE (this session):** scaffold the problem statement, identify
  the threshold `r > (2+δ)/δ`, document Mathlib gaps, plan S2 ORIENT.
  **No Lean code.**
- **S2 ORIENT:** introduce `Stationary`, `PolynomialMixingRate`,
  `MomentBound`, `IbragimovHypotheses`, and the theorem statement
  `mixing_clt_ibragimov` as `:= by sorry`.
- **S3 ACT:** prove the long-run-variance absolute convergence
  (the easiest sub-result with real mathematical content).
- **S4 ACT:** Davydov covariance bound (or companion Aristotle file
  with a clean Hölder route).
- **S5+ ACT:** Bernstein block lemma + Lindeberg + recovery of i.i.d.

#### Why not S2/S3 in this session

- Memory's tier-B SCAFFOLD wave warning (2026-05-12): even 0-score
  slugs are racing within 15–30 minute windows.  S1 OBSERVE
  documentation-only minimizes wasted effort if a parallel session
  produces the scaffold first.
- Memory's "MODERATE+ tier over-subscribed" guidance: 1 productive
  PR per session beats burning hours on a contested slug.

## Forward path

After S1 merges:

1. **S2 ORIENT** (~1 hour, ~200 lines):
   - Create `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean`.
   - Import `Proofs.CentralLimitTheoremOQ02` (re-uses `alphaMixingCoeff`).
   - Define `Stationary`, `PolynomialMixingRate`, `IbragimovHypotheses`.
   - State `mixing_clt_ibragimov := by sorry`.
   - State `longrun_variance_convergent_under_polymix := by sorry`
     (the genuinely tractable sub-result).
   - Create gallery entry `src/data/proofs/central-limit-theorem-oq-02-oq-04/`.

2. **S3 ACT** (~1 hour, ~100 lines):
   - Prove the threshold arithmetic
     `∑ n^{-r δ/(2+δ)} < ∞  ⇔  r > (2+δ)/δ` via
     `Real.summable_one_div_nat_rpow`.
   - Reduce `longrun_variance_convergent_under_polymix` to Davydov,
     leaving Davydov as a single sorry.

3. **S4+ ACT:** Davydov, Bernstein blocks, full Lindeberg.

## References

- Ibragimov, I. A. (1962). "Some limit theorems for stationary processes."
  *Theory of Probability and its Applications*, 7(4), 349-382.
- Davydov, Yu. A. (1968). "Convergence of distributions generated by
  stationary stochastic processes."  *Theory of Probability and its
  Applications*, 13(4), 691-696.
- Rio, E. (1993). "Covariance inequalities for strongly mixing processes."
  *Annales de l'I.H.P. Probabilités et Statistiques*, 29(4), 587-597.
- Bradley, R. C. (2005). "Basic properties of strong mixing conditions:
  a survey and some open questions."  *Probability Surveys*, 2, 107-144.
  (Comprehensive modern reference.)
- Doukhan, P. (1994). *Mixing: Properties and Examples*.  Lecture Notes
  in Statistics 85, Springer.  (Definitive monograph.)

## Session log — Session 2 (researcher-6, 2026-05-12) — S2 ORIENT

**Mode**: REVISIT (build on S1's S2 plan).

**Outcome**: Scaffold complete.  4 definitions, 1 structure, 2 main theorem
statements with sorries, 2 fully-proven summability helpers.

### What I did

- Created `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` (231 lines).
- **Predicates and structure**:
  - `Stationary μ X` via marginal `IdentDistrib (X k) (X 0) μ μ` (slice version).
  - `PolynomialMixingRate α C r` — `α n ≤ C · n^(-r)` for `n ≥ 1`.
  - `MomentBound2δ μ X δ` — `∀ k, MemLp (X k) (2 + δ) μ`.
  - `IbragimovHypotheses μ X δ C r` — 11 fields bundled: stationary,
    integrable, mean_zero, delta_pos, moment_bound, alpha, pastSigma,
    futureSigma, alpha_bound, poly_rate, rate_admissible.
- **Proven summability helpers**:
  - `polynomial_summable_of_exponent_gt_one (s : ℝ) (hs : 1 < s) : Summable (fun n : ℕ => (n : ℝ) ^ (-s))`
    — via Mathlib's `Real.summable_nat_rpow_inv`, with explicit handling of the
    `n = 0` boundary case via `Real.zero_rpow` and `Real.rpow_neg` for `n ≥ 1`.
  - `ibragimov_threshold_summable (δ r : ℝ) (hδ : 0 < δ) (hr : r > (2 + δ) / δ) : Summable (fun n : ℕ => (n : ℝ) ^ (-(r * δ / (2 + δ))))`
    — direct algebraic derivation of `1 < rδ/(2+δ)` from the threshold,
    then applying the polynomial-summability helper.
- **Theorem statements (sorries)**:
  - `longrun_variance_absolutely_convergent` — `∑_k |∫ X 0 ω · X (k+1) ω dμ| < ∞`
    under `IbragimovHypotheses`. S5 target.
  - `mixing_clt_ibragimov` — `φ_{S_n / √n}(t) → exp(-σ² t² / 2)` for all
    `t : ℝ`, under `IbragimovHypotheses` + `σ² > 0` (σ² supplied as parameter,
    not computed inline from `longRunVariance`). S6+ target.
- Created `src/data/proofs/central-limit-theorem-oq-02-oq-04/`:
  - `meta.json` (status `axiomatized`, sorries 2, axioms 0, lineCount 231).
  - `annotations.json` (empty).
  - `index.ts`.

### Key findings

- The Mathlib name is `Real.summable_nat_rpow_inv` (not
  `Real.summable_one_div_nat_rpow` — the latter would be a related result
  but isn't in the repo's existing usage).
- The sharp-threshold algebra `r > (2+δ)/δ ⇒ rδ/(2+δ) > 1` is one step:
  multiply both sides of `r > (2+δ)/δ` by `δ > 0` (using
  `mul_lt_mul_of_pos_right` and `div_mul_cancel₀`), giving `r·δ > 2+δ`, then
  divide both sides by `2+δ > 0` (using `lt_div_iff₀`), giving `1 < rδ/(2+δ)`.
- The main CLT statement separates σ² from the parent's `longRunVariance`
  definition — supplying it as an external parameter avoids the awkward
  inline plumbing of integrability/mean-zero proofs.
- The `IbragimovHypotheses` structure should be refined in S3+ to use
  joint stationarity (over finite tuples) rather than just marginal slices,
  but the marginal slice suffices for the statement itself.

### Mathlib gaps confirmed (S2 update of S1 list)

- **No Davydov inequality** in `Mathlib.MeasureTheory.Function.LpSpace`.
  Build in S3 as standalone lemma `davydov_cov_bound`.
- **No Bernstein block decomposition** in Mathlib's probability sections.
  Build in S5 as set of helper lemmas + main block decomposition theorem.
- **No quantitative Lindeberg verification under polynomial mixing**.
  Compose S3 + S5 to derive in S7.

### Files modified

- `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` (new, 231 lines)
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/meta.json` (new)
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/annotations.json` (new)
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/index.ts` (new)
- `research/problems/central-limit-theorem-oq-02-oq-04/state.md` (updated S2)
- `research/problems/central-limit-theorem-oq-02-oq-04/knowledge.md` (this entry)

### Next steps for S3+

1. **S3**: Prove Davydov's covariance inequality
   `|Cov(X,Y)| ≤ 12·α^{δ/(2+δ)}·‖X‖_{2+δ}·‖Y‖_{2+δ}` (~150 lines).
   Standard Hölder + indicator-decomposition proof; cleanly separates into
   `cov_indicator_bound` + `Lp_norm_bound`.
2. **S4** = old S5: Close `longrun_variance_absolutely_convergent` using
   Davydov per-term + `ibragimov_threshold_summable` + `Summable.comp_injective`
   for the index shift `k ↦ k+1`.
3. **S5+**: Bernstein blocks, Lindeberg, full CLT — per the decomposition
   table in state.md.

### Aristotle

The two sorries are **deferred-to-S3+** statements, not routine lemmas.
The two proven summability helpers are useful standalone but already proven.
No new Aristotle targets in this session.

## Session log — Session 3 (researcher-1, 2026-05-12) — S3 ACT

**Mode**: REVISIT (continue S2 plan from the state.md "Option A" recommendation).

**Outcome**: Reduce `longrun_variance_absolutely_convergent` to a single
named Davydov sorry; ship 3 new proven theorems and 3 new structure fields.

### What I did

#### Lean changes (`proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean`)

- **Extended `IbragimovHypotheses`** with three new fields needed for
  per-term Davydov:
  - `alpha_nonneg : ∀ n, 0 ≤ alpha n` — needed because the parent file's
    `alphaMixingCoeff_nonneg` is omitted due to nested `ciSup` elaboration
    complexity, and `Real.rpow_le_rpow` needs nonneg base for monotonicity.
  - `past_measurable : ∀ k, Measurable[pastSigma k] (X k)` — `X k` is
    measurable w.r.t. its own past at time `k`.
  - `future_measurable : ∀ k, Measurable[futureSigma k] (X k)` — `X k` is
    measurable w.r.t. its own future at time `k`.
- **Stated `davydov_covariance_inequality`** as a sorry (S4 target).
  The statement takes an abstract upper bound `α₀` rather than the
  abstract α-mixing coefficient itself, so per-term applications can plug
  in the numerical mixing bound `H.alpha (k+1)` directly. Exponent is
  `(p - 2) / p`, which specializes to `δ/(2+δ)` when `p = 2 + δ`.
- **Proved `stationary_eLpNorm_eq`** in one line via
  `(H.stationary k).eLpNorm_eq p` — Mathlib's `IdentDistrib.eLpNorm_eq`
  gives this directly.
- **Proved `polynomial_mixing_summable`** combining (i) `Real.rpow_le_rpow`
  monotonicity of `x ↦ x^q` at q = δ/(2+δ); (ii) `Real.mul_rpow` and
  `Real.rpow_mul` for the expansion `(C · x^{-r})^q = C^q · x^{-rq}`;
  (iii) `ibragimov_threshold_summable` (already proven in S2);
  (iv) `summable_nat_add_iff 1` for the n→n+1 index shift;
  (v) `Summable.mul_left K` to scale by the constant; (vi)
  `Summable.of_nonneg_of_le` (from `Mathlib.Topology.Instances.ENNReal.Lemmas`)
  for the comparison test.
- **Proved `longrun_variance_absolutely_convergent`** by chaining:
  per-term Davydov (the new sorry) + `stationary_eLpNorm_eq` to identify
  `‖X 0‖_p` with `‖X (k+1)‖_p` + `H.mean_zero` (twice) + `zero_mul`,
  `sub_zero` to kill the `(∫ X 0)(∫ X (k+1))` term + `linarith` to match
  the constant `K = 12 · M · M`.

#### Net change to sorry / axiom counts

| Item | Before (S2) | After (S3) |
|---|---|---|
| `mixing_clt_ibragimov` | sorry | sorry (unchanged) |
| `longrun_variance_absolutely_convergent` | sorry | **proven** |
| `davydov_covariance_inequality` | (not declared) | sorry (**new**) |
| Total sorries in file | 2 | 2 |
| Total `axiom` declarations | 0 | 0 |

The net sorry count is unchanged, but the open content has been refactored:
the catch-all "longrun_variance is hard" placeholder is now resolved
modulo a single canonical analytic engine (Davydov).

### Key findings

- **`IdentDistrib.eLpNorm_eq`** is the right Mathlib API for the
  stationary norm equality. It takes the L^p exponent as an `ℝ≥0∞`
  argument and works for any `NormedAddCommGroup` codomain
  (including ℝ).
- **`summable_nat_add_iff`** is generated via `@[to_additive]` from
  `multipliable_nat_add_iff` in `Mathlib.Topology.Algebra.InfiniteSum.NatInt`.
  The implicit `f` argument is taken via named-argument syntax
  `(f := ...)`.
- **`Summable.of_nonneg_of_le`** lives in
  `Mathlib.Topology.Instances.ENNReal.Lemmas` (line 1040 of v4.26.0).
  Signature: `(hg : 0 ≤ g) (hgf : g ≤ f) (hf : Summable f) : Summable g`.
- **The IbragimovHypotheses S2 structure was incomplete**:  missing the
  measurability fields needed to apply Davydov. Adding them in S3 is
  the right move (structural completeness), though it would have been
  cleaner if S2 had anticipated this. (No external consumers of the
  structure, so the change is non-breaking.)

### Files modified

- `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` (231 → 402 lines)
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/meta.json` (theoremCount
  2→7, lineCount 231→402, description/proofStrategy/sections/mainTheorems
  updated for S3 status)
- `research/problems/central-limit-theorem-oq-02-oq-04/state.md` (phase ORIENT
  → ACT, decomposition plan updated, S4 next action set)
- `research/problems/central-limit-theorem-oq-02-oq-04/knowledge.md` (this entry)

### Worktree-vs-main-repo trap encountered

I initially Edit'd the Lean file using absolute paths to `/Users/.../proofs/...`
(MAIN REPO path), not `/Users/.../.loom/worktrees/researcher-1/proofs/...`
(WORKTREE path). All my Edit/Write calls landed in the MAIN REPO's
working tree (which was on an unrelated audit branch). Recovered via:
(a) `cp` the in-memory main-repo working-tree copy to /tmp;
(b) `git checkout origin/main -- proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean`
in main repo to restore;
(c) `cp /tmp/...` into the worktree;
(d) use only worktree-absolute paths for the remaining JSON/markdown edits.

This is the exact "Edit/Write absolute paths bypass the worktree silently"
trap noted in MEMORY.md — should have caught it sooner. From now on,
always start absolute paths with `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1/`
when in this session.

### Next steps for S4+

1. **S4**: Discharge `davydov_covariance_inequality` via Hölder + indicator
   decomposition. References: Doukhan 1994 §1.2.2, Bradley 2007 Vol I
   Thm 3.7. ~150 lines, no Mathlib gaps beyond Hölder.
2. **S5**: Refine `Stationary` to joint tuple stationarity (prerequisite
   for Bernstein blocks). ~100 lines.
3. **S6+**: Bernstein blocks, Lindeberg, full CLT — per the decomposition
   table in state.md.

### Aristotle

No new Aristotle targets in this session. The Davydov sorry is genuinely
analytic (not routine) and is the canonical S4 target — not a candidate
for automated proof search.

## Session log — Session 4 (researcher-5, 2026-05-12) — S4 prep (Davydov-independent helpers)

**Mode**: REVISIT.  Contest situation at claim time:
- S3 (PR #17820) had just merged 1 h before.
- Two CONFLICTING S3 PRs still open (#17826 rebased-Davydov-axiom, #17810
  researcher-8 bridge lemmas) — superseded by the S3 merge.
- The state.md "Session 4 next action" was Davydov (~150 lines, single big
  measure-theoretic proof) — too large for one session and contested if a
  parallel agent attempts it.

**Strategy chosen**: prep S6+ infrastructure (Bernstein blocks / Lindeberg-Feller
invocation) by adding **Davydov-independent helper lemmas**.  These are pure
consequences of the structure's existing fields and Mathlib's L^p / IdentDistrib
API — they introduce no new dependencies, no new sorries, and unblock the S6+
proof skeleton.

### What I did

Added a new **Part IV-bis** to `CentralLimitTheoremOQ02OQ04.lean` between
the long-run-variance proof and the main-theorem statement.  Five new
proven theorems, all in the `IbragimovHypotheses` namespace:

1. **`IbragimovHypotheses.memLp_two`** — `MemLp (X k) 2 μ`.  Lyapunov's
   inequality on the probability measure: `(2 + δ)`-moment ⇒ `2`-moment
   via `MemLp.mono_exponent` applied to the ENNReal-coerced exponents.
   Key Mathlib lemma: `MeasureTheory.MemLp.mono_exponent` (used at
   `LawsOfLargeNumbersOQ01OQ02.lean:75` for the same pattern).
2. **`IbragimovHypotheses.integrable_sq`** — `Integrable (fun ω => (X k ω)^2) μ`.
   Bridges `MemLp · 2 μ` to `Integrable (·^2)` via
   `memLp_two_iff_integrable_sq_norm` + a one-step `‖x‖^2 = x^2` congruence
   (`Real.norm_eq_abs` then `sq_abs`).
3. **`IbragimovHypotheses.integral_sq_eq`** — `∫ (X k)^2 = ∫ (X 0)^2`.
   Pushforward of marginal stationarity through `(· ^ 2) : ℝ → ℝ`:
   `((H.stationary k).comp (measurable_id.pow_const 2)).integral_eq`.
4. **`IbragimovHypotheses.partialSum_integrable`** — `Integrable (∑_{k<n} X k) μ`.
   `MeasureTheory.integrable_finset_sum` applied to `H.integrable`.
5. **`IbragimovHypotheses.partialSum_mean_zero`** — `∫ ∑_{k<n} X k = 0`.
   `integral_finset_sum` swap + `Finset.sum_eq_zero` of per-term mean-zero.

### Why these (instead of attempting Davydov S4)

- **Davydov is contested + monolithic.**  Iter-on-iter risk of being scooped
  mid-session by a parallel agent claiming the same slug; ~150-line single
  proof would need 1-2 sessions just to land cleanly.
- **Helper lemmas are non-conflicting + non-blocking.**  They don't touch
  the Davydov sorry, the long-run-variance proof, or the main theorem
  statement.  A future Davydov PR will rebase cleanly on this work; a
  future S6+ Bernstein-blocks PR will use these helpers directly.
- **Real value.**  S6+ needs second-moment finiteness in every Lindeberg
  verification, partial-sum mean-zero in the centering step, and stationary
  second-moment equality to identify `Var(X k) = Var(X 0)`.  Each was an
  inline obligation in any future Bernstein-blocks proof; now they are
  one-line `H.memLp_two k`, `H.integrable_sq k`, `H.integral_sq_eq k`,
  etc.

### Net change to sorry / axiom counts

| Item | Before (S3) | After (S4 helpers) |
|---|---|---|
| `mixing_clt_ibragimov` | sorry | sorry (unchanged) |
| `davydov_covariance_inequality` | sorry | sorry (unchanged) |
| Total sorries in file | 2 | 2 |
| Total `axiom` declarations | 0 | 0 |
| Total proven theorems | 7 | **12** |
| Lines | 402 | ~485 |

Pure infrastructure addition — zero new assumptions, zero new sorries.

### Key Mathlib API confirmed

- `MeasureTheory.MemLp.mono_exponent` — Lyapunov inequality on probability
  measure.  Takes `(hpq : p ≤ q) (h : MemLp f q μ) : MemLp f p μ`.
- `memLp_two_iff_integrable_sq_norm` — `MemLp f 2 μ ↔ Integrable (‖f ·‖^2) μ`
  given AEStronglyMeasurable.
- `Real.norm_eq_abs` — `‖x‖ = |x|` for `x : ℝ`.  `sq_abs : |x|^2 = x^2`.
- `IdentDistrib.comp` — pushforward of identical distributions through a
  measurable map: `h.comp hu : IdentDistrib (u ∘ X) (u ∘ Y)`.
- `Measurable.pow_const` — `Measurable f → Measurable (f^n)` for `n : ℕ`.
- `MeasureTheory.integrable_finset_sum` — finite sum of integrables is
  integrable.
- `integral_finset_sum` — swap of finite-sum and Bochner integral
  (already used at parent file OQ02:97).

### Files modified

- `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` (402 → ~485 lines, +5
  proven theorems in Part IV-bis)
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/meta.json` (theoremCount
  7 → 12, lineCount 402 → ~485, sections updated to reflect new Part IV-bis)
- `research/problems/central-limit-theorem-oq-02-oq-04/state.md` (S4 prep
  recorded; next action remains Davydov but now with rich helper API to
  build atop)
- `research/problems/central-limit-theorem-oq-02-oq-04/knowledge.md` (this
  entry)

### Next steps for S5+

1. **S5 (= old S4)**: Discharge `davydov_covariance_inequality` via Hölder
   + indicator decomposition.  References: Doukhan 1994 §1.2.2, Bradley
   2007 Vol I Thm 3.7.  ~150 lines.
2. **S6**: Refine `Stationary` to joint tuple stationarity (~100 lines).
3. **S7**: Bernstein blocks `p_n, q_n` (~150 lines) — uses `partialSum_*`
   helpers from this session directly.
4. **S8**: Large-block independence via mixing (~120 lines).
5. **S9**: Lindeberg condition on blocks (~100 lines) — uses
   `memLp_two`, `integrable_sq`, `integral_sq_eq` from this session.
6. **S10**: Invoke parent's Lindeberg-Feller CLT (~50 lines).

### Aristotle

No new Aristotle targets in this session.  The five helpers are all proven;
the Davydov sorry remains the canonical S5 (was S4) target and is still
genuinely analytic.
