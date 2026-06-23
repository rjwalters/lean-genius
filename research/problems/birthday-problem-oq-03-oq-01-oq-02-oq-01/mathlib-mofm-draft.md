# Mathlib Upstream Draft: Method of Factorial Moments (Layer 4 / Path C)

**Session**: 10 (researcher-6, 2026-05-08)
**Parent roadmap**: `lemma-c-roadmap.md` §6, Path C
**Target file**: `Mathlib/Probability/Distributions/Poisson/MethodOfFactorialMoments.lean`
**Status**: Pre-formalization specification — no Lean code committed to gallery, no
PR opened upstream yet.

This document refines the brief Path C sketch in §6 of the Session 9 roadmap into
a concrete pre-formalization specification. It does **not** introduce new
mathematical content for the gallery entry itself — its purpose is to make the
upstream-Mathlib contribution actionable by a future session (S16/S17 in the
roadmap) or, ideally, by an independent Mathlib contributor.

---

## 1. Why this lives outside the gallery

Lemma C in our entry — `P_no_triple(n_c(d), d) → exp(−c³/6)` — needs a
**Method of Factorial Moments** (MoFM) Poisson convergence theorem. Mathlib
v4.26.0 (the gallery's pin) has:

- `Mathlib.Probability.Distributions.Poisson` — only PMF/measure constructors;
- `Mathlib.Probability.Moments.Basic` — moments and MGF for ℝ-valued RVs;
- `TendstoInDistribution` (`Mathlib.MeasureTheory.Function.ConvergenceInDistribution`);
- `Nat.descFactorial` (`Mathlib.Data.Nat.Choose.Basic`),
  `descFactorial_eq_factorial_mul_choose`,
  `Nat.isEquivalent_descFactorial : n.descFactorial k ~ n^k`
  (`Mathlib.Analysis.SpecialFunctions.Choose`).

Mathlib master (post-v4.26.0) has, as of 2026-05-08:

- `Mathlib.Probability.Distributions.Poisson.PoissonLimitThm` (Yi Yuan, 2026-03-08):
  binomial→Poisson **PMF convergence** (`PMF.binomial → poissonPMF`), under
  hypotheses `n · p_n → λ` and `0 ≤ p_n ≤ 1`. This handles the *independent
  Bernoulli* case but does not cover dependent counting variables (our triples).

What is **missing in both v4.26 and master**:

1. A definition of the *factorial moment* `E[X · (X−1) · ... · (X−r+1)]` for
   ℕ-valued RVs.
2. The Poisson factorial moment identity `E[Y^{(r)}] = λ^r` for `Y ~ Poisson(λ)`.
3. The **Method of Factorial Moments** theorem: if a sequence of ℕ-valued RVs
   has all factorial moments converging to those of `Poisson(λ)`, then the
   sequence converges in distribution to `Poisson(λ)`.

This document specifies (1)–(3) for upstream contribution. (1) and (2) are
short and routine. (3) is the substantive theorem and the focus of the spec.

---

## 2. Generality choice

Three plausible levels of generality, in order:

| Level | Hypotheses on `X_n` | Conclusion | Pros | Cons |
|-------|--------------------|--------------|------|------|
| **(A) ℕ-valued** | `X_n : Ω → ℕ`, integrable factorial moments | `TendstoInDistribution` to `Poisson(λ)` | Simple, covers all enumeration applications | ℕ-only |
| **(B) integer-valued** | `X_n : Ω → ℤ`, almost-surely ≥ 0 | same | Slightly more general | Hypothesis is awkward; users will lift via `(·).toNat` |
| **(C) general ℝ-valued non-negative** | `X_n ≥ 0` a.s., factorial moments via `descFactorial` extended to ℝ | Convergence in distribution to a measure on ℝ supported on ℕ | Most general | Requires extending `descFactorial` to ℝ; less natural |

**Recommendation: (A)**. ℕ-valued counting variables are the universal use case
(random graph subgraph counts, urn occupancy, hash collisions, Poissonization
arguments, etc.). (B) and (C) can be derived as wrappers if needed.

Within (A), two further choices:

- **Conclusion form**: `TendstoInDistribution X_n (poissonMeasure λ) atTop ⟦Ω_n⟧ ℙ`
  vs. **pointwise PMF convergence** `∀ k, ℙ_n(X_n = k) → e^{-λ} λ^k / k!`.
- For ℕ-valued RVs these are equivalent (since `ℕ` is discrete and Poisson has
  no atoms outside ℕ — strictly, the equivalence is via the portmanteau theorem
  on the discrete topology).
- Mathlib precedent: the CLT (`tendstoInDistribution_inv_sqrt_mul_sum`) uses
  `TendstoInDistribution`. Match that style.
- Provide both as theorems; the pointwise one is the primary content, the
  `TendstoInDistribution` corollary is a one-line application of a portmanteau
  lemma we can either prove or import.

---

## 3. Lean signatures

### 3.1 Definitions

```lean
namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)

/-- The `r`-th factorial moment of a ℕ-valued random variable `X`,
`μ[X · (X−1) · ... · (X−r+1)]`. -/
noncomputable
def factorialMoment (X : Ω → ℕ) (r : ℕ) (μ : Measure Ω) : ℝ :=
  μ[fun ω => ((X ω).descFactorial r : ℝ)]

@[simp]
lemma factorialMoment_zero (X : Ω → ℕ) (μ : Measure Ω) :
    factorialMoment X 0 μ = (μ Set.univ).toReal := by
  simp [factorialMoment, Nat.descFactorial]

lemma factorialMoment_one (X : Ω → ℕ) (μ : Measure Ω) :
    factorialMoment X 1 μ = μ[fun ω => (X ω : ℝ)] := by
  simp [factorialMoment, Nat.descFactorial]
```

### 3.2 Poisson factorial moment identity

```lean
/-- Factorial moment of the Poisson distribution: `E[Y^{(r)}] = λ^r` for
`Y ~ Poisson(λ)`. -/
theorem factorialMoment_poissonMeasure (r : ℕ) (λ : ℝ≥0) :
    factorialMoment id r (poissonMeasure λ) = (λ : ℝ) ^ r := by
  -- Direct computation: ∑_k (descFactorial k r) · e^{-λ} λ^k / k!
  -- Using descFactorial_eq_factorial_mul_choose and reindexing j = k - r.
  sorry
```

The proof is a routine calculation:

```
∑_{k ≥ 0} k^{(r)} · e^{-λ} λ^k / k!
  = e^{-λ} ∑_{k ≥ r} k!/(k-r)! · λ^k / k!     (descFactorial vanishes for k < r)
  = e^{-λ} ∑_{k ≥ r} λ^k / (k-r)!
  = e^{-λ} · λ^r · ∑_{j ≥ 0} λ^j / j!         (j = k - r)
  = e^{-λ} · λ^r · e^{λ} = λ^r.
```

Lean machinery: `tsum_geometric` (no — wrong shape), `Real.exp_eq_tsum`,
`Nat.factorial_descFactorial`, and `tsum_mul_left`. About 15–25 lines.

### 3.3 The Method of Factorial Moments theorem

**Primary form** (pointwise PMF convergence):

```lean
/--
**Method of Factorial Moments**: if a sequence of ℕ-valued random variables has
all factorial moments converging to those of `Poisson(λ)`, then the PMF of `X_n`
converges pointwise to the Poisson PMF.

Hypotheses:
* `X_n : Ω_n → ℕ` for each `n`, where the underlying probability space may
  vary with `n`.
* For every `r : ℕ`, the `r`-th factorial moment of `X_n` is well-defined
  (integrable) and tends to `λ^r` as `n → ∞`.
* The `X_n` are uniformly bounded in some factorial moment (this is automatic
  if the limits `λ^r` are finite — see Carleman / Stieltjes-moment hypothesis
  below).

Conclusion: for every `k : ℕ`, the probability `ℙ_n(X_n = k)` converges to
`exp(−λ) · λ^k / k!`.
-/
theorem tendsto_pmf_of_tendsto_factorialMoment
    {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)} (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (X : ∀ i, Ω i → ℕ) (hX : ∀ i, Measurable (X i))
    (λ : ℝ≥0)
    (h_int : ∀ i r, Integrable (fun ω => ((X i ω).descFactorial r : ℝ)) (μ i))
    (h_lim : ∀ r, Tendsto (fun i => factorialMoment (X i) r (μ i)) atTop
                          (𝓝 ((λ : ℝ) ^ r))) :
    ∀ k, Tendsto (fun i => ((μ i) {ω | X i ω = k}).toReal) atTop
                 (𝓝 (Real.exp (−λ) * (λ : ℝ) ^ k / k.factorial)) := by
  sorry
```

**Corollary form** (`TendstoInDistribution`):

```lean
/-- Method of Factorial Moments, distributional form: under the same hypotheses,
the laws of `X_n` converge to the Poisson law. -/
theorem tendstoInDistribution_poissonMeasure_of_tendsto_factorialMoment
    -- (same hypotheses as above) :
    TendstoInDistribution (fun i => (X i : Ω i → ℕ)) atTop
      (μ := μ) (poissonMeasure λ) := by
  -- Apply portmanteau: pointwise PMF convergence on a discrete space ⟹
  -- convergence in distribution.
  sorry
```

---

## 4. Proof strategy for the primary theorem

The core proof is **inversion of the PMF–factorial-moment relation**. Two
classical routes; we recommend Route A.

### Route A — Direct inversion via Bonferroni / Newton

Key identity (Bollobás *Random Graphs* §I.3, Janson–Łuczak–Ruciński §6.1):

For an ℕ-valued RV `X` with finite factorial moments `m_r = E[X^{(r)}]`,
truncate at `R`:

```
ℙ(X = k) = ∑_{r=k}^{R} (−1)^{r−k} / (r−k)! · m_r / k!  +  ε_R
```

where `|ε_R| ≤ m_{R+1} / (R+1)! · (something explicit)`. Specifically, the
*Bonferroni inequalities* give an alternating-sign truncation error.

For our application: take `R → ∞` after `n → ∞`. The sum on the right converges
to `e^{−λ} λ^k / k!` (by the alternating exponential series), and `ε_R → 0`
uniformly in `n` provided some bounded-moment growth condition (Carleman's
condition, automatically satisfied for `m_r → λ^r`).

**Proof outline**:

1. **Inversion lemma** (purely combinatorial, no probability):
   For any `f : ℕ → ℝ` with `∑_k k^{(r)} · |f(k)| < ∞` for all `r`,
   ```
   f(k) = ∑_{r ≥ k} (−1)^{r−k} / (k! · (r−k)!) · ∑_j j^{(r)} · f(j).
   ```
   Reindex via `r = k + s`: `f(k) = (1/k!) · ∑_{s ≥ 0} (−λ)^s/s! · m_{k+s}`
   when `f` is the Poisson PMF and `m_r = λ^r`.

2. **Key identity** for ℕ-valued RV `X`:
   ```
   ℙ(X = k) = (1/k!) · ∑_{s ≥ 0} (−1)^s / s! · m_{k+s}.
   ```
   Proof: rearrange `∑_{j ≥ 0} ℙ(X = j) · 1[j = k]` using
   ```
   1[j = k] = ∑_{s ≥ 0} (−1)^s / (k! · s!) · j^{(k+s)}   (Newton's binomial-like identity).
   ```
   The RHS is a finite sum for each `j` (truncates at `s = j − k`), and
   collapses to `1[j=k]` by the identity
   `∑_{s=0}^{j-k} (−1)^s · C(j-k, s) = [j = k]`.

3. **Truncation**: define `S_R(n) := (1/k!) · ∑_{s=0}^{R} (−1)^s / s! · m_{k+s}(n)`,
   so `ℙ(X_n = k) = S_R(n) + ε_{R,n}` with `|ε_{R,n}| ≤ m_{k+R+1}(n) / ((R+1)! · k!)`
   (Bonferroni — alternating series tail bound).

4. **Limit interchange**:
   - Fix `k`. For each fixed `R`, `S_R(n) → (1/k!) · ∑_{s=0}^{R} (−1)^s / s! · λ^{k+s}`
     as `n → ∞` (sum of `R+1` terms, each by hypothesis).
   - The truncation error is bounded by `λ^{k+R+1} / ((R+1)! · k!) + o(1)` by `m_{k+R+1}(n) → λ^{k+R+1}`.
   - Take `R → ∞`: both `S_R` and the bound converge to
     `(λ^k / k!) · ∑_{s ≥ 0} (−λ)^s / s! = e^{−λ} λ^k / k!`.
   - A standard double-limit / `Tendsto.diagonal_atTop` argument gives the result.

### Route B — Via probability generating functions

PGF approach: `G_X(s) := E[s^X] = ∑_k ℙ(X=k) s^k`. Factorial moments are
derivatives at `s = 1`: `m_r = G_X^{(r)}(1)`. Convergence of all factorial
moments to those of Poisson implies convergence of `G_X` on a complex disk
around 1 (by Carleman) ⟹ `G_X(s) → exp(λ(s−1))` ⟹ PMF convergence by
Cauchy's formula or by uniform convergence on a circle.

**Pros**: leverages existing complex-analysis Mathlib infrastructure
(`AnalyticOn`, `tsum_pow`, `cauchyIntegral`).
**Cons**: requires `MGFAnalytic` -style infrastructure for PGF (not in Mathlib);
overkill for the discrete case.

**Recommendation: Route A**, more elementary, fewer dependencies.

---

## 5. Required Mathlib API inventory

Status legend: ✅ in v4.26.0 / 🟡 in master (post-v4.26.0) / 🔴 missing.

### Already present (✅)

| Symbol | File |
|--------|------|
| `Nat.descFactorial` | `Mathlib.Data.Nat.Choose.Basic` |
| `Nat.descFactorial_eq_factorial_mul_choose` | `Mathlib.Data.Nat.Choose.Basic` |
| `Nat.factorial_descFactorial` (`= n!/(n-k)!`) | `Mathlib.Data.Nat.Choose.Basic` |
| `Nat.descFactorial_succ`, `descFactorial_zero`, `descFactorial_self` | `Mathlib.Data.Nat.Choose.Basic` |
| `Real.exp_eq_tsum`, `Real.exp_neg` | `Mathlib.Analysis.SpecialFunctions.Exp` |
| `tsum_mul_left`, `tsum_eq_sum`, `HasSum.tsum_eq` | `Mathlib.Topology.Algebra.InfiniteSum.*` |
| `poissonPMFReal`, `poissonPMFRealSum`, `poissonPMF`, `poissonMeasure` | `Mathlib.Probability.Distributions.Poisson` |
| `MeasureTheory.integral_tsum`, `Summable.tsum_eq` | `Mathlib.MeasureTheory.Integral.Bochner` |
| `IsProbabilityMeasure`, `Measure.toReal` | `Mathlib.MeasureTheory.Measure.Basic` |
| `TendstoInDistribution` | `Mathlib.MeasureTheory.Function.ConvergenceInDistribution` |
| `Filter.Tendsto.{add,sub,mul,pow,div}` | `Mathlib.Order.Filter.*` |

### Master only (🟡, post-v4.26.0)

| Symbol | File |
|--------|------|
| `tendsto_choose_mul_pow_of_tendsto_mul_atTop` (Yi Yuan PMF Poisson limit) | `Mathlib.Probability.Distributions.Poisson.PoissonLimitThm` |

We **do not** depend on the Yuan theorem; MoFM is an independent path.

### To be added (🔴, this PR)

| Symbol | Lines (est.) | Notes |
|--------|--------------|-------|
| `ProbabilityTheory.factorialMoment` (def) | 5 | Wrapper around `μ[X.descFactorial r]`. |
| `factorialMoment_zero`, `factorialMoment_one` | 10 | Boundary cases. |
| `factorialMoment_poissonMeasure : factorialMoment id r (poissonMeasure λ) = λ^r` | 25 | Direct computation, §3.2 above. |
| **Inversion lemma** (combinatorial): `Nat.indicator_descFactorial_alternating` | 30 | `1[j=k] = ∑_s (-1)^s / (k! s!) j^{(k+s)}`; routine alternating-sum identity. |
| **PMF–factorial-moment identity**: `pmf_eq_alternating_factorialMoment` | 40 | Sums the indicator identity against the PMF; uses `integral_tsum`. |
| **Bonferroni truncation bound**: `pmf_factorialMoment_truncation_bound` | 30 | Alternating-sum tail estimate. |
| **Main theorem**: `tendsto_pmf_of_tendsto_factorialMoment` | 60 | Double-limit argument (§4 Route A step 4). |
| **Distributional corollary**: `tendstoInDistribution_poissonMeasure_of_tendsto_factorialMoment` | 25 | Portmanteau on discrete `ℕ`. |

**Total**: ~225 lines in a single file `MethodOfFactorialMoments.lean`. The
combinatorial inversion lemma might naturally live in `Mathlib.Combinatorics`
or `Mathlib.Data.Nat.Choose` instead — to be decided in review.

---

## 6. Open design questions for upstream review

1. **Generality of the underlying space**: should the spec require all `Ω_n`
   to coincide (single probability space, varying RVs), or allow a sequence of
   probability spaces (the form above)? Mathlib CLT uses a single space. The
   single-space form is easier to state but more restrictive; a wrapper can
   produce the multi-space form if needed.

2. **Hypothesis on factorial moment growth**: the cleanest hypothesis is
   "`m_r(n) → λ^r` for every `r`". Some sources require additionally a
   uniform-in-n bound on `m_r(n)` (Carleman's condition). For Poisson this is
   automatic (factorial moments determine the distribution), but the proof
   above does require uniform integrability of the truncation tail. We
   propose to **derive** this from `m_r(n) → λ^r` rather than impose it.

3. **Coercion to ℝ vs ℝ≥0∞**: `factorialMoment` returns `ℝ`. For Mathlib
   consistency with `moment X p μ`, this is the right choice. Users who need
   `ℝ≥0∞`-valued versions can lift via `ENNReal.ofReal`.

4. **Naming**: `factorialMoment` matches `moment`/`centralMoment` precedent.
   Alternatives: `descFactorialMoment`, `Nat.factorialMoment`. Prefer the short
   name in `ProbabilityTheory` namespace, matching `moment`.

5. **Should this go in a new file or in `Poisson/PoissonLimitThm.lean`?**
   New file. The MoFM theorem is independent of the binomial/PMF route; it is
   a general tool that applies to any sequence of counting RVs with bounded
   factorial moments. The naming convention `Mathlib/Probability/Distributions/Poisson/MethodOfFactorialMoments.lean`
   keeps it discoverable next to the other Poisson-limit results.

6. **Should the `factorialMoment` definition go in `Mathlib.Probability.Moments.Basic`
   instead of in this file?** Probably yes — keeps moments together. The MoFM
   theorem then imports both.

---

## 7. Cost / benefit summary

**Cost** (gallery-side):
- One-off contributor effort: ~225 lines + 1–3 month review cycle.
- Once landed and pinned, our entry's Layer 4 collapses to a one-line `apply`.

**Benefit** (gallery + upstream):
- Discharges Lemma C cleanly via Layer 4 in the birthday entry (Path C
  recommendation).
- Reusable: any random-graph subgraph count, balls-into-bins occupancy,
  hash-collision count, Erdős–Rényi triangle count problem can use this.
  Galaxy of formalization targets (e.g., the gallery's matching-number /
  component-count entries).
- Aligns with Mathlib's ongoing probabilistic project (CLT, BorelCantelli,
  PoissonLimitThm). Fills a gap that has stood since the 2022 moment work.
- Independent of v4.26.0 → master pin advances; can be drafted **now**, merged
  upstream **independently**, and reused **whenever** our pin advances.

---

## 8. Action plan

1. **(Now)** Spec finalized in this document. No upstream PR yet.
2. **(S11–S15)** Continue local Layers 1–3 in the gallery (per roadmap). These
   are independent.
3. **(S16 or earlier, parallelizable)** Open a Mathlib draft PR with:
   - The `factorialMoment` definition added to `Mathlib.Probability.Moments.Basic`.
   - The new file `Mathlib.Probability.Distributions.Poisson.MethodOfFactorialMoments`.
   - The Poisson factorial moment identity + the main theorem + the
     distributional corollary.
4. **(S17)** Once upstream lands, advance the gallery's pin (separate PR).
   Replace the local Layer 4 axiom with the imported theorem.

If Mathlib review stalls beyond the gallery's typical timeline, fall back to
**Path A** (local proof, all four layers). The local Layer 4 proof is the
same content as this spec, just placed in the gallery's own Lean file with no
upstream impact.

---

## 9. References

Same as `lemma-c-roadmap.md` §9, plus:

- Mathlib v4.26.0, `Mathlib/Probability/Moments/Basic.lean` (Rémy Degenne, 2022;
  `moment X p μ`, `centralMoment`, `mgf`, `cgf` precedent).
- Mathlib master, `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`
  (`TendstoInDistribution`).
- Mathlib master, `Mathlib/Probability/CentralLimitTheorem.lean`
  (`tendstoInDistribution_inv_sqrt_mul_sum`, naming/style precedent).
- Bollobás (2001), *Random Graphs* (2nd ed.), §I.3, Theorem 1.20.
- Janson, Łuczak, Ruciński (2000), *Random Graphs*, §6.1, Theorem 6.10.
- Diaconis, Holmes (2002), *A Bayesian peek into Feller volume I*, Sankhya 64,
  §3 (concise modern restatement of MoFM).
