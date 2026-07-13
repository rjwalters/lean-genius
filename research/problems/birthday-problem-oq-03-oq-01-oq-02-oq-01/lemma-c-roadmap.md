# Lemma C Roadmap: Method of Factorial Moments

**Author**: researcher-6, Session 9 (2026-05-08)
**Slug**: birthday-problem-oq-03-oq-01-oq-02-oq-01
**Target**: discharge `axiom p_no_triple_tendsto` in `Proofs/BirthdayProblemOQ03OQ01OQ02.lean:329`

This document maps the path from the current state (Sessions 1–8, axiom open) to a
proof of Lemma C, distinguishing the **Mathlib 4.26 inventory** (gallery's pin) from
the **Mathlib master inventory** (post-pin additions that may be reachable by a
future pin bump).

---

## 1. The Axiom

```lean
axiom p_no_triple_tendsto (c : ℝ) (hc : 0 < c) :
    let n : ℕ → ℕ := fun d => ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
    Filter.Tendsto
      (fun d : ℕ =>
        (Finset.univ.filter (fun f : Fin (n d) → Fin d =>
          ∀ i j k : Fin (n d), i ≠ j → j ≠ k → i ≠ k →
            ¬(f i = f j ∧ f j = f k))).card /
        (Fintype.card (Fin (n d) → Fin d) : ℝ))
      Filter.atTop (nhds (Real.exp (-(c ^ 3 / 6))))
```

In words: with `n_c(d) := ⌊c · d^{2/3}⌋`, the probability that a uniformly random
function `f : Fin n_c(d) → Fin d` has **no** birthday triple converges to
`exp(-c³/6)` as `d → ∞`.

The asymptotic limit `c³/6 = lim (n choose 3) / d²` is established by Lemma A
(`lambda_tendsto`, proved in Session 4). The axiom is the genuine probabilistic
statement: **convergence of the dependent sum of indicator variables to a
Poisson limit**.

---

## 2. Why Direct Binomial→Poisson Doesn't Apply

A natural first thought: invoke a Mathlib binomial-to-Poisson limit theorem. On
master Mathlib has

```lean
-- Mathlib/Probability/Distributions/Poisson/PoissonLimitThm.lean (post-v4.26.0)
theorem ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k * (1 - p n) ^ (n - k))
      atTop (𝓝 (Real.exp (-r) * (r ^ k) / k.factorial))
```

This **does not directly apply** to Lemma C because:

1. The triple-coincidence indicators `B_{ijk} := 𝟙{f(i)=f(j)=f(k)}` are **not
   independent** — pairs of triples sharing one or two indices are positively
   correlated. The binomial `(p)^k · (1-p)^{n-k}` formula presumes
   independence.
2. The total triple count is `C(n,3) = n!/(3!(n-3)!)`, not the `n` of the binomial
   theorem. The "trial count" in our setting is `C(n,3)` and the "success
   probability" per trial is `1/d²`.
3. The product `(1 − 1/d²)^{C(n,3)}` would equal P(no triple) **only** under
   independence; the actual probability is strictly larger by positive
   correlation, with correction terms of order `n⁴/d³ = O(d^{-1/3}) → 0`.

So the binomial→Poisson lemma is structurally the right shape but not directly
applicable. The genuine Lemma C requires **convergence of the dependent indicator
sum** to Poisson, equivalently:

> `P(X_d = 0) → e^{-λ}` where `X_d := Σ_{i<j<k} 𝟙{f(i)=f(j)=f(k)}` and
> `λ := lim (n choose 3)/d² = c³/6`.

---

## 3. Mathlib 4.26 Inventory (Gallery's Pin, `v4.26.0`)

### Available (relevant building blocks)

- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow` API
- `Mathlib.Analysis.SpecialFunctions.Choose` — `Nat.choose` asymptotics
- `Mathlib.Analysis.SpecificLimits.Normed` — `Real.tendsto_one_add_pow_exp_of_tendsto`
  (this is the underlying analytic lemma `(1 + x_n/n)^n → exp x` for `x_n → x`)
- `Mathlib.Probability.Distributions.Poisson` — `poissonPMFReal`, `poissonPMF`,
  `poissonMeasure` (PMF/measure **constructors only**)
- `Mathlib.Probability.IdentDistrib` and `Mathlib.Probability.Independence.*` —
  for sums of independent indicators (does not cover dependent case)
- `Mathlib.Probability.BorelCantelli` — second Borel–Cantelli
- `Mathlib.Probability.Moments.Basic` — `mgf` (moment generating function),
  variance lemmas

### Missing (for any path to Lemma C)

- **(M1)** Convergence in distribution of integer-valued RVs from convergence
  of factorial moments (`E[X^{(r)}] → λ^r` for all `r` ⇒ `X →d Poisson(λ)`).
  Not in Mathlib 4.26.
- **(M2)** Method of moments / factorial-moment expansion:
  `E[X^{(r)}] = Σ_{distinct r-tuples T of triples} P(all in T coincident)`.
  Not in Mathlib 4.26.
- **(M3)** Stein–Chen total variation bound for sums of dependent indicators.
  Not in Mathlib 4.26 in any form.
- **(M4)** General Bonferroni inequalities for inclusion–exclusion truncation
  (truncated at order `r` gives upper/lower bound depending on parity of `r`).
  Not in Mathlib 4.26 in the general dependent form.
- **(M5)** Direct binomial-to-Poisson `tendsto_choose_mul_pow_of_tendsto_mul_atTop`.
  Available on master, **not in v4.26.0**.

### Already proved in this entry (Sessions 1–8, on `main` or in open PRs)

- `lambda_tendsto` (Lemma A, S4): `λ_c(d) → c³/6`.
- `exp_lambda_tendsto` (Lemma B, S4): `exp(−λ_c(d)) → exp(−c³/6)`.
- `bad_count_n3` (S1): `card{f : Fin 3 → Fin d | f 0 = f 1 ∧ f 1 = f 2} = d`.
- `bad_count_n4_canonical` (S8, PR #16873): `card{... n=4, triple (0,1,2)} = d²`.
- `p_no_triple_n3` (S6): `P(no triple | n=3) = 1 − 1/d²`.
- `p_triple_n3` (S7): `P(triple | n=3) = 1/d²`.
- `p_triple_n3_eq_expectedTriples` (S7): `n=3` first-moment identity.

The first-moment work (Lemmas A/B + Sessions 6/7/8) gives the **mean** of `X_d`
correctly. Lemma C requires the **distribution**, not just the mean.

---

## 4. The Method-of-Factorial-Moments Approach

Define the falling-factorial moment

> `E[X_d^{(r)}] := E[X_d (X_d − 1) ⋯ (X_d − r + 1)]`.

For a Poisson(λ) random variable, `E[X^{(r)}] = λ^r` for all `r`. The Method of
Factorial Moments (MoFM) theorem says: if `X_d` are integer-valued ≥ 0 RVs and
`E[X_d^{(r)}] → λ^r` for every `r ≥ 0`, then `X_d →d Poisson(λ)`. In particular
`P(X_d = 0) → P(Poisson(λ) = 0) = e^{−λ}`.

### 4a. Combinatorial expansion

The factorial moments admit a clean combinatorial expansion. Let `T = {(i,j,k) :
i < j < k ≤ n}` be the index set of triples. Then

> `X_d^{(r)} = Σ_{(t₁,…,t_r) ∈ T^r distinct} 𝟙{B_{t₁} = ⋯ = B_{t_r} = 1}`.

Taking expectations, with `p(t₁,…,t_r) := P(B_{t₁} = ⋯ = B_{t_r} = 1)`:

> `E[X_d^{(r)}] = Σ_{ordered r-tuples of distinct triples} p(t₁,…,t_r)`.

The probability `p(t₁,…,t_r)` depends only on the **fusion pattern** of the
indices in `t₁ ∪ ⋯ ∪ t_r`: if the union has `m` distinct indices grouped into
`q` equivalence classes (induced by the constraints `f(a)=f(b)` from each
`B_{t_ℓ}=1`), then `p(t₁,…,t_r) = d^q / d^m = d^{q−m}`.

### 4b. Counting by fusion pattern

For an ordered `r`-tuple of distinct triples `(t₁, …, t_r)` from `T`, write
`m = |t₁ ∪ ⋯ ∪ t_r|` for the number of distinct indices in the union, and `q`
for the number of connected components in the auxiliary "triple-overlap" graph
(triples are vertices; two triples sharing ≥ 1 index are connected). Then:

- **Per-tuple probability** (given the `m, q` of the pattern):
  `p(t₁,…,t_r) = d^{q − m}` (each connected component forces its `m_c` indices
  to a single common value, contributing `d^{1 − m_c}`; product over components).
- **Count of ordered `r`-tuples in the pattern**: `O(n^m)` (the `m` distinct
  indices are chosen from `[n]`, with constants depending only on the
  combinatorial pattern).
- **Total contribution** of the pattern to the `r`-th factorial moment:
  `O(n^m / d^{m − q})`.

With `n = n_c(d) ~ c · d^{2/3}`, the contribution scales as

> `n^m / d^{m − q} ~ d^{2m/3} · d^{q − m} = d^{q − m/3}`.

The exponent `q − m/3` controls whether the pattern survives in the limit.

### 4c. The disjoint pattern dominates; non-disjoint patterns vanish

| Pattern | `m` | `q` | exponent `q − m/3` | scaling |
|---------|-----|-----|--------------------|---------|
| Disjoint (`r` triples, no shared indices) | `3r` | `r` | `0` | `Θ(1)` |
| Worst non-disjoint (single index shared by 2 triples; remaining `r−2` triples disjoint) | `3r − 1` | `r − 1` | `−2/3` | `Θ(d^{−2/3})` |
| Two indices shared by 2 triples | `3r − 2` | `r − 1` | `−1/3` | `Θ(d^{−1/3})` |
| Any pattern with ≥ 1 shared index | `< 3r` | `≤ r − 1` | `< 0` | `o(1)` |

**Disjoint contribution**:
`(count) · (probability) = C(n,3r) · (3r)! / 6^r · 1/d^{2r} ~ n^{3r}/(6^r · d^{2r})`
`= (n³/(6d²))^r → (c³/6)^r = λ^r`.

The count `(3r)! · C(n, 3r) / 6^r` is the number of ordered `r`-tuples of pairwise
disjoint triples in `[n]`: choose `3r` distinct indices, partition into `r`
ordered triples (with internal ordering by `<`).

**Non-disjoint contributions vanish**: any pattern where two triples share ≥ 1
index satisfies `q ≤ r − 1` (those two triples are in the same connected
component of the overlap graph). Combined with `m ≤ 3r − s_total` where
`s_total ≥ 1`, the exponent `q − m/3` is at most `(r − 1) − (3r − 1)/3 = −2/3 < 0`,
i.e. the contribution is `O(d^{−2/3}) → 0`.

**Pair calculation explicit (`r = 2`)**, useful as a Lean test case:

| Overlap `s` | Count of ordered pairs | Per-pair prob | Total |
|-------------|------------------------|---------------|-------|
| 0 (disjoint) | `C(n,3) · C(n−3,3) ~ n^6/36` | `1/d^4` | `~ n^6/(36 d^4) → c^6/36 = λ^2` |
| 1 (one shared index) | `n · C(n−1,2) · C(n−3,2) ~ n^5/4` | `1/d^4` | `~ n^5/(4 d^4) = c^5/(4 d^{2/3}) → 0` |
| 2 (two shared, "edge in common") | `C(n,2) · (n−2)(n−3) ~ n^4/2` | `1/d^3` | `~ n^4/(2 d^3) = c^4/(2 d^{1/3}) → 0` |

The arithmetic for `r ≥ 3` follows the same rule: enumerate fusion patterns by
the connected components of the overlap graph; the disjoint pattern gives
`λ^r`; every other pattern gives `O(d^{−2/3})`.

### 4d. Convergence of factorial moments to Poisson values

Combining: for each fixed `r ≥ 0`, `E[X_d^{(r)}] → λ^r = (c³/6)^r` as `d → ∞`.
This is the **factorial moment convergence**. By the Method of Factorial Moments,
this gives `X_d →d Poisson(λ)`, hence `P(X_d = 0) → e^{−λ} = e^{−c³/6}`.

---

## 5. Lean Sub-Lemma Decomposition

The proof of Lemma C decomposes into four layers:

### Layer 1 — Indicator algebra (no probability infrastructure needed)

```lean
/-- The triple-coincidence count as an explicit sum of indicators.
    For uniformly random `f : Fin n → Fin d`, the count of triples
    `(i,j,k)` with `i < j < k` and `f i = f j = f k` is
    a Finset.sum over the strictly-increasing triples in Fin n. -/
def tripleCount (d n : ℕ) (f : Fin n → Fin d) : ℕ :=
  (Finset.univ.filter (fun t : Fin n × Fin n × Fin n =>
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ f t.1 = f t.2.1 ∧ f t.2.1 = f t.2.2)).card

/-- `X_d = 0 ↔ no triple` —  the connection to `p_no_triple_tendsto`. -/
lemma tripleCount_eq_zero_iff_no_triple (d n : ℕ) (f : Fin n → Fin d) :
    tripleCount d n f = 0 ↔
      ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k → ¬(f i = f j ∧ f j = f k) := …
```

**Estimated size**: ≈ 30–50 lines. Pure combinatorics, all primitives in Mathlib 4.26.

### Layer 2 — First moment (already done, S7)

`p_triple_n3_eq_expectedTriples` covers `n = 3` in PR #16777 (Session 7).
General `n` form (Markov bound) is the natural next step:

```lean
/-- General-n first moment: E[X_d] = C(n,3) / d². -/
lemma expectedTripleCount_eq (d n : ℕ) (hd : 0 < d) :
    (∑ f : Fin n → Fin d, (tripleCount d n f : ℝ)) /
      (Fintype.card (Fin n → Fin d) : ℝ) =
    (n.choose 3 : ℝ) / (d : ℝ) ^ 2 := …
```

**Estimated size**: ≈ 80 lines, mostly Finset / Fintype rearrangement plus the
per-triple count `C(n,3) · d^{n−2} / d^n = C(n,3)/d²` (Lemma D in the gallery's
state.md "Next Action #1").

### Layer 3 — Higher factorial moments (the genuine new content)

```lean
/-- Per-triple count: with i,j,k distinct, the number of f with f i = f j = f k
    is exactly d^(n−2). The general form of `bad_count_n3` and `bad_count_n4_canonical`. -/
lemma bad_count_general (d n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f i = f j ∧ f j = f k)).card = d ^ (n - 2) := …

/-- Falling-factorial moment expansion. -/
lemma factorial_moment_eq_sum (d n r : ℕ) :
    (∑ f : Fin n → Fin d, ((tripleCount d n f).descFactorial r : ℝ)) /
      (Fintype.card (Fin n → Fin d) : ℝ) =
    ∑ T in (orderedTuples r (triplesIn n)),
      (P_jointCoincidence d T : ℝ) := …

/-- Disjoint contribution to factorial moment converges to λ^r. -/
lemma disjoint_factorial_moment_tendsto (c : ℝ) (hc : 0 < c) (r : ℕ) :
    Filter.Tendsto
      (fun d : ℕ => disjoint_part d (n_c c d) r)
      Filter.atTop (nhds ((c ^ 3 / 6) ^ r)) := …

/-- Non-disjoint terms vanish as d → ∞. -/
lemma nondisjoint_factorial_moment_tendsto_zero (c : ℝ) (hc : 0 < c) (r : ℕ) :
    Filter.Tendsto
      (fun d : ℕ => nondisjoint_part d (n_c c d) r)
      Filter.atTop (nhds 0) := …
```

**Estimated size**: ≈ 250–400 lines. The `bad_count_general` is in state.md as
Next Action #1; the disjoint/nondisjoint split is the core combinatorial work
(fusion-pattern bookkeeping). This layer is **the bottleneck** and admits no
direct Mathlib shortcut at v4.26.0.

### Layer 4 — Method of Factorial Moments (theorem)

```lean
/-- The Method of Factorial Moments, qualitative form: convergence of all
    factorial moments to Poisson values implies convergence in distribution
    (in particular convergence of `P(X_d = 0)` to `e^{-λ}`).

    NOT in Mathlib 4.26. The simplest form needs:
    - the fact that the Poisson generating function `Σ_r λ^r z^r / r!` is
      the unique probability-generating function with these factorial moments;
    - dominated-convergence to commute the sum and limit. -/
lemma method_of_factorial_moments
    {X : ℕ → ℕ → ℝ} (hX_nonneg : ∀ d k, 0 ≤ X d k) (hX_prob : ∀ d, ∑' k, X d k = 1)
    (λ : ℝ) (hλ : 0 ≤ λ)
    (hMoments : ∀ r, Filter.Tendsto
      (fun d => ∑' k, (k.descFactorial r : ℝ) * X d k)
      Filter.atTop (nhds (λ ^ r))) :
    Filter.Tendsto (fun d => X d 0) Filter.atTop (nhds (Real.exp (-λ))) := …
```

**Estimated size**: ≈ 150–250 lines. Requires the algebraic identity
`Σ_r (-1)^r λ^r/r! = e^{-λ}` (Mathlib has `Real.exp_neg_eq_sum`), uniform
absolute convergence, and a Tonelli-style swap. This is essentially a clean
analysis lemma with no probability-specific dependencies once `descFactorial`
arithmetic is in place. **Strong candidate for Mathlib upstream contribution**:
the lemma is generally useful (Erdős–Rényi limits, hash-collision analysis,
random-graph triangle counting, etc.).

---

## 6. Recommended Path Forward

### Path A — Local proof, Mathlib 4.26 only (≈ 600 lines new code)

1. **Layer 1** (indicator algebra): ≈ 30–50 lines. Foundational, no risk.
2. **Layer 2** (first moment): ≈ 80 lines. State.md Next Action #1 (general-n
   per-triple count). PRs #16873/#16837 are partial steps; full version still
   needed.
3. **Layer 3** (factorial moments): ≈ 250–400 lines. The genuine combinatorial
   bottleneck. Sub-decomposition into disjoint vs. non-disjoint contributions
   needs careful fusion-pattern bookkeeping (Section 4c above is a sketch; the
   Lean form will require an explicit `Finset.sum_partition` over fusion
   patterns).
4. **Layer 4** (MoFM theorem): ≈ 150–250 lines. Pure analysis; Mathlib upstream candidate.

Total: ≈ 600 lines of new Lean. Risk: Layer 3 has subtle index bookkeeping (the
"one shared index" arithmetic in §4c had to be corrected once during this
roadmap); careful Lean formalization will catch off-by-ones the informal
calculation may have.

### Path B — Mathlib pin upgrade + reduced local work (≈ 250 lines)

If a future researcher upgrades the gallery's Mathlib pin from `v4.26.0` to a
post-2026-03-08 version, the master `Mathlib.Probability.Distributions.Poisson.PoissonLimitThm`
is available. While `tendsto_choose_mul_pow_of_tendsto_mul_atTop` itself does
**not** discharge Lemma C (independence-required, see §2), the underlying
analytic tooling (`Real.tendsto_one_add_pow_exp_of_tendsto`, `IsEquivalent.choose`,
asymptotics tactics) and the existence of a Poisson-limit-friendly idiom in
Mathlib reduces the boilerplate for Layer 4 by ≈ 100 lines.

Estimated savings: 150 lines (Layer 4 becomes ≈ 100 lines). Layer 3 (the
combinatorial bottleneck) is unaffected.

### Path C — Mathlib upstream contribution (recommended for Layer 4)

The Method of Factorial Moments is a textbook lemma (e.g., Bollobás §I.3,
Janson–Łuczak–Ruciński §6.1) used widely in random combinatorics. Its absence
from Mathlib is a real gap. Contributing the lemma upstream:

1. **Pros**: Generally useful (Erdős–Rényi triangle counts, random-graph
   subgraph counts, hash collisions); well-defined statement; no project-specific
   dependencies; future-proofs the gallery against pin churn.
2. **Cons**: 1–3 month review cycle; requires Lean style polish; needs to be
   stated in the right generality (probably for general integer-valued non-negative
   RVs, not just our `tripleCount`).
3. **Skeleton location in Mathlib**: `Mathlib/Probability/MomentsConvergence.lean`
   (new file) or `Mathlib/Probability/Distributions/Poisson/MethodOfMoments.lean`.

If Path C succeeds, Path A's Layer 4 becomes a single `apply` line, reducing
this entry's local code to Layers 1+2+3 ≈ 360 lines.

### Path D — Stein–Chen quantitative bound (alternative)

Stein–Chen gives a **quantitative** total variation bound `|P − Poisson| ≤ b₁ + b₂`
where `b₁, b₂` are pair-correlation sums. For our problem `b₁ = O(n⁴/d³) = O(d^{−1/3})`
and `b₂ = O(n³/d²) = 0` (positive correlation only, no negative). The bound is
**stronger** than Lemma C (it gives a rate, not just convergence) but requires
**substantially more** Mathlib infrastructure: Stein equation, Stein operator,
total variation distance for measures on ℕ. The infrastructure is ~ 800–1200
lines and is a known target for Mathlib (no PR yet as of 2026-05-08). Not
recommended for this entry — overkill for the qualitative limit.

### Recommendation

**Path C + Path A residual**: contribute Layer 4 (Method of Factorial Moments)
upstream to Mathlib; in parallel, build Layers 1–3 locally in this entry. The
upstream PR can be drafted concurrently with the local Layer 3 work; once the
upstream lands and the gallery's pin advances, the local Layer 4 becomes a
single application of the upstream lemma.

If upstream contribution is not feasible in the current researcher cycle,
**Path A** (local proof, all four layers) is the only fully-rigorous fallback at
the gallery's current pin. Layer 3 should be the priority for the next 2–3
sessions; it is the only layer with combinatorial content specific to this
problem.

---

## 7. Layer-by-Layer Session Sequence

A concrete multi-session plan after this roadmap (S9):

- **S10**: Layer 1 (indicator algebra). `tripleCount` definition + the
  `tripleCount_eq_zero_iff_no_triple` connection. ≈ 50 lines, ≤ 1 session.
- **S11**: Layer 2 part 1 (`bad_count_general`). State.md Next Action #1 in
  full generality. ≈ 80 lines.
- **S12**: Layer 2 part 2 (`expectedTripleCount_eq`). Markov bound for general
  n; the global form of S7's n = 3 identity. ≈ 80 lines.
- **S13–15**: Layer 3 (factorial moments — the bottleneck). Decompose by
  fusion pattern; prove disjoint contribution converges to `λ^r`; prove
  non-disjoint contributions vanish. ≈ 300 lines, 3 sessions.
- **S16–17**: Layer 4 (MoFM theorem). Either local (≈ 200 lines) or apply
  upstream Mathlib contribution. ≈ 1–2 sessions.

Total: 7–9 sessions to discharge the axiom locally. Compares favorably with
the current 7-session investment that established the framework + first
moment but did not yet attack the Poisson limit itself.

---

## 8. Risks and Mitigation

| Risk | Mitigation |
|------|------------|
| Fusion-pattern bookkeeping in Layer 3 has off-by-one errors | Pre-compute small cases (r=1,2,3) by hand; cross-check Lean lemmas against the manual calculation. |
| Mathlib pin upgrade breaks unrelated entries | Coordinate with the gallery's mechanic / build infrastructure; fall back to Path A. |
| Upstream Mathlib contribution stalls in review | Path A is independent; the local proof can land before the upstream PR. |
| Build pressure (32 GB cgroup limit kills builds) | Layer 1+2 are short and self-contained; verify each layer in isolation; rely on warm Mathlib cache. |
| Multiple agents racing on the same file | Use unique branch names (e.g. `research/birthday-lemma-c-layer-N-sM`); coordinate via PR labels. |

---

## 8a. Layer 3 Sub-Decomposition (S13 Survey)

**Author**: researcher-6, Session 13 (2026-05-08)

After Layer 2 closed at S12 (PRs #16986/#17074/#17120), Layer 3 is the
genuine combinatorial bottleneck. To make S14+ implementation tractable
in single-session chunks, this section decomposes Layer 3 (≈ 250–400
lines per §6) into seven independent sub-pieces with explicit signatures,
expected line counts, and dependency edges.

### 8a.1 Dependency graph

```
3a (descFactorial_two def)  ──┐
3b (tripleCount_descFact_2)  ─┼─→  3d (factorial_moment_2 = sum)
3c (overlap-pattern bijection)┘                              │
                                                              ↓
                                                3e (disjoint contribution)
                                                3f (non-disjoint contribution)
                                                              │
                                                              ↓
                                              3g (factorial_moment_2 → c³/6 · c³/6)

Generalisation r ≥ 3 forms Layer 3', deferred until r = 2 closes.
```

### 8a.2 Sub-lemmas

#### Layer 3a — `descFactorial_two` algebra (≈ 30 lines, S14)

Auxiliary identities for the falling factorial at r = 2:

```lean
/-- `n.descFactorial 2 = n * (n - 1)` (Mathlib `Nat.descFactorial_two`,
    no work; cite). -/

/-- `(n.descFactorial 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1)` for n : ℕ.
    Push-cast version; needed because the gallery sums over ℝ. -/
lemma descFactorial_two_real_eq (n : ℕ) :
    (n.descFactorial 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  rw [Nat.descFactorial_two]; push_cast; ring
```

No fusion-pattern reasoning yet; pure cast/algebra. Independent of any
other sub-lemma. **Estimated**: 30 lines including 1 import.

#### Layer 3b — `tripleCount_descFact_2_eq_pairs` (≈ 50 lines, S14)

Combinatorial identity expanding `tripleCount d n f * (tripleCount d n f - 1)`
to a sum over **ordered pairs** of strict triples (with the diagonal removed):

```lean
/-- For each f, `tripleCount.descFactorial 2` equals the count of ordered
    pairs of strict triples (T₁, T₂) with T₁ ≠ T₂ such that f trivialises
    both T₁ and T₂. -/
lemma tripleCount_descFact_2_eq_pairs (d n : ℕ) (f : Fin n → Fin d) :
    (tripleCount d n f).descFactorial 2 =
    ((strictTriples n) ×ˢ (strictTriples n)).card.filter
      (fun p => p.1 ≠ p.2 ∧
        f (p.1).1 = f (p.1).2.1 ∧ f (p.1).2.1 = f (p.1).2.2 ∧
        f (p.2).1 = f (p.2).2.1 ∧ f (p.2).2.1 = f (p.2).2.2)
```

Proof: standard `Finset.card_descFactorial_eq_card_pairs` with the diagonal
removed via `(strictTriples n).filter (fun T => f trivialises T)` setup.
Reuses `tripleCount` from S10 and `card_strict_triples` from S12.

**Risk**: signature requires care with the diagonal-removal — `descFactorial 2`
counts ordered pairs of distinct elements, not all ordered pairs. **Estimated**:
50 lines.

#### Layer 3c — overlap-pattern partition (≈ 60 lines, S15)

Partition the diagonal-removed pair-of-triples space by the size of the
intersection `T₁ ∩ T₂`:

```lean
/-- Five overlap-pattern Finsets partitioning ordered pairs of distinct
    strict triples by intersection size. -/
def overlapPattern (n : ℕ) : Fin 4 → Finset ((Fin n)³ × (Fin n)³)
  | 0 => -- |T₁ ∩ T₂| = 0  (disjoint, requires n ≥ 6)
  | 1 => -- |T₁ ∩ T₂| = 1
  | 2 => -- |T₁ ∩ T₂| = 2
  | 3 => -- |T₁ ∩ T₂| = 3 (T₁ = T₂ as sets but ordered differently)

lemma overlapPattern_partitions (n : ℕ) :
    ((strictTriples n) ×ˢ (strictTriples n)).filter (· ≠ ·) =
    Finset.disjUnion (Finset.range 4) (overlapPattern n) ⟨…⟩
```

**Note**: the |T₁ ∩ T₂| = 3 case (same set, different ordering) reduces to
the diagonal — but our pair filter already excludes T₁ = T₂. Since strict
triples are *ordered* increasing tuples, T₁ ≠ T₂ as ordered tuples already
forces them to be set-distinct (the canonical ordering is unique). So
overlap-3 contributes 0 elements. The genuine partition is over
{0, 1, 2}.

**Estimated**: 60 lines (mostly the `disjUnion` bookkeeping and the
overlap-3-impossible argument).

#### Layer 3d — `factorial_moment_2_eq_sum_overlapPattern` (≈ 40 lines, S15)

Combine 3a + 3b + 3c:

```lean
lemma factorial_moment_2_eq_sum_overlapPattern (d n : ℕ) (hd : 1 ≤ d) :
    (∑ f, ((tripleCount d n f).descFactorial 2 : ℝ)) /
      Fintype.card (Fin n → Fin d) =
    ∑ k ∈ Finset.range 3,
      (∑ p ∈ overlapPattern n k, P_jointCoincidence d p) /
      Fintype.card (Fin n → Fin d)
```

The outer-sum-over-f / inner-sum-over-pairs swap is `Finset.sum_comm`;
the partition-respecting split is `Finset.sum_disjUnion`. **Estimated**:
40 lines.

#### Layer 3e — disjoint contribution (≈ 70 lines, S16)

The k = 0 (disjoint pairs) overlap-pattern contributes `1/d⁴` per pair:

```lean
/-- For disjoint strict triples T₁, T₂ (|T₁ ∩ T₂| = 0), the joint
    coincidence count `f T₁ ∧ f T₂` is `d^(n-4)`, hence probability
    `1/d⁴` (independent of n once n ≥ 6). -/
lemma jointCoincidence_disjoint (d n : ℕ) (hn : 6 ≤ n) (T₁ T₂ : (Fin n)³)
    (hdisj : T₁.toFinset ∩ T₂.toFinset = ∅) :
    (Finset.univ.filter (fun f =>
      f T₁.1 = f T₁.2.1 ∧ … ∧ f T₂.1 = f T₂.2.1 ∧ …)).card = d^(n-4)
```

By independent bijection with `({m // m ∉ T₁.toFinset ∪ T₂.toFinset} → Fin d)`,
generalising `bad_count_general` from S11. After dividing by `d^n`, get
`1/d⁴`. **Estimated**: 70 lines (the bijection mirrors S11's structure).

#### Layer 3f — non-disjoint contributions (≈ 80 lines, S16)

Overlaps k = 1, 2 contribute strictly larger probabilities (`1/d³` and
`1/d²` respectively per pair) but the count of such pairs grows slower
than disjoint (`O(n^5)` vs `O(n^6)`):

```lean
/-- Non-disjoint contribution to factorial moment vanishes as d → ∞ when
    n = ⌊c·d^{2/3}⌋. -/
lemma nondisjoint_factorial_moment_2_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun d : ℕ =>
        let n := ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
        ((∑ k ∈ Finset.range 3 \ {0}, ∑ p ∈ overlapPattern n k,
            P_jointCoincidence d p) : ℝ) /
        Fintype.card (Fin n → Fin d))
      Filter.atTop (nhds 0)
```

The asymptotic rate is `O(d^{-2/3})` — see roadmap §4c: the overlap-1
contribution is `O(n^5/d⁵) = O(d^{10/3 - 5}) = O(d^{-5/3})`; the overlap-2
contribution is `O(n^4/d⁴) = O(d^{8/3 - 4}) = O(d^{-4/3})`. **Estimated**:
80 lines.

#### Layer 3g — factorial_moment_2 limit (≈ 30 lines, S17)

Combine 3d + 3e + 3f to conclude:

```lean
lemma factorial_moment_2_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun d : ℕ =>
        let n := ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
        (∑ f, ((tripleCount d n f).descFactorial 2 : ℝ)) /
        Fintype.card (Fin n → Fin d))
      Filter.atTop (nhds ((c ^ 3 / 6) ^ 2))
```

The disjoint-pair count is `C(n,3)·(C(n,3) - C(n,3)·O(1/n²))` (overlap
correction), which is `(c³/6 · d²)² · (1 + o(1))` after dividing by
`d^n / d^{n-4} = d⁴`. **Estimated**: 30 lines (mostly tendsto algebra).

### 8a.3 Total estimate vs roadmap §6

Roadmap §6 estimated Layer 3 at 250–400 lines. The sub-decomposition
above sums to:

| Sub-piece | Lines | Session |
|-----------|------:|---------|
| 3a descFactorial_two | 30 | S14 |
| 3b tripleCount_descFact_2 | 50 | S14 |
| 3c overlap-pattern partition | 60 | S15 |
| 3d factorial_moment_2 = sum | 40 | S15 |
| 3e disjoint contribution | 70 | S16 |
| 3f non-disjoint vanishing | 80 | S16 |
| 3g factorial_moment_2 limit | 30 | S17 |
| **Total (r = 2 only)** | **360** | **S14–S17** |

For general r ≥ 3, multiply by ≈ 2× (the algebraic structure repeats).
The roadmap's 250–400 estimate covers r = 2 only; full Layer 3 (all r)
requires either an additional ≈ 300 lines or a generic-r abstraction
that subsumes specific r values. The latter is the cleaner path but
substantially harder to write — leave as Layer 3' (post-Layer-3-r=2).

### 8a.4 Why r = 2 is the right S14 starting point

Per the Method of Factorial Moments (Layer 4):

> If `E[X·(X-1)·…·(X-r+1)] → λ^r` for all `r ≥ 0`, then `X →ᵈ Poisson(λ)`.

For Lemma C we need `P(X = 0) → e^{-λ}`. The MoFM theorem actually only
requires the factorial-moment convergence to hold; in practice the
quantitative bound `|P(X = 0) - e^{-λ}| ≤ Σ_{r ≥ 1} |E[X^{(r)}] - λ^r|/r!`
(Bonferroni-style) shows that the first few `r` values give explicit
error bounds. **r = 2 is the simplest non-trivial case** and the
template for r ≥ 3.

### 8a.5 What this session (S13) did NOT do

- No `.lean` edits. This is a SURVEY pass, mirroring S9's deliverable.
- No Docker build. Pure documentation.
- No `meta.json` update — the Lean file is unchanged.

### 8a.6 What S14 should verify first

Before starting 3a/3b, the S14 session should:

1. Confirm `Nat.descFactorial_two` (or `Nat.descFactorial 2`) is in
   Mathlib v4.26.0. (Likely yes; the gallery's pin includes core
   `Nat.Factorial` machinery.)
2. Confirm `Finset.card_descFactorial_eq_card_pairs` (or analogue) is
   in Mathlib. The naming is fluid — fall back to `Finset.card_filter`
   or hand-rolled bijection if the named lemma is absent.
3. Run `./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ03OQ01OQ02`
   to confirm Layer 2 (S10–S12) is currently building cleanly. Multiple
   recent PRs landed as "build pending" via deployer auto-merge; a
   build-status check is prudent before adding 80+ lines on top.

---

## 9. References

- Arratia, R., Goldstein, L., Gordon, L. (1989). *Two moments suffice for Poisson approximations: The Chen–Stein method.* Annals of Probability **17** (1): 9–25. (Chen–Stein survey, Path D background.)
- Bollobás, B. (2001). *Random Graphs* (2nd ed.). Cambridge University Press, §I.3 (Method of Factorial Moments, applied to random graph subgraph counts).
- Janson, S., Łuczak, T., Ruciński, A. (2000). *Random Graphs.* Wiley, §6.1 (Poisson convergence via factorial moments).
- Diaconis, P., Mosteller, F. (1989). *Methods for studying coincidences.* JASA **84** (408): 853–861.
- Mathlib master, `Mathlib/Probability/Distributions/Poisson/PoissonLimitThm.lean`
  (Yi Yuan, 2026-03-08; binomial→Poisson convergence, **post-v4.26.0**).
- Mathlib v4.26.0, `Mathlib/Probability/Distributions/Poisson.lean` (PMF /
  measure constructors only).
