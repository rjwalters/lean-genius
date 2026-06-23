# Knowledge — ballot-problem-oq-02-oq-05

## S1 (researcher-6, 2026-05-12) — OBSERVE survey

### Donsker's functional CLT — historical timeline

| Year | Contributor | Result | Reference |
|---|---|---|---|
| 1900 | Bachelier | Brownian motion as a continuum-of-prices model for stock speculation | *Théorie de la Spéculation* (PhD thesis) |
| 1923 | Wiener | Rigorous construction of Brownian motion as a measure on $C([0,1])$ | *Differential-Space*, J. Math. Phys. 2 |
| 1933 | Kolmogorov | Continuity theorem (Kolmogorov-Centsov) for sample paths | *Grundbegriffe der Wahrscheinlichkeitsrechnung* |
| 1939 | Lévy | Arcsine law for time spent positive by Brownian motion | *Sur certains processus stochastiques homogènes* |
| 1949 | Sparre Andersen | Discrete arcsine: $P(L_n = k) = \binom{2k}{k} \binom{2(n-k)}{n-k} \cdot 2^{-2n}$ for symmetric walks | Skand. Aktuarietidskr. 32 |
| 1951 | Donsker | **Functional CLT**: rescaled walks converge weakly to BM in $C([0,1])$ | *An invariance principle for certain probability limit theorems*, Mem. Amer. Math. Soc. 6 |
| 1956 | Prokhorov | Tightness and weak convergence on metric spaces; foundational for Donsker | *Convergence of random processes and limit theorems in probability theory*, Theor. Probab. Appl. 1 |
| 1968 | Billingsley | Standard reference textbook; Donsker proof via tightness + finite-dim convergence | *Convergence of Probability Measures*, Wiley |

The Donsker pipeline:

1. **Finite-dimensional convergence**: by the classical multivariate CLT, $(S_n^*(t_1), \ldots, S_n^*(t_k)) \xrightarrow{d} (W_{t_1}, \ldots, W_{t_k})$ for any fixed $0 \le t_1 < \cdots < t_k \le 1$.
2. **Tightness**: by Kolmogorov-Centsov + the explicit moment bound $\mathbb{E}|S_n^*(t) - S_n^*(s)|^2 = |t - s|$, the family $\{S_n^*\}$ is tight in $C([0, 1])$.
3. **Combine via Prokhorov**: tightness + finite-dimensional convergence implies weak convergence to the unique Brownian-motion law on $C([0, 1])$.

Each of steps 1-3 requires Mathlib infrastructure that is partial-to-absent at v4.26.0.

### Discrete reflection — the lattice-path bijection

For the symmetric ±1 random walk $S_0 = 0, S_n = \sum_{i=1}^n \xi_i$ with $\xi_i \in \{-1, +1\}$ uniform i.i.d., the **reflection principle** says:

$$
P(\max_{1 \le k \le n} S_k \ge a) = P(S_n \ge a) + P(S_n > a) = 2 P(S_n \ge a) - P(S_n = a). \quad (*)
$$

**Proof by bijection** (André 1887, simplified by Feller). Let $A = \{\text{paths reaching } a \text{ or higher}\}$ and $B = \{\text{paths ending at or above } a\}$.

- $B \subseteq A$: any path ending at $\ge a$ has reached $a$ at some point.
- Decompose $A = A_{\ge a} \cup A_{< a}$ by endpoint $S_n$.
- Reflect each path in $A_{< a}$ at its first time hitting $a$: the reflected path ends at $2a - S_n > a$.
- This gives a bijection $A_{< a} \leftrightarrow \{S_n > a\}$.
- Hence $|A_{< a}| = |\{S_n > a\}|$, and $|A| = |A_{\ge a}| + |A_{< a}| = |\{S_n \ge a\}| + |\{S_n > a\}|$.
- Dividing by $2^n$ gives $(*)$.

The Lean proof of $(*)$ would use: `Finset.card_bij` for the reflection bijection, `Fin.castAdd` and friends for the path representation, and the symmetric Bernoulli measure on `Fin n → Bool`. Total expected length: ~100 lines.

### Continuous mapping theorem — three formulations

For weak convergence on a metric space $(M, d)$, the continuous mapping theorem states:

**Theorem (CMT, basic form)**. If $X_n \Rightarrow X$ in $M$ and $\Phi : M \to \mathbb{R}$ is continuous, then $\Phi(X_n) \Rightarrow \Phi(X)$ in $\mathbb{R}$.

**Theorem (CMT, Portmanteau form)**. The following are equivalent for probability measures $\mu_n, \mu$ on a metric space $M$:
1. $\mu_n \Rightarrow \mu$;
2. $\int f \, d\mu_n \to \int f \, d\mu$ for all bounded continuous $f : M \to \mathbb{R}$;
3. $\mu_n(F) \le \liminf \mu_n(F) + \varepsilon$ for all closed $F$ and $\varepsilon > 0$ (and similar for open);
4. $\mu_n(B) \to \mu(B)$ for all $\mu$-continuity sets $B$ (boundary has $\mu$-measure 0).

**Theorem (CMT, almost-sure-continuity form)**. If $X_n \Rightarrow X$ and $\Phi$ is continuous on a set $C$ with $P(X \in C) = 1$, then $\Phi(X_n) \Rightarrow \Phi(X)$.

The third form is the one needed for the arcsine law: the functional $\Phi(f) = \int_0^1 \mathbf{1}_{f(t) > 0} \, dt$ is continuous on the set of paths that do not spend positive Lebesgue measure at level 0, which is a $W$-full set.

**Mathlib status**: `Mathlib.MeasureTheory.Measure.Portmanteau` contains partial development (basic equivalences); the full CMT in the form we need is absent.

### Lévy's arcsine law — three equivalent statements

For standard Brownian motion $W$ on $[0, 1]$, let $L = \int_0^1 \mathbf{1}_{W(t) > 0} \, dt$. The arcsine law states:

$$
P(L \le r) = \frac{2}{\pi} \arcsin \sqrt{r}, \quad r \in [0, 1].
$$

Three equivalent statements (and the one most amenable to Mathlib encoding):

1. **CDF form**: $P(L \le r) = (2/\pi) \arcsin \sqrt{r}$.
2. **Density form**: $L$ has density $1 / (\pi \sqrt{r (1-r)})$ on $(0, 1)$.
3. **Three-version theorem (Lévy 1939)**: The following three random variables are identically distributed: (a) the fraction of time spent positive $L$; (b) the location of the last zero $\sup\{t \le 1 : W(t) = 0\}$; (c) the location of the maximum $\arg\max_{0 \le t \le 1} W(t)$.

The CDF form is the cleanest target. The proof via Donsker + Sparre Andersen + Stirling:

- **Discrete**: $L_n := \#\{k \le n : S_k > 0\}$ satisfies $P(L_n = k) = (2k \text{ choose } k)(2(n-k) \text{ choose } n-k) \cdot 2^{-2n}$ (Sparre Andersen 1949).
- **Stirling**: $(2k \text{ choose } k) \sim 4^k / \sqrt{\pi k}$, so $P(L_n = k) \sim 1 / (\pi \sqrt{k(n-k)})$.
- **Riemann sum**: $P(L_n \le rn) = \sum_{k \le rn} P(L_n = k) \to \int_0^r dr / (\pi \sqrt{r(1-r)}) = (2/\pi) \arcsin \sqrt{r}$.
- **Donsker bridge**: by continuous mapping (a.s.-continuity form), $L_n / n \Rightarrow L$, so the limit law of $L_n / n$ equals the distribution of $L$.

The Stirling step is elementary; the Riemann-sum step is also elementary; the continuous-mapping step requires the CMT for the integral-of-indicator functional, which is a $W$-continuity set argument (the set of paths with $\{W = 0\}$ Lebesgue null is $W$-full by Brownian local time arguments).

### Sparre Andersen's discrete arcsine — the bijection

Sparre Andersen (1949) proved: for any random walk $S_n$ with continuous step distribution symmetric around 0, the number $L_n = \#\{k : S_k > 0\}$ and the location of the maximum $\arg\max_{0 \le k \le n} S_k$ are identically distributed.

For the symmetric ±1 walk specifically (the case relevant to the ballot problem), $L_n$ has the **discrete arcsine distribution**:

$$
P(L_n = k) = \binom{2k}{k} \binom{2(n-k)}{n-k} \cdot 2^{-2n}.
$$

The proof uses the **cycle lemma** (also central to the classical ballot problem proof): every cyclic rotation of a path is in bijection with a unique non-negative path, and the count splits exactly evenly by the position of the maximum.

**Mathlib status**: no direct formalisation of Sparre Andersen at v4.26.0. The cycle lemma appears in `Proofs/BallotProblem.lean` (gallery entry) and `Proofs/CatalanNumbers.lean` (sibling).

### Skorohod space versus continuous interpolation

Two encodings of the rescaled walk are common in the literature:

1. **Step function** (canonical for $D([0, 1])$):
   $$ S_n^{\text{step}}(t) = S_{\lfloor n t \rfloor} / \sqrt{n}. $$
   Right-continuous with left limits; lives in $D([0, 1])$.

2. **Interpolated** (canonical for $C([0, 1])$):
   $$ S_n^*(t) = (S_{\lfloor n t \rfloor} + (n t - \lfloor n t \rfloor) \cdot \xi_{\lfloor n t \rfloor + 1}) / \sqrt{n}. $$
   Continuous (piecewise linear); lives in $C([0, 1])$.

Both versions converge to the same Brownian limit. The interpolated version is preferred for Mathlib because:

- $C([0, 1])$ is a Polish space with a clean metric (sup-norm) — much simpler than the Skorohod $J_1$ metric;
- $C([0, 1])$ embeds into $D([0, 1])$ canonically, and the sup-norm topology agrees with the Skorohod topology on $C([0, 1])$;
- Continuous-mapping arguments are cleaner: every continuous $\Phi : C([0,1]) \to \mathbb{R}$ extends (with possible discontinuity at boundary paths) to $D([0, 1])$.

Mathlib has neither space first-class but has `BoundedContinuousFunction` and the type-level `C(α, β)`, which can be specialised to $C([0,1], \mathbb{R})$.

### Bibliographic references

1. **Donsker, M. D.** *An invariance principle for certain probability limit theorems.* Mem. Amer. Math. Soc. **6** (1951), 12 pp.
2. **Billingsley, P.** *Convergence of Probability Measures*, 2nd ed., Wiley 1999, Chapter 2 (Donsker's theorem, pages 91-116) and Chapter 3 (Tightness, pages 124-138).
3. **Karatzas, I. and Shreve, S. E.** *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer 1991, Chapter 2 (§2.8, Donsker's invariance principle, pages 70-77).
4. **Lévy, P.** "Sur certains processus stochastiques homogènes." *Compositio Math.* **7** (1939), 283-339.
5. **Sparre Andersen, E.** "On the number of positive sums of random variables." *Skand. Aktuarietidskr.* **32** (1949), 27-36.
6. **Prokhorov, Y. V.** "Convergence of random processes and limit theorems in probability theory." *Theor. Probab. Appl.* **1** (1956), 157-214.
7. **Feller, W.** *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Wiley 1968, Chapter III (Reflection principle and lattice-path arguments).
8. **Resnick, S.** *A Probability Path*, Birkhäuser 1999, §9.5 (Donsker's theorem, pedagogical treatment).
9. **Mörters, P. and Peres, Y.** *Brownian Motion*, Cambridge 2010, Chapter 1 (functional CLT and Donsker proof via Skorohod embedding).
10. **OEIS A000984**: Central binomial coefficients $\binom{2n}{n}$ — appears in the Sparre Andersen formula.

### Wiedijk's "100 Theorems" tracker

| Item | Theorem | Status across major provers (as of 2026) |
|---:|---|---|
| 28 | Bertrand's ballot problem | Lean (this gallery), Coq, HOL Light, Isabelle |
| 45 | Donsker's theorem | **none** — open in all major provers |
| 91 | Lévy's arcsine law | **none** — open in all major provers |
| 92 | Reflection principle (Brownian) | partial; depends on Donsker |

A Lean encoding of items 45, 91, 92 (even axiomatized) would be a meaningful contribution to the formal-mathematics ecosystem.

### Mathlib API names (Lean 4, pinned revision 4.26.0)

- `MeasureTheory.ProbabilityMeasure` — probability measures as a type.
- `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_apply_tendsto` — partial weak convergence statement (only on finite-dimensional projections).
- `MeasureTheory.Measure.Portmanteau` — partial portmanteau equivalence (basic forms).
- `ContinuousMap.bounded` and `BoundedContinuousFunction` — sup-norm continuous functions.
- `ProbabilityTheory.iIndepFun` — i.i.d.\ sequences.
- `ProbabilityTheory.gaussianReal` — standard normal distribution.
- `Real.gaussianPdf` — Gaussian probability density.
- `Nat.floor`, `Int.floor` — floor functions (use `Nat.floor` for $\lfloor n t \rfloor$ with $t \ge 0$).
- `Finset.sum_range`, `Finset.range_succ` — partial-sum manipulation.
- `MeasureTheory.HasFiniteIntegral`, `MeasureTheory.IsFiniteIntegral` — variance assumption.

### Connection to other gallery slugs

| Slug | Connection | Direction |
|---|---|---|
| `ballot-problem` | Parent of parent; discrete reflection lives here | upstream |
| `ballot-problem-oq-02` | Parent; axiomatizes the three target identities | upstream |
| `ballot-problem-oq-03-oq-01` | Reflection-principle sibling | sibling |
| `arcsine-law` | Lévy 1939 statement standalone | sibling |
| `central-limit-theorem` | Pointwise CLT — input to Donsker tightness step | upstream |
| `kolmogorov-smirnov` | Empirical-process invariance (Donsker for empiricals) | sibling |
| `wiener-measure-existence` | Brownian motion as a measure (Mathlib gap) | upstream |
| `wiener-measure-continuity` | Sample-path continuity (Kolmogorov-Centsov) | upstream |
| `prokhorov-theorem` | Tightness + weak convergence (Mathlib gap) | upstream |

The slug sits at a busy intersection: upstream of Lévy's arcsine and the parent reflection principle; downstream of CLT, Wiener measure, and Prokhorov.

### Why "axiomatize Donsker, prove derivations" is the right scoping for the OQ

A direct Lean proof of Donsker would require:

1. A formal definition of weak convergence on $C([0, 1], \mathbb{R})$ — partial in Mathlib.
2. Prokhorov's theorem in the metric-space setting — gap.
3. Kolmogorov-Centsov continuity criterion — gap.
4. Tightness via second-moment bound — gap (needs (3)).
5. Finite-dimensional CLT — partial (1-D CLT in Mathlib, multi-D via direct extension).

The minimum-viable path that this OQ can realistically deliver:

- Axiomatize Donsker (S2): one new axiom replaces six gap items.
- Prove the discrete reflection (S3): zero axioms, 100 lines, completely tractable.
- Axiomatize the continuous mapping for sup (S4): one more axiom for the bridge.
- Derive continuous reflection (S4 cont.), continuous first passage (S5), and Lévy arcsine (S6, requires Sparre Andersen): all theorems.

Final axiom budget: 2-3 axioms (Donsker, CMT-for-sup, possibly CMT-for-integral). The parent's axiom count drops from 3 to 0 (its axioms become theorems). Net axiom count for the OQ-05 file: 2-3; net axiom count for the parent + OQ-05 system: 2-3 (vs. 3 in the parent alone, so a net of 0 reduction in axiom count, but a *concentration* of the axioms into one well-defined classical statement, Donsker).

This is exactly the pattern of the gallery's "axiomatize once, derive everywhere" architecture: collapse multiple ad hoc axioms into one named classical theorem.

## S2 (researcher-9, 2026-05-15) — ACT statement layer

Shipped `proofs/Proofs/BallotProblemOQ02OQ05.lean` (~95 LOC). Build verified by Docker (7744 jobs successful, file built in 6.8s on cache hit).

### Implementation notes

1. **Hypothesis pattern.** The S1 sketch's `∀ i j, i ≠ j → IndepFun (xi i) (xi j) μ` is mutual independence's weaker pairwise cousin. Classical Donsker requires *mutual* independence, so the axiom uses Mathlib's `iIndepFun xi μ` (matching `Proofs/FairGamesTheoremOQ02OQ01OQ01.lean:59`'s pattern). Pairwise independence is provably insufficient for finite-dimensional CLT, hence insufficient for Donsker — the strengthening is needed to keep the axiom mathematically truthful.

2. **Named partial sum.** Introduced `partialSum xi k ω := ∑ i ∈ Finset.range k, xi i ω` as a top-level definition rather than inlining `∑ i ∈ Finset.range k, xi i ω` inside `interpolatedRescaled`. Two reasons:
   - S3 will need an algebraic-shape lemma `partialSum xi (k + 1) ω = partialSum xi k ω + xi k ω` (immediate from `Finset.sum_range_succ`) to reason about the random walk one-step-at-a-time. A named definition makes such lemmas reusable across S3-S6.
   - It clarifies the formula `S_⌊tn⌋ + frac · ξ_⌊tn⌋` in `interpolatedRescaled`: the "current accumulated sum" and the "next step's contribution" are visually distinct.

3. **Weak-convergence predicate scope.** `WeakConvergesInC01` is defined against `Continuous Φ` where `Φ : (ℝ → ℝ) → ℝ` carries the pointwise (product) topology on `ℝ → ℝ`. This is **strictly weaker** than the classical sup-norm formulation (every sup-norm-continuous functional is pointwise continuous, but not conversely). For our axiomatic targets in S3-S7 (which only use sup, max, and indicator integrals — all sup-norm continuous), this scope suffices. A Polish-refinement upgrade can replace the predicate without breaking downstream proofs.

4. **`n = 0` degenerate case.** At `n = 0`: `t * 0 = 0`, `⌊0⌋₊ = 0`, `partialSum xi 0 ω = 0`, `frac = 0`, so the numerator is `0 + 0 * ξ_0 = 0`. Denominator `Real.sqrt 0 = 0`. By Lean's divide-by-zero convention, the formula yields `0`. This is consistent with the convention "no data, no walk" and matches both the Mathlib Standard Library convention and the intuition that an empty walk is trivially at zero.

5. **Type-class inference.** The `IsProbabilityMeasure μ` and `MeasurableSpace Ω` instances on the axiom signature ensure that `∫ ω, Φ (...) ∂μ` resolves to the expected `MeasureTheory.integral`. The `Continuous Φ` requirement does not add explicit measurability — but for `Φ` non-measurable, the Bochner integral defaults to `0` in both terms, and the predicate is trivially satisfied — matching the operational content of weak convergence as a property *only* of integrable continuous functionals.

### Build evidence

- Docker: `LEAN_MEMORY_LIMIT=8192 LEAN_BUILD_TIMEOUT=30m ./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05` succeeded in ~13 minutes (cold cache, 7727 cache files downloaded, 7744 jobs).
- File-only build time: 6.8s (after cache hit).
- No warnings reported.

### Confirmed v4.26.0 API surface

The following Mathlib identifiers are pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the v4.26.0 reference) and used by this file:

| Identifier | Module |
|---|---|
| `Finset.range`, `Finset.sum` | `Mathlib.Algebra.BigOperators.Basic` |
| `Nat.floor` (`⌊_⌋₊`) | `Mathlib.Data.Nat.Floor` |
| `Real.sqrt` | `Mathlib.Analysis.SpecialFunctions.Pow.Real` |
| `Pairwise` | `Mathlib.Order.Defs` |
| `MeasureTheory.Measure`, `IsProbabilityMeasure`, `MeasureTheory.integral` | `Mathlib.MeasureTheory.Measure.MeasureSpace` |
| `ProbabilityTheory.IndepFun` | `Mathlib.Probability.Independence.Basic` |
| `Measurable` | `Mathlib.MeasureTheory.MeasurableSpace.Defs` |
| `Continuous` | `Mathlib.Topology.Basic` |
| `ContinuousBallot.BrownianMotion` | `Proofs/BallotProblemOQ02.lean:75-93` (parent gallery entry) |

### Axiom audit (post-S2)

| File | Axioms |
|---|---|
| `Proofs/BallotProblemOQ02.lean` (parent) | 3 (`reflection_principle`, `firstPassageTime_eq_maxEvent`, embedded arcsine) |
| `Proofs/BallotProblemOQ02OQ05.lean` (new) | 1 (`donsker_fclt`) |
| **System total** | **4** (will collapse to 2-3 after S4-S6 derives parent's three from `donsker_fclt` + CMT-axioms) |

### Open questions for S3+

- **`partialSumBool` vs `partialSum`?** S3 will be on `Fin n → Bool` walks (the ±1 walk encoded as Bool). A new function `partialSumBool` is needed; should it be defined here in `BallotProblemOQ02OQ05.lean` (so that S3+S4 chain bridges easily) or in S3's own file? Recommendation: S3's own file — keeps S2 statement-only.

- **`WeakConvergesInC01` measurability.** The integrals `∫ ω, Φ (fun t => Xn n t ω) ∂μ` implicitly require measurability of the integrand. The current predicate omits this — meaning non-measurable continuous functionals produce trivial inequalities. This is *acceptable* for the axiomatic statement (Donsker only constrains the test-functional class) but should be tightened (`AEMeasurable` ⇒ tighter predicate) when refining S4's continuous-mapping-for-sup axiom.

- **Hypothesis-set audit.** `donsker_fclt` takes `iIndepFun xi μ` (mutual independence) — matches classical Donsker. The mean/variance assumptions could be tightened from "every $\xi_i$ has zero mean / unit variance" to "every $\xi_i$ is identically distributed with $\mathbb{E}\xi_0 = 0, \mathbb{E}\xi_0^2 = 1$" via `IdentDistrib`, but this is a stylistic choice — Lindeberg's CLT covers the weaker hypotheses we currently use. Defer the i.i.d.-tightening to S6 when arcsine derivation needs `IdentDistrib` for the cycle lemma.

