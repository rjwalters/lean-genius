# Problem: Donsker's functional CLT — connecting discrete and continuous ballot

## Statement

### Plain Language

The parent gallery entry `ballot-problem-oq-02` (`Proofs/BallotProblemOQ02.lean`) axiomatizes the continuous-time ballot problem via Brownian motion: it states (without proof) the reflection principle, the first-passage time CDF, and Lévy's arcsine law, then derives the continuous ballot probabilities. The sibling `ballot-problem` family formalizes the **discrete** ballot problem (Bertrand 1887): if $A$ gets $p$ votes and $B$ gets $q$ votes with $p > q$, then $P(A \text{ leads throughout}) = (p - q) / (p + q)$.

This OQ asks the natural bridge:

> **Provide a formal proof of Donsker's functional central limit theorem (FCLT) that exhibits the continuous ballot problem as the $n \to \infty$ scaling limit of the discrete ballot random walk.**

The classical statement is:

**Theorem (Donsker 1951)**. Let $\xi_1, \xi_2, \ldots$ be i.i.d. random variables with mean $0$ and variance $1$. Define the partial sums $S_n = \sum_{i=1}^n \xi_i$ and the **interpolated rescaled random walk** $S_n^* : [0, 1] \to \mathbb{R}$ by

$$
S_n^*(t) = \frac{1}{\sqrt{n}} \big( S_{\lfloor n t \rfloor} + (n t - \lfloor n t \rfloor) \cdot \xi_{\lfloor n t \rfloor + 1} \big).
$$

Then $S_n^* \Rightarrow W$ in $C([0, 1])$, where $W$ is standard Brownian motion on $[0, 1]$ and $\Rightarrow$ denotes weak convergence (convergence in distribution of $C([0, 1])$-valued random variables under the supremum norm).

**Consequence (continuous mapping)**. For any continuous (or a.s.-continuous) functional $\Phi : C([0, 1]) \to \mathbb{R}$, $\Phi(S_n^*) \Rightarrow \Phi(W)$. Three classical specialisations:

| Discrete functional | Continuous limit | Result |
|---|---|---|
| $\max_{1 \le k \le n} S_k / \sqrt{n}$ | $\max_{0 \le t \le 1} W(t)$ | Reflection principle: $P(\max W \ge a) = 2 P(W_1 \ge a)$ |
| $\inf\{k : S_k = a \sqrt{n}\} / n$ | $\tau_a := \inf\{t : W(t) = a\}$ | First-passage CDF: $P(\tau_a \le t) = 2(1 - \Phi(a / \sqrt{t}))$ |
| $\#\{k : S_k > 0\} / n$ | $\int_0^1 \mathbf{1}_{W(t) > 0} \, dt$ | Lévy's arcsine law: $P(\text{fraction} \le r) = (2/\pi) \arcsin \sqrt{r}$ |

Each of the three axioms in the parent file (`reflection_principle`, `firstPassageTime_eq_maxEvent`, the arcsine identity inside the main theorem) is in principle derivable from Donsker's theorem plus the corresponding discrete-walk identity (which is provable elementarily in the discrete ballot setting).

### Formal Statement (target Lean signatures)

The natural Lean type signatures at the pinned Mathlib v4.26.0 revision:

```lean
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Function.LpSpace
import Proofs.BallotProblemOQ02  -- for the BrownianMotion structure

/-- Interpolated rescaled random walk on `[0, 1]`. -/
noncomputable def interpolatedRescaled
    {Ω : Type*} (xi : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  let k := ⌊t * n⌋₊
  let frac := t * n - k
  (∑ i ∈ Finset.range k, xi i ω + frac * xi k ω) / Real.sqrt n

/-- **Donsker's functional CLT (axiomatized at v4.26.0).**
For i.i.d. mean-0 variance-1 random variables, the rescaled interpolated
random walk converges weakly in `C([0, 1])` to standard Brownian motion. -/
axiom donsker_fclt
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (xi : ℕ → Ω → ℝ)
    (hiid : ∀ i, Measurable (xi i))  -- abbreviation for i.i.d. assumption
    (hmean : ∀ i, ∫ ω, xi i ω ∂μ = 0)
    (hvar  : ∀ i, ∫ ω, (xi i ω)^2 ∂μ = 1) :
    ∃ bm : ContinuousBallot.BrownianMotion Ω μ,
      -- the rescaled walk converges weakly to `bm.W` in `C([0,1])`
      True  -- placeholder: weak convergence stated via Filter.Tendsto on
            -- `MeasureTheory.ProbabilityMeasure (C([0,1] → ℝ))`

/-- **Reflection principle from Donsker.**
Derive the parent's `reflection_principle` axiom from `donsker_fclt`
applied to the symmetric ±1 random walk + the discrete reflection identity. -/
theorem reflection_principle_from_donsker
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (bm : ContinuousBallot.BrownianMotion Ω μ) (a T : ℝ) (ha : 0 < a) (hT : 0 < T) :
    μ {ω | ∃ t ∈ Set.Icc 0 T, bm.W t ω ≥ a} = 2 * μ {ω | bm.W T ω ≥ a} := by
  sorry  -- via donsker_fclt + discrete-walk reflection (elementary)
```

The structural goal of this OQ is: ship at least the **statement** of Donsker's FCLT as a single axiom at the right type, plus the **derivation pipeline** sketch showing how each of the three axioms in `BallotProblemOQ02.lean` would follow from it.

## Classification

```yaml
tier: B
significance: 8
tractability: 3
tags:
  - seeker-selected
  - probability
  - brownian-motion
  - donsker
  - functional-clt
  - ballot-problem
  - weak-convergence
  - mathlib-gap
  - classical
```

**Significance**: 8/10 — Donsker's FCLT is Wiedijk #45 ("Donsker's theorem") on the "Formalizing 100 Theorems" tracker, unformalized in Mathlib at the pinned revision. It is the canonical bridge between discrete-time random walks and continuous-time Brownian motion, sitting at the heart of probabilistic combinatorics, mathematical finance, and statistical physics. Formalizing even the axiomatic statement + derivation pipeline would advance Mathlib's probability story and remove three independent axioms from the parent `BallotProblemOQ02.lean`.

**Tractability**: 3/10 — Hard:

- **Statement of Donsker as an axiom**: feasible, ~50 Lean lines. Needs a careful encoding of weak convergence on `C([0, 1], ℝ)` (which requires the metric space + Borel sigma-algebra to be set up; partially available in Mathlib).
- **Discrete reflection identity** ($P(\max S_k \ge a) = 2 P(S_n \ge a + 1) + P(S_n = a)$): tractable, ~100 lines of bijective combinatorics on lattice paths. This is the **only** mathematical content of the OQ that is unambiguously single-session-feasible.
- **Continuous reflection from Donsker + discrete**: requires the continuous mapping theorem for $\Phi = \sup$, which in turn requires showing $\sup$ is continuous on $C([0, 1])$ (one-line) plus a careful tightness argument so that $\sup S_n^*$ has weak limit $\sup W$ (~200 lines of advanced measure theory).
- **Full proof of Donsker** (not axiomatized): well beyond a single iteration. Goes via Kolmogorov-Centsov continuity for the limit, Prokhorov tightness for the family, and finite-dimensional convergence by classical CLT. Each step requires Mathlib infrastructure that is partial-to-absent.

## Why This Matters

1. **Mathlib coverage** — Mathlib v4.26.0 has `Mathlib.MeasureTheory.Function.LpSpace`, `Mathlib.Probability.Distributions.Gaussian`, and a partial `Mathlib.Probability.Independence.Basic`, but **no Brownian motion**, **no weak convergence on $C([0, 1])$**, and **no Donsker's theorem**. The Skorohod space $D([0, 1])$ is also absent. This OQ is the first attempt to articulate the Donsker pipeline in Mathlib idiom.

2. **Removes three axioms from the parent** — `Proofs/BallotProblemOQ02.lean` carries `reflection_principle`, `firstPassageTime_eq_maxEvent`, and the embedded arcsine identity as axioms (badge: `axiom`). Donsker plus standard discrete-walk identities derives all three. A successful OQ-05 thus collapses the axiom count of the parent from 3 to 1 (Donsker itself).

3. **Bridge to Wiedijk #45** — Wiedijk's tracker lists "Donsker's theorem" as item 45 of the "100 Theorems" canon, and there is no formal proof on file in any major theorem prover. A Lean version (even axiomatized) is genuine library novelty.

4. **Connection to broader gallery** — The continuous ballot problem connects to: the parent discrete ballot problem (`ballot-problem`), Lévy's arcsine law (`arcsine-law` family), reflection-principle proofs (`reflection-principle`), Brownian motion infrastructure (in `wiener-measure-oq-*`, partial), and the CLT family (`central-limit-theorem-*`). Donsker is the **functional generalisation** of the classical CLT, and OQ-05 is one of the few places in the gallery where this generalisation is explicitly demanded.

## Theoretical Background

### Discrete to continuous: the scaling map

For $\xi_i \in \{-1, +1\}$ symmetric Bernoulli random variables, the symmetric random walk $S_n = \sum_{i=1}^n \xi_i$ has step variance $1$ (so $\mathrm{Var}(S_n) = n$). The rescaling $S_n / \sqrt{n}$ has variance $1$ for every $n$, and by the classical CLT,

$$
\frac{S_n}{\sqrt{n}} \xrightarrow{d} W_1 \sim N(0, 1).
$$

Donsker upgrades this **pointwise** convergence to a **functional** convergence: the entire interpolated trajectory $\{S_n^*(t) : 0 \le t \le 1\}$ converges, as an element of $C([0, 1], \mathbb{R})$, to standard Brownian motion. This is a much stronger statement: it implies that *any* continuous functional of the trajectory has the limit distribution induced by Brownian motion.

### Why weak convergence on $C([0, 1])$ is the right setting

Two reasons:

1. **Continuous functionals close under weak limit** (Portmanteau theorem). If $\Phi : C([0, 1]) \to \mathbb{R}$ is continuous and $X_n \Rightarrow X$, then $\Phi(X_n) \Rightarrow \Phi(X)$. This is exactly the **continuous mapping theorem**, and it is the reason Donsker is useful.

2. **Tightness via Arzelà-Ascoli**. To prove $S_n^* \Rightarrow W$ in $C([0, 1])$, one shows the family $\{S_n^*\}$ is **tight** (uniformly relatively compact in distribution), which by Prokhorov reduces to a finite-dimensional convergence + an equicontinuity (modulus-of-continuity) bound. The classical CLT supplies the finite-dimensional convergence; Kolmogorov-Centsov supplies the equicontinuity.

### Three discrete identities and their continuous shadows

For the symmetric ±1 walk $S_n$, three identities (all provable by lattice-path bijections) translate via Donsker to the continuous Brownian world:

**(1) Discrete reflection.** For $a > 0$,
$$
P(\max_{1 \le k \le n} S_k \ge a) = 2 P(S_n \ge a) + P(S_n = a) \cdot (\text{correction term for parity}).
$$
The bijection: a path reaching $a$ and ending below $a$ is reflected after its first hit of $a$ to give a path ending above $2a - S_n$. The continuous shadow ($n \to \infty$, $a \sim a\sqrt{n}$): $P(\max W_t \ge a) = 2 P(W_1 \ge a) = 2 (1 - \Phi(a))$.

**(2) Discrete first passage.** Let $T_a^{(n)} = \min\{k : S_k = a\sqrt{n}\}$. Then
$$
P(T_a^{(n)} \le n) = P(\max_{1 \le k \le n} S_k \ge a \sqrt{n}) \to P(\tau_a \le 1) = 2(1 - \Phi(a)).
$$
The CDF identity follows directly from (1).

**(3) Discrete arcsine.** Let $L_n = \#\{k \le n : S_k > 0\}$ (number of positive partial sums up to time $n$). Then Sparre Andersen's theorem (1949) gives
$$
P(L_n = k) = \binom{2k}{k} \binom{2(n-k)}{n-k} \cdot 2^{-2n},
$$
which by Stirling tends to the arcsine density $1 / (\pi \sqrt{r(1-r)})$ for $k / n \to r$. Donsker + continuous mapping (the functional $L : C([0,1]) \to \mathbb{R}$, $L(f) = \int_0^1 \mathbf{1}_{f(t) > 0} \, dt$, is a.s.-continuous w.r.t.\ Brownian measure) gives **Lévy's arcsine law**:
$$
P\big( \int_0^1 \mathbf{1}_{W_t > 0} \, dt \le r \big) = \frac{2}{\pi} \arcsin \sqrt{r}.
$$

The OQ thus asks for a Lean encoding of: (a) Donsker as axiom, (b) each of the three discrete identities as theorems (provable, finite combinatorics), (c) the derivation pipeline reflection $\to$ first passage $\to$ arcsine via Donsker + continuous mapping.

### Skorohod $D([0, 1])$ versus $C([0, 1])$

Donsker is sometimes stated on the **Skorohod space** $D([0, 1])$ of càdlàg (right-continuous-with-left-limits) functions, where the natural metric is the Skorohod $J_1$ metric. For the i.i.d. partial-sum case both work; for **interpolated** rescaled walks (as defined in `interpolatedRescaled` above), $S_n^*$ is in $C([0, 1])$ already, and the simpler sup-norm metric suffices. Mathlib v4.26.0 has neither $D([0, 1])$ nor weak convergence on $C([0, 1])$ as first-class objects, so the OQ must build the minimal scaffolding ad hoc.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `ballot-problem-oq-02` (parent) | Continuous-time ballot via Brownian motion (3 axioms) |
| `ballot-problem` | Discrete ballot via lattice paths (Bertrand 1887) |
| `ballot-problem-oq-01` | Cycle lemma & Catalan-number variant |
| `ballot-problem-oq-03-oq-01` | Reflection-principle infrastructure (sibling OQ) |
| `arcsine-law` family | Lévy's arcsine law (continuous shadow of Sparre Andersen) |
| `central-limit-theorem` | Classical pointwise CLT (Donsker is the functional upgrade) |
| `central-limit-theorem-oq-04` | Local CLT (refinement complementary to Donsker) |
| `wiener-measure-*` | Brownian motion construction (Mathlib gap, multiple OQs) |
| `kolmogorov-smirnov` | Empirical-process CLT (Donsker for indicator functionals) |

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4) | Module | Status |
|---|---|---|---|
| Probability measure on a Polish space | `MeasureTheory.ProbabilityMeasure` | `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` | available |
| Weak convergence of measures | `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_apply_tendsto` (partial) | `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` | partial |
| Continuous functions $[0,1] \to \mathbb{R}$ | `C(Set.Icc (0:ℝ) 1, ℝ)` via `ContinuousMap` | `Mathlib.Topology.ContinuousFunction.Basic` | available |
| Sup-norm on $C([0,1])$ | `BoundedContinuousFunction` | `Mathlib.Topology.ContinuousFunction.Bounded` | available |
| Polish space instance for $C([0,1])$ | (none — needs separability of `C` proved via Stone-Weierstrass) | — | **gap** |
| Tightness | `MeasureTheory.IsTightFamily` | `Mathlib.MeasureTheory.Measure.Tight` | partial |
| Prokhorov's theorem | (none) | — | **gap** |
| Continuous mapping theorem | (none) | — | **gap** |
| Standard normal CDF $\Phi$ | `ProbabilityTheory.gaussianReal` | `Mathlib.Probability.Distributions.Gaussian` | available |
| I.i.d.\ sequence | `ProbabilityTheory.iIndepFun` | `Mathlib.Probability.Independence.Basic` | available |
| Random walk | `ProbabilityTheory.RandomWalk` | (none at v4.26.0; ad hoc only) | **gap** |
| Kolmogorov-Centsov continuity | (none) | — | **gap** |
| Donsker's theorem | (none) | — | **gap** |
| Brownian motion (existence) | (none; the parent file axiomatizes) | — | **gap** |

**Gap summary**: of the 13 ingredients needed for a full proof of Donsker, ~4 are available, ~2 are partial, and ~7 are gaps. This is consistent with Donsker being a "frontier" probabilistic target rather than a single-session formalisation.

## Suggested Next-Action Decomposition

This is **OBSERVE** phase. No Lean changes yet — only a survey and a concrete deliverable list.

1. **S2 — `interpolatedRescaled` definition + Donsker axiom statement** (~80 lines).
   - Define `interpolatedRescaled : (ℕ → Ω → ℝ) → ℕ → ℝ → Ω → ℝ` carefully.
   - State `donsker_fclt` as an axiom with the correct (∃ Brownian motion) signature.
   - Encode "weak convergence in `C([0, 1])`" minimally; if Mathlib lacks the right type, axiomatize the predicate `WeakConvergesIn_CIcc01` as well.
   - Deliverable: one new file `proofs/Proofs/BallotProblemOQ02OQ05.lean` with the Donsker axiom + 1-2 immediate corollaries (discrete CLT recovery).
   - 0 sorries, 1 new axiom, 0 theorems requiring proof.

2. **S3 — Discrete reflection identity** (~100 lines, fully proved).
   - State `discrete_reflection : ∀ n a, P(max S_k ≥ a) = 2 P(S_n ≥ a) + P(S_n = a)` for the symmetric ±1 walk.
   - Prove by the classical lattice-path reflection bijection.
   - This is the **only** sorry-free deliverable of substance in the OQ-05 pipeline; everything else axiomatizes.
   - 0 sorries, 0 new axioms, 1 new theorem.

3. **S4 — Continuous mapping for $\sup$** (~50 lines, axiom-with-derivation).
   - State `continuous_mapping_sup : (X_n ⇒ X in C([0,1])) → (sup X_n ⇒ sup X)` as an axiom (the general continuous mapping theorem requires Polish + Portmanteau, both gaps).
   - Combine with `donsker_fclt` + `discrete_reflection` to derive the parent's `reflection_principle` as a theorem (no longer an axiom).
   - This closes the first of three parent axioms.

4. **S5 — First passage from reflection** (~40 lines, fully proved from S4).
   - The first-passage CDF is an algebraic consequence of the maximum CDF (parent's `first_passage_cdf` already proves this).
   - The deeper axiom `firstPassageTime_eq_maxEvent` (the event identity $\{\tau_a \le T\} = \{\max W \ge a\}$) requires path-continuity + $\inf$-of-closed-set theory; can be downgraded from an axiom to a theorem given the BrownianMotion structure's `pathContinuous` field. Plausibly a 30-line `extracta` from `BrownianMotion.pathContinuous` + `Real.csInf_mem`.

5. **S6 — Arcsine law via Sparre Andersen** (~150 lines, ambitious).
   - State `sparre_andersen : P(L_n = k) = (2k choose k)·(2(n-k) choose (n-k))·2^{-2n}` (theorem, provable by bijection).
   - State `arcsine_density_limit : ∀ r, P(L_n / n ≤ r) → (2/π) arcsin √r` (axiom, via Stirling + continuous mapping for the integral functional).
   - Combine to obtain the parent's arcsine law as a theorem.
   - Largest single S-step in the plan; could be split.

6. **S7 — Wrap-up**: update `Proofs/BallotProblemOQ02.lean` to depend on the new file, downgrading its 3 axioms to theorems (status changes from `axiomatized` to `verified` if Donsker can also be downgraded; more realistically, `axiomatized` with axiom count $3 \to 1$).

Each of S2–S5 is a ~50–100-line single-session deliverable. S6 is ambitious and may itself need splitting. S7 is documentation + status update.

## Risk Notes

- **Mathlib drift**: weak convergence on `C([0, 1])` is partially in Mathlib via `MeasureTheory.ProbabilityMeasure` and `Mathlib.MeasureTheory.Measure.Portmanteau`; the API names may shift between revisions. Pin to v4.26.0 and check `Mathlib.MeasureTheory.Measure.Portmanteau` early in S2.
- **Borel sigma-algebra on `C([0, 1])`**: the metric structure on `BoundedContinuousFunction` is available, but the canonical Borel measure space structure may not be auto-derived. Be prepared to manually invoke `BorelSpace` instance derivation.
- **i.i.d. encoding**: Mathlib's `ProbabilityTheory.iIndepFun` is well-tested; the additional mean/variance assumptions plug in via `MeasureTheory.IsFiniteIntegral` + `MeasureTheory.HasFiniteIntegral`.
- **Decidability of $\lfloor n t \rfloor$ for real $t$**: use `Nat.floor` not `Int.floor` to avoid sign-handling; `interpolatedRescaled` should restrict $t \in [0, 1]$ via `Set.Icc`.
- **Axiom-count honesty**: the parent's status is `axiomatized` with 3 axioms. After S2–S6 the count becomes 1 (Donsker itself) + possibly 1 (continuous mapping for $\sup$) + possibly 1 (arcsine-density limit) = up to 3 axioms total. The status should remain `axiomatized` unless Donsker is itself proved (well beyond single-session scope).
- **Wiedijk #45 visibility**: any future "Donsker's theorem in Lean" statement MUST clearly say "axiom" until a Mathlib proof exists, to avoid over-claiming on the 100-theorems tracker.
- **Sibling slug conflicts**: `ballot-problem-oq-03-oq-01-oq-01` and `ballot-problem-oq-01-oq-04-oq-01` are reflection-principle slugs in adjacent positions; coordinate with their state-files to avoid duplicating the discrete reflection identity in S3.

## Adversarial Checklist (SOLVED claim, 2026-07-24 — discrete-reflection scope)

The S12 claim: the **discrete-reflection section** of
`proofs/Proofs/BallotProblemOQ02OQ05.lean` is fully proved (0 sorries; the sole
axiom is the intended `donsker_fclt` statement axiom). Ways THIS claim could be
wrong, and why each is excluded:

- **Scope inflation.** The claim is NOT that OQ-05's continuous-side plan
  (S4–S7: deriving the parent's 3 axioms from Donsker) is done — those remain
  future DEEP work and `donsker_fclt` remains an axiom (Wiedijk #45 stays
  "axiom", per the Risk Notes above). The completed unit is exactly what S11
  pinned as "the only work left on this slug": `reaches_iff_hits_or_above` +
  `discrete_reflection`.
- **Degenerate reflection branch.** `reflectAt` defaults `firstHitFin` to
  `⟨0,_⟩` on paths that never hit `a`; the S7-PREP counterexample showed the
  unconditional involution is FALSE. Confirm every use of
  `reflectAt_involutive` supplies `(hitSet ω a).Nonempty`: the D-class carries
  it by definition; the E-class derives it via `hitSet_nonempty_of_ge`
  (endpoint `> a ≥ a` + discrete IVT). No use is unconditioned.
- **Overshoot in the IVT.** `hitSet_nonempty_of_ge` requires `0 < a` (paths
  start at `S₀ = 0 < a`); a `+1` jump from `< a` lands `≤ a`. For `a ≤ 0` the
  claim would be false as stated (e.g. `a = 0` is hit at index 0 regardless) —
  the lemma and both consumers carry `0 < a`.
- **Double-counting in the partition.** `A = B ∪ D` uses the DISJOINTIFIED
  form (`D` requires `S_n < a`), not the raw `reaches ↔ ends-≥ ∨ hits`
  disjunction whose disjuncts overlap. `card_union_of_disjoint` demands the
  proved `Disjoint` terms — no double count.
- **ℕ-subtraction truncation.** The statement uses `2·|B| − |C|` in ℕ;
  truncation would silently weaken it if `|C| > 2·|B|`. From `B = C ⊔ E`,
  `|C| ≤ |B|`, so the subtraction is exact; the closing `omega` uses the three
  card equations, not truncation coincidences.
- **Wrong-multiplicity near-miss.** The bijection is between `D` (ends `< a`,
  hits) and `E` (ends `> a`) — NOT the classical-but-different pairing with
  "ends ≥ a". The final identity was cross-checked against the partition
  algebra `|A| = |B| + |E|` and `|E| = |B| − |C|`, which is exactly André's
  count.
