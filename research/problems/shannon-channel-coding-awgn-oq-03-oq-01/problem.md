# Problem: Capacity of parallel Gaussian channels via water-filling

**Slug**: shannon-channel-coding-awgn-oq-03-oq-01
**Created**: 2026-07-09T16:03:15-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $N_1, \dots, N_n > 0$ be the noise powers of $n$ independent parallel Gaussian
sub-channels, and let $P \ge 0$ be a total transmit-power budget. Define the
per-allocation rate

$$
R(P_1, \dots, P_n) \;=\; \sum_{i=1}^n \tfrac{1}{2}\log\!\Big(1 + \frac{P_i}{N_i}\Big),
\qquad P_i \ge 0.
$$

The claim is that the constrained maximum over the simplex
$\big\{\,(P_i) : P_i \ge 0,\ \sum_i P_i \le P \,\big\}$ is attained by the
**water-filling** allocation

$$
P_i^\star \;=\; (\mu - N_i)_+ \;=\; \max(\mu - N_i,\, 0),
$$

where the **water level** $\mu \ge 0$ is the unique constant fixed by the budget
constraint

$$
\sum_{i=1}^n (\mu - N_i)_+ \;=\; P,
$$

and the resulting channel capacity is

$$
C(P; N_1,\dots,N_n) \;=\; \max_{\sum_i P_i \le P} R(P_1,\dots,P_n)
\;=\; \sum_{i=1}^n \tfrac{1}{2}\log\!\Big(1 + \frac{P_i^\star}{N_i}\Big)
\;=\; \sum_{i=1}^n \tfrac{1}{2}\log\!\Big(\frac{\max(\mu, N_i)}{N_i}\Big).
$$

### Plain Language

Suppose you must send data over several independent noisy channels at once — each
with its own noise level $N_i$ — and you have a fixed total amount of transmit
power $P$ to split among them. How should you divide the power to maximise the
total data rate? The answer is *water-filling*: imagine pouring water (power) into
a landscape whose ground heights are the noise levels $N_i$. The water settles to a
common surface level $\mu$; each channel receives power equal to the depth of water
above its floor, $(\mu - N_i)_+$. Channels that are too noisy ($N_i \ge \mu$) get no
power at all. This problem asks for a rigorous proof that this intuitive allocation
is genuinely optimal and that the water level is uniquely determined by the budget.

### Why This Matters

- Water-filling is the canonical example of resource allocation in information
  theory and underlies practical schemes such as OFDM/DMT bit-loading in DSL, Wi-Fi
  and 4G/5G, where subcarriers with better SNR are given more power.
- It is the multi-dimensional completion of the scalar Shannon–Hartley formula
  already in the gallery: the parent entry treats one channel; this treats a bank
  of parallel channels and shows how a shared power budget is optimally spread.
- Formalising it exercises constrained concave optimisation (KKT / Lagrange
  multipliers over a simplex) in Lean, a reusable capability well beyond this one
  result.

## Known Results

### What's Already Proven

- Per-use AWGN capacity $\tfrac12\log(1 + P/N)$ nats/use — gallery entry
  `shannon-channel-coding-awgn` (verified, axiom-free).
- Bandlimited Shannon–Hartley $C = B\log_2(1 + P/N)$ bits/s and its full structural
  theory (sign, monotonicities, low-SNR linear bound) — gallery entry
  `shannon-channel-coding-awgn-oq-03` (this problem is the explicitly deferred
  second half of that entry's OQ-03).
- The water-filling theorem is classical mathematics (Shannon 1949; Cover & Thomas,
  *Elements of Information Theory*, Thm 9.9.1). Only the Lean formalization is open.

### What's Still Open

- A Lean 4 proof that the water-filling allocation maximises the parallel-channel
  rate under the sum-power constraint.
- Existence and uniqueness of the water level $\mu$ solving $\sum_i (\mu - N_i)_+ = P$
  (the map $\mu \mapsto \sum_i (\mu - N_i)_+$ is continuous, non-decreasing,
  piecewise-linear, and strictly increasing once $\mu > \min_i N_i$).
- The closed form $C = \sum_i \tfrac12\log(\max(\mu, N_i)/N_i)$ for the optimum value.

### Our Goal

Formalize the finite-dimensional water-filling theorem: define the parallel-channel
rate over a finite index set, prove existence/uniqueness of the water level, prove
the KKT optimality of $P_i^\star = (\mu - N_i)_+$, and derive the closed-form
capacity. Scope is the *equality/optimisation* statement over a fixed finite family
$N_1,\dots,N_n$; the continuous (infinite-band) limit is a separate follow-up.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-channel-coding-awgn-oq-03 | Direct parent; this is its deferred OQ second half | Nyquist rate, change of log base, `Real.logb` monotonicity |
| shannon-channel-coding-awgn | Supplies the per-sub-channel term $\tfrac12\log(1+P_i/N_i)$ | Differential entropy, AWGN capacity |
| shannon-channel-coding-oq-01 | Grandparent: capacities of concrete channels (BSC, BEC, AWGN) | Mutual information, capacity computation |

## Initial Thoughts

### Potential Approaches

1. **Approach A — KKT / Lagrange multipliers (textbook route)**:
   Maximise the concave objective $\sum_i \tfrac12\log(1 + P_i/N_i)$ subject to
   $\sum_i P_i = P$ and $P_i \ge 0$. Stationarity gives
   $\frac{1}{2(N_i + P_i)} = \lambda$ for active channels, i.e. $N_i + P_i = \mu$
   with $\mu = 1/(2\lambda)$; complementary slackness sends inactive channels
   ($N_i \ge \mu$) to $P_i = 0$. Yields $P_i = (\mu - N_i)_+$.
   - Why it might work: it is the standard proof; every step is elementary once
     concavity and the KKT conditions are in place.
   - Risk: Mathlib's convex-optimisation / KKT machinery is thin; the multiplier
     argument may need to be reconstructed by hand.

2. **Approach B — direct concavity + tangent-line (multiplier-free) bound**:
   Guess $P_i^\star = (\mu - N_i)_+$, then prove optimality directly by the
   supporting-hyperplane inequality for the concave $\log$: for any feasible $(P_i)$,
   $R(P_i) - R(P_i^\star) \le \sum_i \tfrac{1}{2\mu}(P_i - P_i^\star) \le 0$ using
   $\log(1+x) \le \log(1+x^\star) + \frac{x - x^\star}{1 + x^\star}$ and
   $1 + P_i^\star/N_i = \mu/N_i$ on active channels. This turns the whole problem
   into one tangent-line inequality plus budget bookkeeping.
   - Why it might work: sidesteps KKT infrastructure; relies only on the concavity
     bound `Real.add_pow_le_pow_mul_pow_of_sq_le` / `Real.log_le_sub_one_of_pos`
     already used by the parent.
   - Risk: careful case analysis on active vs. inactive channels; handling the
     budget equality vs. inequality.

### Key Difficulties

- Establishing existence/uniqueness of $\mu$: continuity and strict monotonicity of
  $\mu \mapsto \sum_i (\mu - N_i)_+$ (a `Finset.sum` of `posPart` maps).
- Case split between active channels ($N_i < \mu$) and inactive ones ($N_i \ge \mu$),
  including complementary slackness at the boundary $N_i = \mu$.
- Choosing a formalisation of "capacity as a maximum" (a `sSup`/`iSup` over the
  feasible set) that is convenient to reason about, and proving the sup is attained.

### What Would a Proof Need?

- Key lemma 1: **water-level existence/uniqueness** — $\exists!\,\mu \ge 0$ with
  $\sum_i (\mu - N_i)_+ = P$ (intermediate value theorem + strict monotonicity on
  $\mu > \min_i N_i$; degenerate $P = 0$ handled separately).
- Key lemma 2: **tangent-line/concavity bound** — $\log(1+x) \le \log(1+y) +
  \frac{x-y}{1+y}$ for $x, y > -1$ (a one-variable concavity inequality).
- Key lemma 3: **upper bound = achieved value** — for every feasible $(P_i)$,
  $R(P_i) \le R(P_i^\star)$, closing optimality.
- Technical requirements: `Finset.sum` manipulation, `posPart`/`max` lemmas,
  IVT (`intermediate_value_Icc`), and the log-concavity bound; no new axioms.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is classical and finite-dimensional (no measure theory beyond the
  per-channel term, which the parent already supplies), so it is not a moonshot.
- However, Mathlib lacks a ready KKT/water-filling theorem, so the constrained
  optimisation must be built from scratch (the multiplier-free Approach B is the
  most self-contained but still needs the water-level and tangent-line lemmas).
- Similar finite concave-optimisation arguments (e.g. AM–GM, Jensen for finite sums)
  are available in Mathlib, giving reusable patterns.
- Real risk lives in the bookkeeping (active/inactive case split, budget equality),
  not in deep theory.

**Estimated Effort**:
- Exploration: 2–4 days (survey Mathlib convexity/`posPart` support, pick approach)
- If tractable: 1–3 weeks (water-level lemma + optimality via tangent-line bound)
- If hard: unknown (if KKT infrastructure must be developed generically)

## References

### Papers
- C. E. Shannon, "Communication in the Presence of Noise", *Proc. IRE* 37(1):10–21,
  1949 — origin of the Gaussian-channel capacity and the sampling-based dimension
  count underlying parallel channels.
- R. G. Gallager, *Information Theory and Reliable Communication*, 1968 — detailed
  treatment of parallel Gaussian channels and power allocation.

### Online Resources
- Cover & Thomas, *Elements of Information Theory* (2nd ed.), §9.4 "Parallel
  Gaussian Channels" and Thm 9.9.1 — the reference statement and proof of
  water-filling being formalised here.
- Boyd & Vandenberghe, *Convex Optimization*, §5.5 / Example 5.2 — water-filling as a
  worked KKT example, the cleanest optimisation-theoretic account.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log`, `Real.log_le_sub_one_of_pos`
  (the concavity bound the tangent-line lemma specialises).
- `Mathlib.Analysis.Convex.SpecificFunctions.Basic` — `Real.strictConcaveOn_log` and
  friends for the concavity of the objective.
- `Mathlib.Algebra.Order.PosPart` / `posPart` lemmas — for $(\mu - N_i)_+$.
- `Mathlib.Topology.Algebra.Order.IntermediateValue` — `intermediate_value_Icc` for the
  water-level existence proof.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum` manipulation across sub-channels.

## Metadata

```yaml
tags:
  - information-theory
  - channel-capacity
  - shannon-hartley
  - awgn
  - shannon
  - analysis
  - coding-theory
  - optimization
related_proofs:
  - shannon-channel-coding-awgn-oq-03
  - shannon-channel-coding-awgn
difficulty: high
source: user-request
created: 2026-07-09T16:03:15-07:00
```
