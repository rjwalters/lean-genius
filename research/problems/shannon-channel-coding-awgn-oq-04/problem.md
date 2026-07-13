# Problem: Operational Coding Theorem for the AWGN Channel — Random Gaussian Codebooks and the Sphere-Packing Converse

**Slug**: shannon-channel-coding-awgn-oq-04
**Created**: 2026-07-09T15:23:00-07:00
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

For the additive white Gaussian noise channel $Y = X + Z$ with independent noise $Z \sim N(0, N)$, an average-power constraint $\frac{1}{n}\sum_{i=1}^{n}\mathbb{E}[X_i^2] \le P$, and capacity $C(P,N) = \tfrac12\log\!\left(1 + \tfrac{P}{N}\right)$, the *operational* capacity equals the *information* capacity. Concretely, for every $\varepsilon > 0$:

$$
\Big(\;R < C(P,N) \;\Longrightarrow\; \exists\, (2^{nR}, n)\text{-codes with } P_e^{(n)} \to 0\;\Big)
\quad\text{and}\quad
\Big(\;R > C(P,N) \;\Longrightarrow\; \inf_{\text{codes}} P_e^{(n)} \not\to 0\;\Big).
$$

The **achievability** half is established by the random-coding argument: draw a codebook of $2^{nR}$ codewords i.i.d. from $N(0, P-\delta)^{\otimes n}$; then the average (over codebooks) probability of a decoding error under joint-typicality (or nearest-neighbour) decoding tends to $0$ whenever $R < C(P,N)$, so *some* codebook achieves vanishing error. The **converse** half is Fano's inequality combined with the sphere-packing bound: reliable decoding requires the $2^{nR}$ noise spheres of radius $\approx\sqrt{nN}$ to pack disjointly inside the output sphere of radius $\approx\sqrt{n(P+N)}$, forcing $2^{nR} \lesssim \big(\tfrac{P+N}{N}\big)^{n/2}$, i.e. $R \le C(P,N)$.

### Plain Language

The parent proof pins down the *value* of the AWGN channel capacity, $C = \tfrac12\log(1+P/N)$, as a difference of differential entropies. But it does not yet answer the operational question that makes capacity meaningful: *can we actually communicate at rate $C$ with arbitrarily small error, and is it impossible to do better?* This problem asks to formalize both directions. Achievability: if you pick your codewords at random from a Gaussian distribution, then on average the receiver can decode them almost perfectly as the block length grows — so a good code must exist. Converse: no matter how cleverly you design your code, you cannot beat $C$, because each transmitted point gets blurred by noise into a small ball, and only so many disjoint balls fit inside the region of allowable outputs.

### Why This Matters

Shannon's capacity is only a *number* until it is tied to operational rates by a coding theorem. The random-coding achievability argument and the sphere-packing / Fano converse are the two theorems that give $C = \tfrac12\log(1+P/N)$ its meaning as the fundamental limit of reliable communication over every physical (wireless, optical, deep-space) channel. Turbo, LDPC, and polar codes are all benchmarked against exactly this operational limit. Formalizing the coding theorem — not just the capacity value — closes the gap between the entropy-difference assembly in the gallery and the theorem practitioners actually cite, and it forces the measure-theoretic machinery (jointly typical sets, the AEP for continuous sources, Fano's inequality) to be built in Lean, which is reusable for every other channel.

## Known Results

### What's Already Proven

- **AWGN capacity value** $C(P,N) = \tfrac12\log(1+P/N)$ as an entropy difference — `shannon-channel-coding-awgn` (parent), theorems `awgn_capacity_achieved` (achievability of the *formula*) and `awgn_capacity_upper_bound` (max-entropy converse of the *formula*), 0 axioms / 0 sorries.
- **Gaussian differential entropy** $h(N(\mu,\sigma^2)) = \tfrac12\log(2\pi e\,\sigma^2)$ and the **maximum-entropy property** of the Gaussian at fixed variance — `shannon-entropy-oq-01` (`gaussianDifferentialEntropy`, `gaussian_max_entropy`).
- **Discrete channel capacities** and the finite-alphabet channel-coding scaffold — `shannon-channel-coding-oq-02` (BSC), `shannon-channel-coding-bec` (BEC).
- Classical mathematics of the result: Shannon (1948) states the theorem; Cover–Thomas (2006, Ch. 9) and Gallager (1968, Ch. 7–8) give the modern random-coding proof and the sphere-packing converse.

### What's Still Open

- The operational continuous-alphabet **mutual information** $I(X;Y)$ for the additive channel $Y = X + Z$ and the chain-rule identity $I(X;Y) = h(Y) - h(Z)$ are described in prose in the parent but **not** formalized.
- The variance-of-a-sum relation $\mathbb{E}[Y^2] = P + N$ for independent additive noise appears in the parent only as the converse *hypothesis* `hvar`, not as a derived fact.
- No formalization exists (in this gallery or, to our knowledge, in Mathlib) of the **jointly typical set** for continuous alphabets, the **random-coding error exponent**, or **Fano's inequality** applied to the continuous channel.

### Our Goal

Formalize the **operational coding theorem** for the AWGN channel in two self-contained pieces, keeping each honest about its assumptions:

1. **Achievability**: define a random Gaussian codebook and jointly-typical (or minimum-distance) decoding, and prove that the *expected* probability of error over the random ensemble tends to $0$ for every rate $R < C(P,N)$, hence a deterministic code with $P_e^{(n)} \to 0$ exists.
2. **Converse**: prove, via Fano's inequality plus the sphere-packing volume bound, that any sequence of codes with $P_e^{(n)} \to 0$ must have $R \le C(P,N)$.

A tractable first milestone is the **volumetric sphere-packing converse bound** $2^{nR} \le \big(\tfrac{P+N}{N}\big)^{n/2}(1+o(1))$ as an inequality on codebook cardinality given a minimum-distance separation, which is largely a Euclidean-geometry / volume argument and sidesteps the heaviest measure theory.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-channel-coding-awgn | Parent: supplies the capacity value $C=\tfrac12\log(1+P/N)$ and both entropy-difference bounds this theorem must connect to operational rates | differential entropy, Gaussian max-entropy, `Real.log` monotonicity |
| shannon-entropy-oq-01 | Provides the Gaussian entropy closed form and max-entropy theorem underpinning the AEP / typical-set volume estimates | measure theory, differential entropy, variational max-entropy |
| shannon-channel-coding-oq-02 | Sibling BSC channel; its discrete coding-theorem structure (typical sets, Fano) is the finite-alphabet analogue of the argument needed here | discrete channel capacity, entropy bounds |
| shannon-channel-coding-bec | Sibling BEC channel; erasure decoding gives a clean operational-capacity template with an exact converse | channel capacity, combinatorial decoding |
| shannon-channel-coding | Parent scaffold tying the three named channels together; the operational theorem completes the continuous-alphabet slot | channel-coding framework, capacity definitions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Geometric sphere-packing converse first (recommended entry point).** Model a length-$n$ code as a finite set $\mathcal{C} \subset \mathbb{R}^n$ with $\|c\|^2 \le nP$ and pairwise decoding regions. Under a minimum-distance / disjoint-noise-ball model, each codeword's Voronoi cell contains a ball of radius $\approx\sqrt{nN}$, and all codewords lie in a ball of radius $\approx\sqrt{n(P+N)}$; comparing Euclidean volumes ($\mathrm{vol}(B_r^n) = r^n \mathrm{vol}(B_1^n)$) yields $|\mathcal{C}| \le \big(\tfrac{\sqrt{P+N}}{\sqrt{N}}\big)^{n} = \big(1+\tfrac{P}{N}\big)^{n/2}$, i.e. $R \le C$.
   - Why it might work: Mathlib has $n$-dimensional ball volume, `MeasureTheory.Measure.addHaar` scaling, and the $r^n$ volume-scaling lemma; this is deterministic geometry, no probabilistic AEP needed.
   - Risk: bridging the *statistical* noise-ball radius (concentration of $\|Z\|^2$ around $nN$) to a clean deterministic packing statement requires a concentration inequality; a rigorous version needs the $\chi^2$ tail (Laurent–Massart), which is non-trivial in Lean.

2. **Approach B — Random-coding achievability via joint typicality.** Define the jointly-typical set $A_\varepsilon^{(n)}$ for $(X^n, Y^n)$, prove (i) the AEP so the true pair is typical w.h.p., and (ii) that an independent codeword is jointly typical with the received $Y^n$ with probability $\le 2^{-n(I(X;Y)-3\varepsilon)}$; a union bound over $2^{nR}-1$ wrong codewords gives $P_e \to 0$ when $R < I(X;Y) = C$.
   - Why it might work: mirrors the discrete BSC/BEC template already in the gallery; each step is standard and modular.
   - Risk: the continuous AEP requires the differential-entropy AEP and continuous joint-typicality, which lean heavily on measure-theoretic convergence (weak LLN for $-\tfrac1n\log f(X^n)$); this is the heaviest part and may need substantial supporting Mathlib development.

### Key Difficulties

- Formalizing the **jointly typical set** and the **asymptotic equipartition property (AEP)** for *continuous* (density-carrying) random vectors, including $-\tfrac1n\log f(X^n) \to h(X)$ in probability.
- A rigorous **concentration bound for $\|Z\|^2$** (the $\chi^2_n$ tail) to justify the "noise sphere of radius $\sqrt{nN}$" both in achievability (typical noise) and converse (packing).
- **Fano's inequality** in the continuous-output setting: $H(W \mid \hat W) \le 1 + P_e^{(n)} nR$, linking block error probability to mutual information.
- Comparing high-dimensional **Euclidean ball volumes** and getting the $\big(\tfrac{P+N}{N}\big)^{n/2}$ ratio with the $o(1)$ terms controlled.

### What Would a Proof Need?

- **Key lemma 1** (packing volume bound): if $\mathcal{C}\subset B^n_{\sqrt{n(P+N)}}$ and the balls $B^n_{\sqrt{nN}}(c)$, $c\in\mathcal{C}$, are pairwise disjoint, then $|\mathcal{C}| \le \big(\tfrac{P+N}{N}\big)^{n/2}$ — pure volume comparison.
- **Key lemma 2** ($\chi^2$ / Gaussian-norm concentration): $\Pr\big[\big|\tfrac1n\|Z^n\|^2 - N\big| > \delta\big] \to 0$ (Laurent–Massart tail), controlling the noise-sphere radius.
- **Key lemma 3** (continuous AEP): $-\tfrac1n\log f_{X^n}(X^n) \to h(X)$ in probability for i.i.d. $X_i \sim N(0,P)$, giving $|A_\varepsilon^{(n)}| \approx 2^{nh}$.
- **Key lemma 4** (Fano): $H(W\mid \hat W) \le 1 + P_e^{(n)}\log|\mathcal{W}|$, then $nR \le I(X^n;Y^n) + 1 + P_e nR$ and $I(X^n;Y^n)\le nC$ from the parent's single-letter bound.
- **Technical requirements**: a `Code (n R)` structure (encoder $\{1,\dots,2^{nR}\}\to\mathbb{R}^n$, decoder $\mathbb{R}^n\to\{1,\dots,2^{nR}\}$), average error probability, and the definition of achievable rate.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full operational coding theorem requires continuous AEP, joint typicality, Fano, and a concentration inequality — none of which currently exist in Mathlib for continuous alphabets, so substantial supporting infrastructure must be built.
- However, the **geometric sphere-packing converse bound** (Approach A / Key lemma 1) is a self-contained high-dimensional volume argument that Mathlib's Haar-measure ball-volume scaling can support, making a meaningful *partial* result realistically attainable and a good first deliverable.
- Similar structured "achievability + converse" arguments already exist in the gallery for the discrete BSC and BEC channels, giving a proven template for the code/error-probability scaffolding; the novelty is entirely in the continuous-alphabet analysis.
- The single-letter mutual-information bound $I(X^n;Y^n) \le nC$ can reuse the parent's `awgn_capacity_upper_bound`, so the converse's information-theoretic core is partly in place.

**Estimated Effort**:
- Exploration: 3–5 days to scope the Mathlib measure-theory / ball-volume API and the concentration tools.
- If tractable (geometric converse bound only): 1–2 weeks.
- If hard (full operational theorem with continuous AEP + Fano): unknown / multi-month.

## References

### Papers
- Claude E. Shannon, "A Mathematical Theory of Communication," Bell System Technical Journal 27 (1948), 379–423 & 623–656 — states the channel-coding theorem and the AWGN capacity $C=\tfrac12\log(1+P/N)$.
- Thomas M. Cover and Joy A. Thomas, "Elements of Information Theory," 2nd ed., Wiley (2006), Ch. 9 & 7 — the modern random-coding achievability, joint-typicality decoding, and the sphere-packing / Fano converse for the Gaussian channel.
- Robert G. Gallager, "Information Theory and Reliable Communication," Wiley (1968), Ch. 7–8 — rigorous coding theorems for continuous-alphabet channels, error exponents, and the sphere-packing bound.
- Beatrice Laurent and Pascal Massart, "Adaptive estimation of a quadratic functional by model selection," Annals of Statistics 28 (2000), 1302–1338 — sharp $\chi^2$ (Gaussian-norm) concentration tail used for the noise-sphere radius.
- Abbas El Gamal and Young-Han Kim, "Network Information Theory," Cambridge University Press (2011) — modern treatment of the Gaussian channel and typicality-based coding theorems.

### Mathlib
- `Mathlib.Probability.Distributions.Gaussian` — Gaussian measures and densities on $\mathbb{R}$ / $\mathbb{R}^n$, the input/noise distributions of the codebook.
- `Mathlib.MeasureTheory.Measure.Haar.NormedSpace` (`addHaar` scaling, `addHaar_ball`) — $n$-dimensional Euclidean ball volume and its $r^n$ scaling for the sphere-packing volume comparison.
- `Mathlib.Probability.Independence.Basic` and `Mathlib.Probability.Variance` — independence of noise and codewords and the $\mathbb{E}[Y^2] = P+N$ variance-of-a-sum relation.
- `Mathlib.Probability.IdentDistrib` / laws of large numbers (`Mathlib.Probability.StrongLaw`) — the LLN driving the continuous AEP for $-\tfrac1n\log f(X^n)$.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log` monotonicity for rate comparisons, as used in the parent.

## Metadata

```yaml
tags:
  - information-theory
  - probability
  - measure-theory
  - coding-theory
  - channel-capacity
  - concentration-of-measure
related_proofs:
  - shannon-channel-coding-awgn
  - shannon-entropy-oq-01
  - shannon-channel-coding-oq-02
  - shannon-channel-coding-bec
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:23:00-07:00
```
