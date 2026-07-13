# Problem: Logarithmic Correction in the Erdős–Rogers Function f(n)

**Slug**: erdos-620-oq-01
**Created**: 2026-07-09T15:22:58-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $f(n)$ denote the Erdős–Rogers function: the minimum, over all $K_4$-free graphs $G$ on $n$ vertices, of the maximum size of a triangle-free induced subgraph of $G$,
$$
f(n) \;=\; \min_{\substack{G \text{ on } n \text{ vertices}\\ G \text{ is } K_4\text{-free}}} \; \max\bigl\{\,|S| : S \subseteq V(G),\; G[S] \text{ triangle-free}\,\bigr\}.
$$
The current best bounds are
$$
c\,\frac{\sqrt{n}\,\sqrt{\log n}}{\log\log n} \;\le\; f(n) \;\le\; C\,\sqrt{n}\,\log n
\qquad (c, C > 0,\; n \ge 16).
$$
The open question is to determine the true order of the logarithmic correction: is
$$
f(n) \;=\; \Theta\!\left(\sqrt{n}\,\log n\right)
\qquad\text{or}\qquad
f(n) \;=\; \Theta\!\left(\sqrt{n}\,\sqrt{\log n}\right)\text{ (or some intermediate power of }\log n\text{)?}
$$

### Plain Language

Take any graph on $n$ vertices that contains no $K_4$ (no four mutually adjacent vertices). Inside such a graph, we look for the largest set of vertices whose induced subgraph is triangle-free. Some $K_4$-free graphs are cleverly built so that every large induced piece still contains a triangle, forcing this "largest triangle-free piece" to be small. The Erdős–Rogers function $f(n)$ is the size that is *guaranteed* no matter how adversarially the $K_4$-free graph is constructed.

We already know $f(n)$ grows like $\sqrt{n}$ times a factor that is somewhere between $\sqrt{\log n}$ and $\log n$. The question is: which end of that window is correct? Pinning down this logarithmic factor would close a gap that has resisted attack since 1962.

### Why This Matters

The $\sqrt{n}$ base growth rate is settled; the entire remaining mystery is the logarithmic correction. This is a canonical "which log power" problem in extremal combinatorics, structurally analogous to the situation for the Ramsey number $R(3,k) = \Theta(k^2/\log k)$ that Kim resolved in 1995. Resolving it would (i) reveal the structure of the extremal $K_4$-free graphs that minimize $f(n)$, (ii) test whether the regularity-free graph blowup method of Mubayi–Verstraëte (2024) is tight or merely convenient, and (iii) potentially transfer to the whole hierarchy $f_{s,t}(n)$ of generalized Erdős–Rogers functions.

## Known Results

### What's Already Proven

- **Trivial lower bound $f(n) \gg \sqrt{n}$** — independent sets in $K_4$-free graphs (Erdős–Rogers 1962). Formalized as an axiom in the parent gallery proof `erdos-620` (`Proofs/Erdos620Problem.lean`).
- **Shearer lower bound $f(n) \gg \sqrt{n}\,\sqrt{\log n}/\log\log n$** — entropy method plus dependent random choice. Axiom `shearer_lower_bound` in `erdos-620`.
- **Upper bounds progression**: Bollobás–Hind $f(n) \ll n^{7/10+o(1)}$ (1991), Krivelevich $f(n) \ll n^{2/3}(\log n)^{1/3}$ (1994), Wolfovitz $f(n) \ll \sqrt{n}(\log n)^{120}$ (2013), and Mubayi–Verstraëte $f(n) \ll \sqrt{n}\,\log n$ (2024). Axiom `mubayi_verstraete_upper` in `erdos-620`.
- **`triangleFree_implies_K4Free`** — a fully machine-checked lemma in the parent file establishing the clique-hierarchy monotonicity underlying the problem.
- **`gap_analysis` / `current_bounds`** — Lean proofs combining the Shearer and Mubayi–Verstraëte axioms into the explicit sandwich inequality for $n \ge 16$.

### What's Still Open

- The exact exponent $\alpha$ of the logarithmic correction $f(n) = \Theta(\sqrt{n}\,(\log n)^\alpha)$ with $1/2 \le \alpha \le 1$ (up to $\log\log n$ factors).
- Whether the Mubayi–Verstraëte $\sqrt{n}\log n$ construction is asymptotically optimal, i.e. whether the upper bound can be improved to $\sqrt{n}(\log n)^{1-\varepsilon}$.
- The structure of the extremal minimizing $K_4$-free graphs (algebraic / pseudorandom?).

### Our Goal

We do **not** attempt to resolve the open question. Instead, the formalizable target is a *conditional dichotomy / gap-narrowing* result: assuming the two boundary axioms already present in `erdos-620`, prove in Lean the explicit statement that the ratio of the two candidate growth rates is exactly the slowly-growing factor $\sqrt{\log n}\cdot\log\log n$, and formalize the conditional implication

> *If* $f(n) \le C\sqrt{n}(\log n)^{1-\varepsilon}$ for some fixed $\varepsilon > 0$ and all large $n$ (an improved upper bound), *then* $f(n) = o(\sqrt{n}\log n)$, ruling out $\Theta(\sqrt{n}\log n)$.

Concretely: (1) a Lean definition of the candidate asymptotic classes $\mathrm{UpperClass}(n)=\sqrt{n}\log n$ and $\mathrm{LowerClass}(n)=\sqrt{n}\sqrt{\log n}$, (2) a proof that $\mathrm{UpperClass}/\mathrm{LowerClass} = \sqrt{\log n}$ tends to infinity (so the classes are genuinely distinct), and (3) the conditional dichotomy theorem stated above, discharged from the parent's axioms plus the hypothesized improved bound.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-620 | Direct parent: defines $f(n)=$ `erdosRogers n`, axiomatizes Shearer and Mubayi–Verstraëte bounds, proves `gap_analysis`. This problem refines the log-factor sub-question. | Induced subgraphs, `CliqueFree`, `Real.sqrt`/`Real.log`, minimax definitions |
| ramseys-theorem | $f(n)$ generalizes independent sets in $K_4$-free graphs; the lower bound is controlled by $R(3,k)=\Theta(k^2/\log k)$ (Kim). | Ramsey numbers, probabilistic existence, pigeonhole |
| erdos-1010 | Triangle supersaturation is the dual: #620 asks how much triangle structure must survive under a $K_4$-avoidance constraint. | Counting triangles, extremal density arguments |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Asymptotic-class separation + conditional dichotomy.** Define the two candidate growth functions as real-valued functions of $n$ and prove, using Mathlib's `Real.log` / `Filter.Tendsto` / `Asymptotics.IsLittleO` machinery, that $\sqrt{n}\sqrt{\log n} = o(\sqrt{n}\log n)$ via $\sqrt{\log n}/\log n \to 0$. Then state the dichotomy as a clean Lean theorem conditioned on the parent axioms and a hypothesized improved upper bound.
   - Why it might work: the analytic core reduces to $(\log n)^{1/2}/\log n \to 0$, entirely within Mathlib's asymptotics library; no new combinatorics is required. It is genuinely provable, unlike the open question itself.
   - Risk: careful handling of `Real.sqrt` monotonicity and `log` positivity domains ($n \ge 2$) can generate fiddly side goals; must avoid accidentally encoding the open resolution as an axiom (axiom-integrity policy).

2. **Approach B — Formalize the Shearer/Mubayi–Verstraëte ratio explicitly.** Prove that the ratio of the *proven* upper and lower bounds equals $\sqrt{\log n}\cdot\log\log n$ (up to constants) and that this ratio is unbounded, formalizing the precise "size of the remaining gap" as a theorem rather than prose.
   - Why it might work: it turns the qualitative "$(\log n)^{1/2}\log\log n$ gap" claim from the parent overview into a checked inequality, a self-contained analytic result.
   - Risk: the $\log\log n$ term requires $n$ large enough for $\log\log n > 0$ (roughly $n > e$); domain bookkeeping and the interaction of three nested logs may be delicate.

### Key Difficulties

- The underlying mathematical question is genuinely open, so any *unconditional* determination of $\alpha$ is off-limits; the formal target must be conditional or a gap-quantification result.
- Axiom-integrity: the parent already carries `shearer_lower_bound` and `mubayi_verstraete_upper` as axioms; new work must not silently add an axiom that "decides" the answer.
- Analytic side-conditions on `Real.log`/`Real.sqrt` (positivity, monotonicity, domain $n \ge 2$) must be discharged rather than assumed.

### What Would a Proof Need?

- Key lemma 1: `sqrt (log n) =o[atTop] log n`, i.e. $\lim_{n\to\infty}\sqrt{\log n}/\log n = 0$, established via `Real.log` growth and `Real.sqrt` estimates (`Asymptotics.IsLittleO`, `Filter.Tendsto.comp`).
- Key lemma 2: distinctness of the candidate classes — $\sqrt{n}\log n / (\sqrt{n}\sqrt{\log n}) = \sqrt{\log n} \to \infty$ (`Filter.Tendsto ... atTop`).
- Key lemma 3: the conditional dichotomy — from the parent axioms plus `f n ≤ C * sqrt n * (log n)^(1-ε)`, derive `f n =o[atTop] (fun n => sqrt n * log n)`, hence $f \ne \Theta(\sqrt{n}\log n)$.
- Technical requirements: `Real.sqrt`, `Real.log`, `Filter.atTop`, `Asymptotics.IsLittleO`, `Asymptotics.IsBigO`, monotonicity/positivity lemmas for logs and square roots.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The full open problem is a Moonshot, but the *formalizable target here* (asymptotic-class separation and a conditional dichotomy) is a self-contained real-analysis exercise on top of an existing, well-structured parent file.
- Mathlib has mature support for exactly the needed pieces: `Asymptotics.IsLittleO`, `Filter.Tendsto ... atTop`, and log/sqrt growth lemmas, all previously used in gallery analysis proofs.
- The parent proof `erdos-620` already provides the definitions and the two boundary axioms, so scaffolding cost is low; the risk is concentrated in analytic side-goals, not in conceptual gaps.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1 week
- If hard: unknown (only if one over-scopes toward the open question)

## References

### Papers
- P. Erdős and C. A. Rogers, "The construction of certain graphs," *Canadian Journal of Mathematics* / *Mathematika* 9 (1962), 111–114 — original posing of the problem.
- B. Bollobás and H. R. Hind, "Graphs without large triangle-free subgraphs," *Discrete Mathematics* 87 (1991), 119–131 — first non-trivial upper bound $n^{7/10+o(1)}$.
- M. Krivelevich, "Bounding Ramsey numbers through large deviation inequalities," *Random Structures & Algorithms* 7 (1995) — related bound $n^{2/3}(\log n)^{1/3}$.
- J. B. Shearer, "A note on the independence number of triangle-free graphs," *Discrete Mathematics* 46 (1983), 83–87 — entropy method underlying the lower bound.
- G. Wolfovitz, "$K_4$-free graphs without large induced triangle-free subgraphs," *Combinatorica* 33 (2013), 623–631 — bound $\sqrt{n}(\log n)^{120}$.
- D. Mubayi and J. Verstraëte, "A note on the Erdős–Rogers function," 2024 — current best upper bound $\sqrt{n}\log n$ via regularity-free blowups.
- J. H. Kim, "The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$," *Random Structures & Algorithms* 7 (1995), 173–207 — the closely related Ramsey asymptotics.

### Online Resources
- https://erdosproblems.com/620 — Erdős Problem #620 statement, status, and bound history.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Clique` — `SimpleGraph.CliqueFree`, for the $K_4$-free / triangle-free predicates.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log` and its monotonicity/positivity lemmas.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` / `Mathlib.Analysis.SpecialFunctions.Sqrt` — `Real.sqrt` and real powers for the growth-rate functions.
- `Mathlib.Analysis.Asymptotics.Asymptotics` — `IsLittleO`, `IsBigO` for the class-separation and dichotomy statements.
- `Mathlib.Order.Filter.AtTopBot` — `Filter.atTop` and `Tendsto` for the limits.

## Metadata

```yaml
tags:
  - graph-theory
  - ramsey-theory
  - induced-subgraphs
  - extremal-graph-theory
related_proofs:
  - erdos-620
  - ramseys-theorem
  - erdos-1010
difficulty: medium
source: proof-suggestion
created: 2026-07-09T15:22:58-07:00
```
