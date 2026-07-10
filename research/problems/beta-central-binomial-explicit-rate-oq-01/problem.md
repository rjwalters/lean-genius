# Problem: A Sharp Effective Constant for the Diagonal Beta Correction Rate

**Slug**: beta-central-binomial-explicit-rate-oq-01
**Created**: 2026-07-09T17:03:07-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $q(n) = B(n+1,n+1)/T(n)$ be the multiplicative correction of the diagonal
Euler Beta value relative to its Wallis/Stirling leading term
$T(n) = \sqrt{\pi n}/((2n+1)\,4^n)$. The parent proof establishes the effective
Landau bound $|q(n) - 1| \le 3/n$. The question is whether the constant $3$ can
be replaced by a smaller, ultimately sharp, effective constant:

$$
\text{Find the smallest } C \text{ and the sharp first-order coefficient } c_1 \text{ so that } \quad q(n) - 1 = \frac{c_1}{n} + O\!\left(\frac{1}{n^2}\right), \qquad |q(n) - 1| \le \frac{C}{n} \ \ (n \ge n_0), \qquad c_1 = \tfrac{1}{8}.
$$

Concretely: prove an effective bound $|q(n) - 1| \le C/n$ with $C$ strictly below
the current $3$ (ideally $C \to 1/8$ as $n\to\infty$), and identify
$c_1 = \lim_{n\to\infty} n\,(q(n)-1)$ as the true first-order coefficient.

### Plain Language

The parent entry proves the diagonal Beta value $B(n+1,n+1)$ agrees with its
leading term to within a relative error of at most $3/n$. The constant $3$ was
chosen for convenience — it comes from cheap exponential inequalities applied to a
two-sided bracket, not from the actual size of the error. The genuine leading
behaviour of the correction is $q(n) - 1 \approx \frac{1}{8n}$, so the true error
is roughly $24$ times smaller than the certified bound. This problem asks to close
that gap: prove an honest, machine-checked constant that approaches the sharp
value $1/8$, and pin down $1/8$ as the exact first-order coefficient.

### Why This Matters

The parent result is advertised as an *effective* rate, but its constant is a
loose over-estimate. A sharp constant turns the bound from "correct in order" into
"correct in magnitude", making it directly usable as a numerical error bar — for
example when bounding the normalising constant of a symmetric $\mathrm{Beta}(n+1,n+1)$
prior or the mass of the density $t^n(1-t)^n$. It also validates the parent's own
stated open question and demonstrates that the telescoping Stirling-tail machinery
can be pushed from an $O(1/n)$ envelope to a sharp leading coefficient.

## Known Results

### What's Already Proven

- **Effective two-sided bracket** — `betaDiag_correction_bracket` in
  `Proofs/BetaCentralBinomialExplicitRate.lean`: for $n \ge 2$,
  $\exp(-1/(4(2n-1))) \le q(n) \le \exp(1/(2(n-1)))$.
- **Landau form with constant 3** — `betaDiag_correction_isBigO`:
  $(q(n) - 1) = O(1/n)$ with explicit constant $3$.
- **Stirling tail bound** — `log_stirlingSeq_sub_sqrt_pi_le`:
  $\log\mathrm{stirlingSeq}(m+1) - \log\sqrt\pi \le 1/(4m)$, telescoped from
  Mathlib's per-step $O(1/m^2)$ estimate.
- **Mathlib's qualitative Stirling limit** — `Stirling.tendsto_stirlingSeq_sqrt_pi`
  gives $\mathrm{stirlingSeq}(k) \to \sqrt\pi$, and
  `Stirling.stirlingSeq'_antitone` / lower bound $\sqrt\pi \le \mathrm{stirlingSeq}(k)$.

### What's Still Open

- The **sharp effective constant**: no bound of the form $|q(n)-1| \le C/n$ with
  $C < 3$ is currently proven; the true infimum of admissible constants (large $n$)
  is $c_1 = 1/8$.
- The **exact first-order coefficient** $c_1 = \lim_{n} n(q(n)-1) = 1/8$ is not
  formalized, only heuristically identified from the classical expansion
  $\log\mathrm{stirlingSeq}(k) = \log\sqrt\pi + \tfrac{1}{12k} - \tfrac{1}{360k^3} + \cdots$.

### Our Goal

Formalize $c_1 = 1/8$ as the true first-order coefficient of $q(n) - 1$, i.e.
$n(q(n)-1) \to 1/8$, **and** upgrade the effective bound to $|q(n)-1| \le C/n$ for
an explicit $C$ strictly below $3$ (a first milestone: any $C \le 1$; the target:
$C$ arbitrarily close to $1/8$ for large $n$). Deriving the coefficient from a
two-sided *matching* Stirling expansion is the crux.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| beta-central-binomial-explicit-rate | Parent entry; supplies $q(n)$, the bracket, and the loose constant $3$ to be improved | Stirling tail bound, telescoping, log-bracket, `IsBigO` |
| beta-central-binomial-asymptotic | Establishes the bare asymptotic $B(n+1,n+1) \sim \sqrt{\pi n}/((2n+1)4^n)$ underlying $q(n)\to 1$ | Wallis product, Stirling limit |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Sharpen the tail bound to a two-sided $\pm\,1/(12m) + O(1/m^2)$
   window.** Replace the one-sided envelope $\log\mathrm{stirlingSeq}(m+1) - \log\sqrt\pi \le 1/(4m)$
   with the matching pair $\tfrac{1}{12(m+1)} - \tfrac{C'}{m^2} \le \log\mathrm{stirlingSeq}(m) - \log\sqrt\pi \le \tfrac{1}{12m}$,
   using Robbins-type explicit Stirling inequalities. Feeding indices $n$ and $2n$
   into $\log q(n) = 2\Delta(n) - \Delta(2n)$ gives
   $\log q(n) = \tfrac{2}{12n} - \tfrac{1}{12\cdot 2n} + O(1/n^2) = \tfrac{1}{8n} + O(1/n^2)$.
   - Why it might work: the $1/(12m)$ constant is classical and the parent already
     telescopes the per-step estimate; only the *lower* per-step direction is new.
   - Risk: Mathlib may not package a per-step lower bound of matching quality, so
     the sharp lower telescoping term may need to be built from scratch.

2. **Approach B — Robbins bounds directly on $q(n)$.** Use Robbins' effective
   factorial inequalities $\sqrt{2\pi n}(n/e)^n e^{1/(12n+1)} \le n! \le \sqrt{2\pi n}(n/e)^n e^{1/(12n)}$
   to bracket $C(2n,n)$ and hence $q(n)$ directly, bypassing $\mathrm{stirlingSeq}$.
   - Why it might work: Robbins bounds give explicit two-sided exponents in one
     step, immediately yielding $|q(n)-1| \le C/n$ with a small $C$.
   - Risk: Robbins' inequalities are not in Mathlib in this exact form and would
     have to be formalized or reconstructed from the monotone `stirlingSeq` data.

### Key Difficulties

- Mathlib's Stirling API is *one-sided and qualitative*: it gives monotonicity and
  the limit but no packaged sharp two-sided rate; the $1/(12m)$ coefficient must be
  extracted, not cited.
- Converting a log-bracket into a bound on $q(n)-1$ (not $\log q(n)$) with a sharp
  constant requires careful control of the $\exp x - 1 = x + O(x^2)$ remainder, not
  just the convex over-estimates $1-x\le e^{-x}$ used in the parent.
- The limit $n(q(n)-1)\to 1/8$ needs the *second*-order Stirling term to be
  controlled uniformly, or an `IsLittleO` remainder argument.

### What Would a Proof Need?

- Key lemma 1: a two-sided per-index Stirling estimate
  $|\log\mathrm{stirlingSeq}(m) - \log\sqrt\pi - \tfrac{1}{12m}| \le C'/m^2$.
- Key lemma 2: the identity $\log q(n) = 2\Delta(n) - \Delta(2n)$ with
  $\Delta(k) = \log\mathrm{stirlingSeq}(k) - \log\sqrt\pi$ (parent has `log_correction_eq`).
- Key lemma 3: $n\,\log q(n) \to 1/8$ and $\exp$-remainder control giving
  $n(q(n)-1)\to 1/8$.
- Technical requirements: `Filter.Tendsto`, `Asymptotics.IsBigO`/`IsLittleO`,
  `Real.exp`/`Real.log` estimates, and the parent file's Stirling lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The heuristic coefficient $1/8$ is unambiguous and the algebraic reduction to
  Stirling deviations is already done in the parent file.
- The main new ingredient — a matching lower per-step Stirling estimate — is a
  finite refinement of machinery the parent already uses, not a new theory.
- Robbins-type bounds are standard and have appeared in comparable Mathlib-adjacent
  formalizations; the second-order remainder is the only genuinely delicate step.
- A partial result (any $C < 3$, e.g. $C = 1$) is Low difficulty and a good first
  milestone; the fully sharp $C \to 1/8$ with the limit is Medium.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks
- If hard: unknown (if a sharp lower Stirling tail must be built from scratch)

## References

### Papers
- H. Robbins, "A Remark on Stirling's Formula", *Amer. Math. Monthly* 62 (1955),
  26–29 — the explicit two-sided factorial bounds $e^{1/(12n+1)}$ / $e^{1/(12n)}$.
- E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen* (1909) — origin
  of the $O(\cdot)$ notation used in the rate statement.

### Online Resources
- https://en.wikipedia.org/wiki/Stirling%27s_approximation — the asymptotic series
  $\log n! = n\log n - n + \tfrac12\log(2\pi n) + \tfrac{1}{12n} - \cdots$ giving the
  $1/(12k)$ leading correction and hence the $1/8$ coefficient.
- https://dlmf.nist.gov/5.11 — DLMF asymptotic expansions of the Gamma and Beta
  functions, including the diagonal Beta ratio.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Stirling` — `stirlingSeq`, its monotonicity,
  the lower bound $\sqrt\pi \le \mathrm{stirlingSeq}(k)$, and the limit $\to \sqrt\pi$.
- `Mathlib.Analysis.SpecialFunctions.Gamma.Beta` — the Euler Beta integral and its
  reduction to central binomial coefficients.
- `Mathlib.Analysis.Asymptotics.Asymptotics` — `IsBigO`, `IsLittleO` for the Landau
  statement and the sharp-coefficient limit.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` and `.../Exp` — the $\log$/$\exp$
  estimates converting the log-bracket into a bound on $q(n)-1$.

## Metadata

```yaml
tags:
  - analysis
  - asymptotics
  - beta-function
  - stirling
  - central-binomial
  - landau-notation
  - research
related_proofs:
  - beta-central-binomial-explicit-rate
  - beta-central-binomial-asymptotic
difficulty: medium
source: gallery-gap
created: 2026-07-09T17:03:07-07:00
```
