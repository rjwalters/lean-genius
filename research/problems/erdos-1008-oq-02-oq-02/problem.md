# Problem: Explicit Closed-Form ex(n; K₂,ₜ) from the Kővári–Sós–Turán Quadratic

**Slug**: erdos-1008-oq-02-oq-02
**Created**: 2026-07-09T16:43:20-07:00
**Status**: Active
**Source**: user-request

## Problem Statement

### Formal Statement

$$
\text{For fixed } t \ge 2,\ \text{a } K_{2,t}\text{-free graph } G \text{ on } n \text{ vertices with } m \text{ edges satisfies the Kővári–Sós–Turán quadratic } 4m^2 \le (t-1)\,n^2(n-1) + 2nm,\ \text{whence } m \le \tfrac14\,n\bigl(1 + \sqrt{\,1 + 4(t-1)(n-1)\,}\bigr).
$$

### Plain Language

The parent entry solved the quadratic inequality that bounds the edges of a graph containing no 4-cycle (equivalently, no $K_{2,2}$), turning the implicit bound $4m^2 \le n^2(n-1) + 2nm$ into the explicit Reiman form $m \le \tfrac14 n(1+\sqrt{4n-3})$. This problem asks for the same explicit form one step more general: for a graph that contains no $K_{2,t}$ (no two vertices with $t$ common neighbours), the Kővári–Sós–Turán counting argument produces a quadratic $4m^2 \le (t-1)n^2(n-1) + 2nm$ with the parameter $t-1$ in front, and we want to solve it to get a clean closed form $m \le \tfrac14 n(1 + \sqrt{1 + 4(t-1)(n-1)})$. The goal is to prove, in Lean 4, a single parametric lemma that recovers the sharp upper root of this $t$-dependent quadratic and specializes back to the $C_4$ case when $t=2$.

### Why This Matters

$K_{2,t}$-free extremal numbers are the next rung of the Zarankiewicz ladder above $C_4$: Kővári, Sós and Turán (1954) give $\text{ex}(n;K_{2,t}) \le \tfrac12\bigl(\sqrt{t-1}\,n^{3/2} + n\bigr)$, and Füredi (1996) showed this is asymptotically tight, $\text{ex}(n;K_{2,t}) = \tfrac12\sqrt{t-1}\,n^{3/2}(1+o(1))$. Having the exact solved quadratic in a machine-checked form gives the precise finite-$n$ constant rather than an asymptotic estimate, and it demonstrates that the parent's sqrt-free quadratic-solving mechanism generalizes verbatim to a whole family of extremal problems. It also feeds directly into Erdős #1008, whose density thresholds are governed by exactly these $K_{s,t}$-avoidance bounds.

## Known Results

### What's Already Proven

- `Erdos1008.kovari_sos_turan` (parent #1008 formalization) — the $C_4$/$K_{2,2}$ quadratic $4m^2 \le n^2(n-1) + 2nm$, proved axiom-free.
- `reiman_quadratic_solve` (gallery proof `erdos-1008-oq-02`) — solves that quadratic to $4m \le n(1+s)$ with $s^2 = 4n-3$, via a sign case split on $4m-n$.
- `reiman_root_exact` (gallery proof `erdos-1008-oq-02`) — certifies $\tfrac14 n(1+s)$ is a genuine root, $4R^2 = n^2(n-1)+2nR$.

### What's Still Open

- The $t$-parametric quadratic $4m^2 \le (t-1)n^2(n-1) + 2nm$ has not been solved to explicit closed form in Lean.
- The general discriminant $s^2 = 1 + 4(t-1)(n-1)$ (which reduces to $4n-3$ at $t=2$) is not yet formalized as a reusable identity.
- The counting derivation of the $K_{2,t}$ quadratic itself (bounding $\sum_v \binom{\deg v}{2} \le (t-1)\binom{n}{2}$) is not part of the parent scope.

### Our Goal

Formalize a single parametric lemma `kst_quadratic_solve` generalizing `reiman_quadratic_solve`: for reals $m,n,s\ge 0$ with $n\ge 1$, a parameter $c = t-1 \ge 1$, and $s^2 = 1 + 4c(n-1)$ together with the hypothesis $4m^2 \le c\,n^2(n-1) + 2nm$, prove $4m \le n(1+s)$. Then specialize to $c=1$ to recover the parent's Reiman bound and check the discriminant collapses to $4n-3$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1008-oq-02 | Direct parent: solves the $t=2$ ($C_4$) case of exactly this quadratic; the target generalizes its `reiman_quadratic_solve` lemma | Sqrt-free quadratic solving, sign case split on $4m-n$, `nlinarith`, `Real.sq_sqrt` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Parametrize the existing sign-split proof**: Copy the structure of `reiman_quadratic_solve` but carry a coefficient $c = t-1$. From $s^2 = 1 + 4c(n-1)$ and $4m^2 \le c\,n^2(n-1)+2nm$, derive $(4m-n)^2 = 16m^2 - 8mn + n^2 \le 4c\,n^2(n-1) + n^2 = n^2(1+4c(n-1)) = (ns)^2$, then case split on the sign of $4m-n$ using $n\ge 1, c\ge 1 \Rightarrow s\ge 1 \Rightarrow ns\ge n$.
   - Why it might work: the algebra is identical to the parent up to the constant $c$; `nlinarith` handled the $c=1$ case and the extra multiplicative parameter stays polynomial.
   - Risk: `nlinarith` may need explicit product hints (e.g. `mul_nonneg`, the term $c\cdot n^2(n-1)$) once $c$ is a free variable rather than the literal $1$.

2. **Approach B — Reduce to the parent by rescaling**: Attempt to substitute $m' = m/\sqrt{c}$ or absorb $c$ into $n$ to reuse `reiman_quadratic_solve` as a black box.
   - Why it might work: would give the result with almost no new algebra if a clean substitution exists.
   - Risk: the quadratic $4m^2 \le c n^2(n-1) + 2nm$ is not homogeneous in a way that cleanly rescales (the linear term $2nm$ has no $c$), so a direct reduction likely fails; better used only as a sanity cross-check at $t=2$.

### Key Difficulties

- Confirming the exact shape of the $K_{2,t}$ quadratic: the standard KST count gives $\sum_v \binom{\deg v}{2} \le (t-1)\binom{n}{2}$, and turning this into $4m^2 \le (t-1)n^2(n-1)+2nm$ requires convexity ($\sum \binom{\deg v}{2} \ge n\binom{2m/n}{2}$); the sign/constant must match the parent's normalization at $t=2$.
- Keeping the core lemma sqrt-free: as in the parent, all analytic input ($s\ge 0$, $s^2 = 1+4c(n-1)$) should be isolated so the algebraic core stays constructive and `nlinarith`-friendly.
- Providing `nlinarith` with the right degree hints once $c$ is symbolic; the parent relied on the concrete discriminant $4n-3$.

### What Would a Proof Need?

- Key lemma 1: `kst_quadratic_solve` — the parametric upper-root extraction $4m \le n(1+s)$ from $4m^2 \le c n^2(n-1)+2nm$ and $s^2 = 1+4c(n-1)$, $c\ge 1$, $n\ge 1$, $s\ge 0$.
- Key lemma 2: `kst_root_exact` — $4R^2 = c\,n^2(n-1)+2nR$ at $R = \tfrac14 n(1+s)$, generalizing `reiman_root_exact`.
- Technical requirements: a specialization corollary at $c=1$ reproducing `reiman_quadratic_solve`, and the identity check $1 + 4\cdot1\cdot(n-1) = 4n-3$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent already proved the $t=2$ instance with a short, robust proof; introducing the parameter $c=t-1$ is a modest generalization of a working argument.
- The algebraic core is a single one-variable quadratic; `nlinarith` and a sign case split suffice, as demonstrated in `erdos-1008-oq-02`.
- The main uncertainty is the graph-theoretic derivation of the $K_{2,t}$ quadratic (convexity of the common-neighbour count), which may be scoped as an assumption if a full formalization is out of reach — mirroring how the parent took `Erdos1008.kovari_sos_turan` as given input.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: several days to a week
- If hard: unknown (chiefly if the KST counting step is formalized from scratch)

## References

### Papers
- Kővári, Sós, Turán, "On a problem of K. Zarankiewicz", Colloq. Math. 3 (1954) — the general density bound giving the $K_{2,t}$ quadratic.
- Reiman, "Über ein Problem von K. Zarankiewicz", Acta Math. Acad. Sci. Hungar. 9 (1958) — the exact $C_4$ ($t=2$) closed form solved by the parent.
- Füredi, "New asymptotics for bipartite Turán numbers", J. Combin. Theory Ser. A 75 (1996) — asymptotic tightness $\text{ex}(n;K_{2,t}) = \tfrac12\sqrt{t-1}\,n^{3/2}(1+o(1))$.

### Online Resources
- https://erdosproblems.com/1008 — Erdős Problem #1008, the parent open question.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Pow.NNReal` / `Real.sqrt` (`Real.sq_sqrt`, `Real.sqrt_nonneg`) — supplies the analytic facts $s = \sqrt{1+4c(n-1)} \ge 0$ and $s^2 = 1+4c(n-1)$.
- `Mathlib.Tactic.Linarith` / `nlinarith` — discharges the polynomial quadratic inequality after the discriminant identity is in hand.
- `Mathlib.Combinatorics.SimpleGraph.Basic` and `Mathlib.Combinatorics.DoubleCounting` — the graph framework and double-counting lemmas underlying the KST derivation.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - extremal
  - cycles
  - zarankiewicz
  - kovari-sos-turan
  - reiman
  - c4-free
related_proofs:
  - erdos-1008-oq-02
difficulty: medium
source: user-request
created: 2026-07-09T16:43:20-07:00
```
