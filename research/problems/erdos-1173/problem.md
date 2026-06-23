# Problem: Erdős #1173 — Free Sets for Set Mappings under GCH

## Statement

### Plain Language

Under the Generalized Continuum Hypothesis, suppose every ordinal below
ω_{ω+1} is assigned a set of size at most ℵ_ω, and any two of these
assigned sets share strictly fewer than ℵ_ω elements. Must there exist
a "free" set of size ℵ_{ω+1} — that is, a set S in which no element of
S belongs to the assigned set of any other element of S?

### Formal Statement

$$
\text{GCH} \implies \forall f : \omega_{\omega+1} \to [\omega_{\omega+1}]^{\le \aleph_\omega},\
  \bigl(\forall \alpha \ne \beta,\ |f(\alpha) \cap f(\beta)| < \aleph_\omega\bigr)
  \implies \exists S \subseteq \omega_{\omega+1},\ |S| = \aleph_{\omega+1}\
   \land\ (\forall \alpha \ne \beta \in S,\ \alpha \notin f(\beta)).
$$

## Classification

```yaml
tier: B
significance: 7
tractability: 6
erdosNumber: 1173
erdosUrl: https://erdosproblems.com/1173

tags:
  - erdos
  - set-theory
  - infinitary-combinatorics
  - singular-cardinals
  - free-sets
  - GCH
```

**Significance**: 7/10
**Tractability**: 6/10 (open Erdős–Hajnal problem; partial formalization possible)

## Why This Matters

1. **Erdős–Hajnal legacy** — Part of the classical Erdős–Hajnal program on set mappings and free sets in infinitary combinatorics.
2. **Singular vs. regular dichotomy** — The Hajnal free set theorem handles regular κ via standard combinatorial arguments. Whether an analogue holds for the singular cardinal ℵ_ω with the weaker almost-disjoint intersection hypothesis is unresolved.
3. **PCF connection** — Resolution would inform the PCF-theoretic structure of [κ]^{<κ} when κ is singular, and connect to Shelah's work on cofinalities of products of regular cardinals.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| (none yet — this is a standalone problem statement) | — |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- Erdős, P. & Hajnal, A. — original problem on set mappings and free sets
- Komjáth, P. (Ko25b), Problem 35
- Vaughan, J. (Va99), 7.88

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
