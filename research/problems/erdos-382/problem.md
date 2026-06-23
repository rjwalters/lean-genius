# Problem: Erdős #382

## Statement

### Plain Language
Let $u\leq v$ be such that the largest prime dividing $\prod_{u\leq m\leq v}m$ appears with exponent at least $2$. Is it true that $v-u=v^{o(1)}$? Can $v-u$ be arbitrarily large?



Erd\H{o}s and Graham report it follows from results of Ramachandra that $v-u\leq v^{1/2+o(1)}$.

Cambie has observed that the first question boils down to some old conjectures on prime gaps.
By Cram\'{er's conjecture}, for every $\epsilon>0,$ ...


### Formal Statement
$$
Let $u\leq v$ be such that the largest prime dividing $\prod_{u\leq m\leq v}m$ appears with exponent at least $2$. Is it true that $v-u=v^{o(1)}$? Can $v-u$ be arbitrarily large?



Erd\H{o}s and Graham report it follows from results of Ramachandra that $v-u\leq v^{1/2+o(1)}$.

Cambie has observed that the first question boils down to some old conjectures on prime gaps.
By Cram\'{er's conjecture}, for every $\epsilon>0,$ for every $u$ sufficiently large there is a prime between $u$ and $u+u^\epsilon$.
Thus for $u+u^\epsilon<v$, the largest prime divisor of \( \prod_{u \leq m \leq v} m \) appears with exponent $1$.
Since this is not the case in the question, \( v - u = v^{o(1)} \).

Cambie also gives the following heuristic for the second question. The 'probability' that the largest prime divisor of $n$ is $<n^{1/2}$ is $1-\log 2>0$. For any fixed $k$, there is therefore a positive 'probability' that there are $k$ consecutive integers around $q^2$ (for a prime $q$) all of whose prime divisors are bounded above by $q$, when $v-u\geq k$. See [383] for a conjecture along these lines. A similar argument applies if we replace multiplicity $2$ with multiplicity $r$, for any fixed $r\geq 2$.

See also [380].
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 382
erdosUrl: https://erdosproblems.com/382

tags:
  - erdos
```

**Significance**: 6/10
**Tractability**: 4/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - open problem


## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #1998](https://www.erdosproblems.com/1998)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #383](https://www.erdosproblems.com/383)
- [Problem #380](https://www.erdosproblems.com/380)
- [Problem #381](https://www.erdosproblems.com/381)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [ErGr80]

## OEIS Sequences

- [A388850](https://oeis.org/A388850)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
