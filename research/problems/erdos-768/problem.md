# Problem: Erdős #768

## Statement

### Plain Language
Let $A\subset\mathbb{N}$ be the set of $n$ such that for every prime $p\mid n$ there exists some $d\mid n$ with $d>1$ such that $d\equiv 1\pmod{p}$. Is it true that there exists some constant $c>0$ such that for all large $N$\[\frac{\lvert A\cap [1,N]\rvert}{N}=\exp(-(c+o(1))\sqrt{\log N}\log\log N).\]



Erd\H{o}s could prove that there exists some constant $c>0$ such that for all large $N$\[\exp(-c\sqrt{\log N}\log\log ...


### Formal Statement
$$
Let $A\subset\mathbb{N}$ be the set of $n$ such that for every prime $p\mid n$ there exists some $d\mid n$ with $d>1$ such that $d\equiv 1\pmod{p}$. Is it true that there exists some constant $c>0$ such that for all large $N$\[\frac{\lvert A\cap [1,N]\rvert}{N}=\exp(-(c+o(1))\sqrt{\log N}\log\log N).\]



Erd\H{o}s could prove that there exists some constant $c>0$ such that for all large $N$\[\exp(-c\sqrt{\log N}\log\log N)\leq \frac{\lvert A\cap [1,N]\rvert}{N}\]and\[\frac{\lvert A\cap [1,N]\rvert}{N}\leq \exp(-(1+o(1))\sqrt{\log N\log\log N}).\]Erd\H{o}s asked about this because $\lvert A\cap [1,N]\rvert$ provides an upper bound for the number of integers $n\leq N$ for which there is a non-cyclic simple group of order $n$.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 768
erdosUrl: https://erdosproblems.com/768

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
- [Problem #767](https://www.erdosproblems.com/767)
- [Problem #769](https://www.erdosproblems.com/769)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er74b]

## OEIS Sequences

- [A001034](https://oeis.org/A001034)
- [A352287](https://oeis.org/A352287)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
