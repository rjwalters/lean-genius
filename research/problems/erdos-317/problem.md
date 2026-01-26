# Problem: Erdős #317

## Statement

### Plain Language
Is there some constant $c>0$ such that for every $n\geq 1$ there exists some $\delta_k\in \{-1,0,1\}$ for $1\leq k\leq n$ with\[0 \frac{1}{[1,\ldots,n]}\]whenever the left-hand side is not zero?



Inequality is obvious for the second claim, the problem is strict inequality. This fails for small $n$, for example\[\frac{1}{2}-\frac{1}{3}-\frac{1}{4}=-\frac{1}{12}.\]Arguments of Kovac and van Doorn in the comment section pr...


### Formal Statement
$$
Is there some constant $c>0$ such that for every $n\geq 1$ there exists some $\delta_k\in \{-1,0,1\}$ for $1\leq k\leq n$ with\[0< \left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert < \frac{c}{2^n}?\]Is it true that for sufficiently large $n$, for any $\delta_k\in \{-1,0,1\}$,\[\left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert > \frac{1}{[1,\ldots,n]}\]whenever the left-hand side is not zero?



Inequality is obvious for the second claim, the problem is strict inequality. This fails for small $n$, for example\[\frac{1}{2}-\frac{1}{3}-\frac{1}{4}=-\frac{1}{12}.\]Arguments of Kovac and van Doorn in the comment section prove a weak version of the first question, with an upper bound of\[2^{-n\frac{(\log\log\log n)^{1+o(1)}}{\log n}},\]and van Doorn gives a heuristic that suggests this may be the true order of magnitude.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 317
erdosUrl: https://erdosproblems.com/317

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
- [Problem #316](https://www.erdosproblems.com/316)
- [Problem #318](https://www.erdosproblems.com/318)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

(No references available)

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
