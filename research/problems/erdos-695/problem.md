# Problem: Erdős #695

## Statement

### Plain Language
Let $p_1<p_2<\cdots$ be a sequence of primes such that $p_{i+1}\equiv 1\pmod{p_i}$. Is it true that\[\lim_k p_k^{1/k}=\infty?\]Does there exist such a sequence with\[p_k \leq \exp(k(\log k)^{1+o(1)})?\]



Such a sequence is sometimes called a prime chain.

If we take the obvious 'greedy' chain with $2=p_1$ and $p_{i+1}$ is the smallest prime $\equiv 1\pmod{p_i}$ then Linnik's theorem implies that this sequence grows like...


### Formal Statement
$$
Let $p_1<p_2<\cdots$ be a sequence of primes such that $p_{i+1}\equiv 1\pmod{p_i}$. Is it true that\[\lim_k p_k^{1/k}=\infty?\]Does there exist such a sequence with\[p_k \leq \exp(k(\log k)^{1+o(1)})?\]



Such a sequence is sometimes called a prime chain.

If we take the obvious 'greedy' chain with $2=p_1$ and $p_{i+1}$ is the smallest prime $\equiv 1\pmod{p_i}$ then Linnik's theorem implies that this sequence grows like\[p_k \leq e^{e^{O(k)}}.\]It is conjectured that, for any prime $p$, there is a prime $p'\leq p(\log p)^{O(1)}$ which is congruent to $1\pmod{p}$, which would imply this sequence grows like\[p_k\leq \exp(k(\log k)^{1+o(1)}).\]An extensive study of the growth of finite prime chains was carried out by Ford, Konyagin, and Luca \cite{FKL10}.

See also [696].
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 695
erdosUrl: https://erdosproblems.com/695

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
- [Problem #696](https://www.erdosproblems.com/696)
- [Problem #694](https://www.erdosproblems.com/694)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er79e]
- [FKL10]

## OEIS Sequences

- [A061092](https://oeis.org/A061092)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
