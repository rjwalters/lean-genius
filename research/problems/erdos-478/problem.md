# Problem: Erdős #478

## Statement

### Plain Language
Let $p$ be a prime and\[A_p = \{ k! \pmod{p} : 1\leq k<p\}.\]Is it true that\[\lvert A_p\rvert \sim (1-\tfrac{1}{e})p?\]



Since $A_p/A_p=\{1,\ldots,p-1\}$ it follows that $\lvert A_p\rvert \gg p^{1/2}$. The best known lower bound is due to Grebennikov, Sagdeev, Semchankau, and Vasilevskii \cite{GSSV24},\[\lvert A_p\rvert \geq (\sqrt{2}-o(1))p^{1/2},\]which follows from proving that $\lvert A_pA_p\rvert=(1+o(1))p$.

Wils...


### Formal Statement
$$
Let $p$ be a prime and\[A_p = \{ k! \pmod{p} : 1\leq k<p\}.\]Is it true that\[\lvert A_p\rvert \sim (1-\tfrac{1}{e})p?\]



Since $A_p/A_p=\{1,\ldots,p-1\}$ it follows that $\lvert A_p\rvert \gg p^{1/2}$. The best known lower bound is due to Grebennikov, Sagdeev, Semchankau, and Vasilevskii \cite{GSSV24},\[\lvert A_p\rvert \geq (\sqrt{2}-o(1))p^{1/2},\]which follows from proving that $\lvert A_pA_p\rvert=(1+o(1))p$.

Wilson's theorem implies $(p-2)!\equiv 1\pmod{p}$, and hence $\lvert A_p\rvert\leq p-2$. It is open whether even $\lvert A_p\rvert<p-2$. This has been verified for all primes $p<10^9$ (see \cite{GSSV24}). Results on $\lvert A_p\rvert$ on average were obtained by Klurman and Munsch \cite{KlMu17}.

In Hardy and Subbarao \cite{HaSu02} they raise the question, discussed in conversation with Erd\H{o}s, of whether $\lvert A_p\rvert=p-2$ for many values of $p$. (This is also mentioned in problem A2 of Guy's collection.) Such a prime must be $\equiv 1\pmod{4}$. The answer is surely only finitely many (and probably only $p=5$, given the data mentioned above).
$$

## Classification

```yaml
tier: C
significance: 5
tractability: 3
erdosNumber: 478
erdosUrl: https://erdosproblems.com/478

tags:
  - erdos
```

**Significance**: 5/10
**Tractability**: 3/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - open problem; long statement


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
- [Problem #477](https://www.erdosproblems.com/477)
- [Problem #479](https://www.erdosproblems.com/479)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [GSSV24]
- [KlMu17]
- [HaSu02]

## OEIS Sequences

- [A210184](https://oeis.org/A210184)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
