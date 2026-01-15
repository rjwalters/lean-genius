# Problem: Erdős #1130

## Statement

### Plain Language
Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

For $x_1,\ldots,x_n\in [-1,1]$ let\[l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},\]which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.

Let $x_0=-1$ and $x_{n+1}=1$ and\[\Upsilon(x_1,\ldots,x_n)=\min_{0\leq i\leq n}\max_{x\in[x_i,x_{i+1}]} \sum_k \lvert l_k(x)\rvert.\]Is it true that\[\Upsilon(x_1,\ldots,x_n)\ll \log n?\]Describe which choice of $x_i$ maximise $\Upsilon(x_1,\ldots,x_n)$.



...

### Formal Statement
$$
Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

For $x_1,\ldots,x_n\in [-1,1]$ let\[l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},\]which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.

Let $x_0=-1$ and $x_{n+1}=1$ and\[\Upsilon(x_1,\ldots,x_n)=\min_{0\leq i\leq n}\max_{x\in[x_i,x_{i+1}]} \sum_k \lvert l_k(x)\rvert.\]Is it true that\[\Upsilon(x_1,\ldots,x_n)\ll \log n?\]Describe which choice of $x_i$ maximise $\Upsilon(x_1,\ldots,x_n)$.




The functions $l_k(x)$ are sometimes called the fundamental functions of Lagrange interpolation.

Erd\H{o}s \cite{Er47} could prove\[\Upsilon(x_1,\ldots,x_n)< \sqrt{n}.\]Erd\H{o}s thought that the maximising choice is characterised by the property that the sums\[\max_{x\in [x_i,x_{i+1}]}\sum_k \lvert l_k(x)\rvert\]are all equal for $0\leq i\leq n$ (where $x_0=-1$ and $x_{n+1}=1$), which would be the same (conjectured) characterisation as [1129].

See also [1129].




References


[Er47] Erd\H{o}s, P., Some remarks on polynomials. Bull. Amer. Math. Soc. (1947), 1169--1176.


Back to the problem
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 1130
erdosUrl: https://erdosproblems.com/1130

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
- [Problem #1129](https://www.erdosproblems.com/1129)
- [Problem #1131](https://www.erdosproblems.com/1131)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- [Er47]

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
