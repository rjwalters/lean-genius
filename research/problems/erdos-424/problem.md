# Problem: Erdős #424

## Statement

### Plain Language
Let $a_1=2$ and $a_2=3$ and continue the sequence by appending to $a_1,\ldots,a_n$ all possible values of $a_ia_j-1$ with $i\neq j$. Is it true that the set of integers which eventually appear has positive density?



Asked by Hofstadter. The sequence begins $2,3,5,9,14,17,26,\ldots$ and is A005244 in the OEIS. This problem is also discussed in section E31 of Guy's book Unsolved Problems in Number Theory.

In \cite{ErGr80...


### Formal Statement
$$
Let $a_1=2$ and $a_2=3$ and continue the sequence by appending to $a_1,\ldots,a_n$ all possible values of $a_ia_j-1$ with $i\neq j$. Is it true that the set of integers which eventually appear has positive density?



Asked by Hofstadter. The sequence begins $2,3,5,9,14,17,26,\ldots$ and is A005244 in the OEIS. This problem is also discussed in section E31 of Guy's book Unsolved Problems in Number Theory.

In \cite{ErGr80} (and in Guy's book) this problem as written is asking for whether almost all integers appear in this sequence, but the answer to this is trivially no (as pointed out to me by Steinerberger): no integer $\equiv 1\pmod{3}$ is ever in the sequence, so the set of integers which appear has density at most $2/3$. This is easily seen by induction, and the fact that if $a,b\in \{0,2\}\pmod{3}$ then $ab-1\in \{0,2\}\pmod{3}$.

Presumably it is the weaker question of whether a positive density of integers appear (as correctly asked in \cite{Er77c}) that was also intended in \cite{ErGr80}.

See also Problem 63 of Green's open problems list.
$$

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 424
erdosUrl: https://erdosproblems.com/424

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
- [Problem #3](https://www.erdosproblems.com/3)
- [Problem #423](https://www.erdosproblems.com/423)
- [Problem #425](https://www.erdosproblems.com/425)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)
- [Problem #63](https://www.erdosproblems.com/63)

## References

- [ErGr80]
- [Er77c]

## OEIS Sequences

- [A005244](https://oeis.org/A005244)
- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
