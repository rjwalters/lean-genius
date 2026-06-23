# Erdős #478 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $p$ be a prime and\[A_p = \{ k! \pmod{p} : 1\leq k<p\}.\]Is it true that\[\lvert A_p\rvert \sim (1-\tfrac{1}{e})p?\]



Since $A_p/A_p=\{1,\ldots,p-1\}$ it follows that $\lvert A_p\rvert \gg p^{1/2}$. The best known lower bound is due to Grebennikov, Sagdeev, Semchankau, and Vasilevskii \cite{GSSV24},\[\lvert A_p\rvert \geq (\sqrt{2}-o(1))p^{1/2},\]which follows from proving that $\lvert A_pA_p\rvert=(1+o(1))p$.

Wilson's theorem implies $(p-2)!\equiv 1\pmod{p}$, and hence $\lvert A_p\rvert\leq p-2$. It is open whether even $\lvert A_p\rvert<p-2$. This has been verified for all primes $p<10^9$ (see \cite{GSSV24}). Results on $\lvert A_p\rvert$ on average were obtained by Klurman and Munsch \cite{KlMu17}.

In Hardy and Subbarao \cite{HaSu02} they raise the question, discussed in conversation with Erd\H{o}s, of whether $\lvert A_p\rvert=p-2$ for many values of $p$. (This is also mentioned in problem A2 of Guy's collection.) Such a prime must be $\equiv 1\pmod{4}$. The answer is surely only finitely many (and probably only $p=5$, given the data mentioned above).




References


[GSSV24] Grebennikov, Alexandr and Sagdeev, Arsenii and Semchankau,
Aliaksei and Vasilevskii, Aliaksei, On the sequence {$n! \bmod p$}. Rev. Mat. Iberoam. (2024), 637--648.

[HaSu02] Hardy, G. E. and Subbarao, M. V., A modified problem of Pillai and some related questions. Amer. Math. Monthly (2002), 554--559.

[KlMu17] Klurman, Oleksiy and Munsch, Marc, Distribution of factorials modulo {$p$}. J. Th\'{e}or. Nombres Bordeaux (2017), 169--177.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 3/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #2
- Problem #477
- Problem #479
- Problem #39
- Problem #1

## References

- GSSV24
- KlMu17
- HaSu02

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*
