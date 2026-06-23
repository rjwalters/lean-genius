# Erdős #892 - Knowledge Base

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

Is there a necessary and sufficient condition for a sequence of integers $b_1<b_2<\cdots$ that ensures there exists a primitive sequence $a_1<a_2<\cdots$ (i.e. no element divides another) with $a_n \ll b_n$ for all $n$?

In particular, is this always possible if there are no non-trivial solutions to $(b_i,b_j)=b_k$?



A problem of Erd\H{o}s, S\'{a}rk\"{o}zy, and Szemer\'{e}di \cite{ESS68}. It is known that\[\sum \frac{1}{b_n\log b_n}<\infty\]and\[\sum_{b_n<x}\frac{1}{b_n} =o\left(\frac{\log x}{\sqrt{\log\log x}}\right)\]are both necessary. (The former is due to Erd\H{o}s \cite{Er35}, the latter to Erd\H{o}s, S\'{a}rk\"{o}zy, and Szemer\'{e}di \cite{ESS67}.)

One can ask a similar question for sequences of real numbers, as in [143].




References


[ESS67] Erd\H{o}s, P. and S\'{a}rk\"ozy, A. and Szemer\'{e}di, E., On a theorem of Behrend. J. Austral. Math. Soc. (1967), 9--16.

[ESS68] Erd\H{o}s, P. and S\'{a}rk\"ozi, A. and Szemer\'{e}di, E., On the solvability of certain equations in sequences of
positive upper logarithmic density. J. London Math. Soc. (1968), 71--78.

[Er35] Erd\"{o}s, Paul, Note on Sequences of Integers No One of Which is Divisible By Any Other. J. London Math. Soc. (1935), 126-128.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #143
- Problem #891
- Problem #893
- Problem #2
- Problem #39
- Problem #1

## References

- Er98
- ESS68
- Er35
- ESS67

## Sessions

- **2026-05-13 (researcher-9, S3 PREP, complement to PR #18763)** — Doc-only state.md / knowledge.md / gallery JSON sync explicitly scoped out by the sibling skeleton PR #18763 (researcher-11). Pinned 10 Mathlib lemma names + line numbers against lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Replaced the prior `for k ≥ 1` condensed-term lower bound with the uniform-in-k bound `2^k + 2 ≤ 2^(k+2)` (valid for all k ∈ ℕ since `3·2^k ≥ 2`), yielding `2^k · f(2^k) ≥ 1/(4·(k+2)·log 2)` without a k=0 special case. Full Steps 1–6 recipe + LOC estimate in `state.md` S3 PREP section.

---

*Generated from erdosproblems.com on 2026-01-15*
