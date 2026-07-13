# Erdős #374 - Knowledge Base

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

For any $m\in \mathbb{N}$, let $F(m)$ be the minimal $k\geq 2$ (if it exists) such that there are $a_1<\cdots <a_k=m$ with $a_1!\cdots a_k!$ a square. Let $D_k=\{ m : F(m)=k\}$. What is the order of growth of $\lvert D_k\cap\{1,\ldots,n\}\rvert$ for $3\leq k\leq 6$? For example, is it true that $\lvert D_6\cap \{1,\ldots,n\}\rvert \gg n$?



Studied by Erd\H{o}s and Graham \cite{ErGr76} (see also \cite{LSS14}). It is known, for example, that:
{UL}
{LI}no $D_k$ contains a prime,{/LI}
{LI}$D_2=\{ n^2 : n>1\}$,{/LI}
{LI} $\lvert D_3\cap \{1,\ldots,n\}\rvert = o(\lvert D_4\cap \{1,\ldots,n\}\rvert)$,{/LI}
{LI} the least element of $D_6$ is $527$, and{/LI}
{LI} $D_k=\emptyset$ for $k>6$.{/LI}
{/UL}




References


[ErGr76] Erd\H{o}s, P. and Graham, R. L., On products of factorials. Bull. Inst. Math. Acad. Sinica (1976), 337-355.

[LSS14] Luca, F. and Saradha, N. and Shorey, T. N., Squares and factorials in products of factorials. Monatsh. Math. (2014), 385-400.


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
- Problem #373
- Problem #375
- Problem #2
- Problem #39
- Problem #1
- Problem #14

## References

- ErGr76
- ErGr80
- LSS14

## Sessions

State-md catchup at S9 (researcher-5, 2026-05-16) — see
`sessions/2026-05-16-s09-state-sync-axiomatized-265loc-deferred-growth-rate.md`
for full audit. Substantive research-class PRs touching
`proofs/Proofs/Erdos374Problem.lean` or `src/data/proofs/erdos-374/meta.json`:

| Iter | Date | PR | Commit | Description |
|-----|------|-----|--------|-------------|
| 0 | 2026-01-26 | #1352 | `38a3be78f3b` | initial enhance (stub + scaffolding) |
| 1 | 2026-03-23 | #5368 | `cb614ee9461` | axiom elimination + D₂ backward direction |
| 2 | 2026-03-28 | #7259 | `97d580b3a2f` | 2 axioms eliminated across erdos-374 + erdos-864 |
| 3 | 2026-03-28 | #7264 | `796f473e228` | +3 theorems + 1 assessment |
| 4 | 2026-03-28 | #7521 | `31844801b6e` | 12 axioms + 2 bugs + 11 meta.json audit |
| 5 | 2026-03-28 | #7272 | `09392a85f0b` | +18 theorems across 5 problems, 1 axiom eliminated |
| 6 | 2026-03-30 | #8308 | `b0a186690ef` | 1 axiom eliminated + 2 bugs + 8 lemmas proven |
| 7 | 2026-03-30 | #8347 | `f780eac6ac5` | isoperimetric multi-slug pass (touched 374 metadata) |
| 8 | 2026-03-30 | #8355 | `d67e1c4c089` | "4 problems — incl. factorial squares" (final Lean edit) |
| 9 | 2026-05-16 | (this PR) | — | S9 STATE-SYNC — doc-only catchup, no Lean/meta edits |

Current state (post-S8 build-verified, S9 doc-only): 265 LOC, 13 named
theorems + 3 private lemmas + 5 definitions, 0 axioms, 0 sorries,
Mathlib `v4.26.0`. Status `"axiomatized"` per open-conjecture
convention (the growth-rate question for D₃-D₆ remains formally
unstated). See `state.md` for next-action paths (a/b/c).

---

*Generated from erdosproblems.com on 2026-01-13*
