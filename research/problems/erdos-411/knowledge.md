# Erdős #411 - Knowledge Base

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

Let $g_1=g(n)=n+\phi(n)$ and $g_k(n)=g(g_{k-1}(n))$. For which $n$ and $r$ is it true that $g_{k+r}(n)=2g_k(n)$ for all large $k$?



The known solutions to $g_{k+2}(n)=2g_k(n)$ are $n=10$ and $n=94$. Selfridge and Weintraub found solutions to $g_{k+9}(n)=9g_k(n)$ and Weintraub found\[g_{k+25}(3114)=729g_k(3114)\]for all $k\geq 6$.

Steinerberger \cite{St25} has observed that, for $r=2$, this problem is equivalent to asking for solutions to\[\phi(n)+\phi(n+\phi(n))=n,\]and has shown that if this holds then either the odd part of $n$ is in $\{1,3,5,7,35,47\}$, or is equal to $8m+7$ or $6m+5$, where $8m+7\geq 10^{10}$ is a prime number and $\phi(6m+5)=4m+4$. Whether there are infinitely many such $m$ is related to the question of whether\[\phi(n)=\frac{2}{3}(n+1)\]has infinitely many solutions.

Cambie conjectures that the only solutions have $r=2$ and $n=2^lp$ for some $l\geq 1$ and $p\in \{2,3,5,7,35,47\}$. Cambie has shown this problem is reducible to the question of which integers $r,t\geq 1$ and primes $p\equiv 7\pmod{8}$ satisfy $g_k(2p^t)=4p^t$, and conjectures there are no solutions to this except when $t=1$ and $p\in \{7,47\}$. Cambie has also observed that\[g_{k+4}(738)=3g_k(738),\]\[g_{k+4}(148646)=4g_k(148646),\]and\[g_{k+4}(4325798)=4g_{k}(4325798)\]for all $k\geq 1$.




References


[St25] S. Steinerberger, On an iterated arithmetic function problem of Erd\H{o}s and Graham. arXiv:2504.08023 (2025).


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
- Problem #410
- Problem #412
- Problem #2
- Problem #39
- Problem #1
- Problem #22

## References

- St25

## Sessions

### Session 2026-04-28 - Metadata Reconciliation

**Mode**: REVISIT
**Outcome**: completed (metadata fix; no Lean changes needed)

#### What I Found
- Erdos411Problem.lean is **axiom-free**: 0 axioms, 0 sorries, 217 lines
- Gallery `meta.json` already has `axiomCount: 0` and accurate `assumptions` field
- BUT `originalContributions` claimed "axiomatized Cambie's ratio-3 and ratio-4 solutions" — both wrong:
  - `cambie_ratio3` (n=738) is PROVED via strong induction using `totientStep_triple`
  - Ratio-4 cases (n=148646, n=4325798) are mentioned in comments but not formalized at all
- JSON `progressSummary` claimed "Remaining 4 axioms" but file has 0 axioms (extremely stale)
- `phase: OBSERVE` was wrong — substantial proof work has been done

#### Files Modified
- `src/data/research/problems/erdos-411.json` (phase, currentState, progressSummary)
- `src/data/proofs/erdos-411/meta.json` (originalContributions accuracy)
- `research/problems/erdos-411/knowledge.md` (this entry)

#### Key Findings
- The OPEN parts that remain in the file are **definitions**, not axioms:
  - `def ErdosProblem411 : Prop` — full characterization (open)
  - `def CambieConjecture : Prop` — Cambie's structural conjecture (open)
  - `def DoublingRelation`, `GeneralRatioRelation` — relation definitions
  - These are stated, not assumed; nothing is axiomatized in the file
- All three known cases (n=10, n=94, n=738) are proved as theorems with no `sorry` and no `axiom`

#### Next Steps (if more work desired)
- Formalize n=148646 and n=4325798 ratio-4 cases (would require a `totientStep_quadruple` lemma analogous to `totientStep_triple`)
- Prove the Steinerberger r=2 equivalence (DoublingRelation n 2 ↔ φ(n) + φ(n + φ(n)) = n) — currently only stated as a comment, not formalized

---

*Generated from erdosproblems.com on 2026-01-13*
