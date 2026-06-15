# Research State: pell-equation-oq-05

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14 (S3 ORIENT bearer-pin + ACT re-scope; was 2026-06-14T21:05 S2)
**Iteration**: 3

## Current Focus
S3 ORIENT (researcher-7): bearers re-confirmed at the exact lake-pin and the ACT
re-scoped. `NumberField.Units.rank := card (InfinitePlace K) - 1` is a *definition*
(DirichletTheorem.lean:354), and `K=ℚ(∛2)=AdjoinRoot(X^3-2)` is a free `NumberField`
instance (Basic.lean:451 + Eisenstein), so the ACT's only hard part is proving
`card (InfinitePlace K) = 2` — which has **no Mathlib bearer** (no signature-from-minpoly
procedure; the cyclotomic place-count lemmas don't apply). Place-count is the LOC-dominant
step to de-risk first. Still Docker-gated (Docker DOWN, Aristotle `prove` "Resource not found").

## Active Approach
Instantiate Mathlib's Dirichlet unit theorem for a concrete cubic
($K=\mathbb{Q}(\sqrt[3]2)$): prove unit rank $=1$ from signature $(1,1)$, formalize the
cubic norm form via `Algebra.norm`, exhibit the fundamental unit $t-1$, and state
finiteness of $N(\xi)=m$ solution classes.

## Verified This Session (sympy, reproducible)
- Signatures + rank $r_1+r_2-1$ for 5 fields; identity $r_1+2r_2=n$.
- Cubic norm form $a^3+2b^3+4c^3-6abc$ as det of multiplication matrix.
- Fundamental unit $t-1$, inverse $t^2+t+1$, norm-1 chain $u^k$.
- $N(\xi)=2$ solved by $t$; one class mod units (class number 1).
- Classical Pell recovered as the rank-1 quadratic case.

See `verify_norm_equations.py` (all sections pass) and `knowledge.md`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Docker unavailable this session → no `lake build` → ACT (Lean transcription) deferred.

## Next Action
ACT (when a backend is up): write `Proofs/PellEquationOQ05.lean`. Attack the
place-count `Fintype.card (InfinitePlace (AdjoinRoot (X^3-2))) = 2` FIRST (the only
bearer-less, LOC-dominant step); field instance + `rank = 1` unfolding are near-free.
Then norm-form via `Algebra.norm` and `ClassGroup`-finiteness packaging. See
knowledge.md §"Bearer pin + ACT re-scope" for pinned file:line bearers.
