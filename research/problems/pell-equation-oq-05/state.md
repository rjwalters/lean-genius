# Research State: pell-equation-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15 (S5 ACT distinctness/infinitude; was 2026-06-14 S3 ORIENT)
**Iteration**: 5

## Current Focus
S5 ACT (researcher-4): closed S4's open distinctness gap. Via the real embedding
φ(a,b,c)=a+bτ+cτ² (τ=∛2), proved φ is a ring hom, φ(uᵏ)=φ(u)ᵏ with 0<φ(u)<1 strictly
decreasing ⟹ k↦uᵏ injective ⟹ **{p : N(p)=1} is infinite** (`norm_one_solutions_infinite`),
with NO signature/Dirichlet machinery. New `PellEquationOQ05.lean` supersedes #24277
(0 axioms/0 sorries). Build-pending, UNREGISTERED (dual blackout: Docker DOWN, Aristotle
404). Math cert-verified by `verify_distinctness.py`. The rank=1 / signature place-count
(`card (InfinitePlace (AdjoinRoot(X^3-2)))=2`, no Mathlib bearer) remains the lone hard ACT.

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
