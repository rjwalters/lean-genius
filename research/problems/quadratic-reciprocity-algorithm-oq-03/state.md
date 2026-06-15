# Research State: quadratic-reciprocity-algorithm-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14 (S6 ORIENT — Milestone 2 numerically certified)
**Iteration**: 6

## Session 6 (2026-06-14, researcher-2) — Milestone 2 certified, honesty flag discharged
Build-free (Docker down). Added `verify_reciprocity_m2.py` (all asserts pass, 240 odd-prime
pairs). Pinned the M2 reciprocity bridge with verify-before-assert: the **grid-transpose
permutation** `σ=c∘r⁻¹` (`r(i,j)=i·q+j`, `c(i,j)=j·p+i`) has `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`
— a self-contained, M1-independent combinatorial identity — and assembles with the M1 Zolotarev
signs to recover QR. **Refuted** the naive CRT-listing permutation `ρ(k)=(k mod p)·q+(k mod q)`
as the bridge (its sign is neither the reciprocity factor nor the Legendre product). M2 is no
longer "second proof in name only" — its new content (lemma B) is now explicit and certified.
Next build-free step: pin M2 `Equiv.Perm.sign` bearers to file:line. See knowledge.md.

## Current Focus
Zolotarev's lemma as the formalization spine: `legendreSym p a = Perm.sign (mulLeft a)` on
`ZMod p`. OQ resolved on paper (researcher-8 S1); Milestone-1 statement + key cycle-structure
step numerically verified (researcher-4 S2); committed as a reproducible script
(`verify_zolotarev.py`, researcher-5 S3, asserts all four steps for every odd prime 3≤p<80).
researcher-4 S4 **pinned every M1 Mathlib bearer to an exact `file:line` at the build version**
(v4.26.0, mathlib rev `2df2f01`) and re-confirmed Zolotarev's lemma is still absent upstream — so
M1 is now paste-ready (numerically certified AND name-discovery-free), awaiting only Docker.

## Active Approach
Permutation-sign (Zolotarev) proof. Milestone 1 = the Zolotarev lemma itself (cyclic units +
cycle-sign + Euler's criterion), ~80–120 LOC, oq-01-independent. Milestone 2 (reciprocity) =
the grid-transpose sign lemma (B, `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`, S6-certified) assembled with
M1; the exact statement is now pinned and numerically de-risked (was "gated/assess after M1").

## Attempt Count
- Total attempts: 0 (no Lean built — Docker down, no materialized Mathlib)
- Current approach attempts: 0
- Approaches tried: 1 surveyed (Zolotarev direct), 1 deprioritized (algorithm-confluence)

## Blockers
- Docker build environment down (`docker info` times out); cannot compile/verify Lean this session.
- No new foundational Mathlib gap for Milestone 1 — it is buildable once the environment returns.

## Next Action
**ACT Milestone 1 (when Docker returns):** new file `proofs/Proofs/QuadraticReciprocityZolotarev.lean`
proving `legendreSym p (a.val : ℤ) = (Equiv.Perm.sign (Equiv.mulLeft₀ a ha) : ℤ)` for odd prime `p`,
`a : ZMod p`, `a ≠ 0`. Steps: (1) `π_g` is a single `(p−1)`-cycle on the units ⇒ `sign = −1`;
(2) `a = g^k`, `sign (π_a) = (−1)^k` via `map_pow`; (3) Euler's criterion gives `legendreSym p a =
(−1)^k`. **All bearers confirmed @ v4.26.0 (rev `2df2f01`) — no name-discovery left** (see S4 in
knowledge.md for the file:line table): `Equiv.mulLeft₀` (Algebra/GroupWithZero/Units/Equiv.lean:34,
returns `Perm G₀`), `IsCyclic Rˣ` instance (RingTheory/IntegralDomain.lean:137) + `IsCyclic.exists_generator`,
`Equiv.Perm.IsCycle.sign` (GroupTheory/Perm/Cycle/Basic.lean:434), `legendreSym.eq_pow` /
`euler_criterion` (NumberTheory/LegendreSymbol/Basic.lean:114/:62). Then create the gallery entry
`src/data/proofs/quadratic-reciprocity-zolotarev/`.

See knowledge.md for the full survey, Mathlib inventory, and the honesty flag on Milestone 2.
