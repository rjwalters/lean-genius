# Erdős #335 - Knowledge Base

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

Let $d(A)$ denote the density of $A\subseteq \mathbb{N}$. Characterise those $A,B\subseteq \mathbb{N}$ with positive density such that\[d(A+B)=d(A)+d(B).\]



One way this can happen is if there exists $\theta>0$ such that\[A=\{ n>0 : \{ n\theta\} \in X_A\}\textrm{ and }B=\{ n>0 : \{n\theta\} \in X_B\}\]where $\{x\}$ denotes the fractional part of $x$ and $X_A,X_B\subseteq \mathbb{R}/\mathbb{Z}$ are such that $\mu(X_A+X_B)=\mu(X_A)+\mu(X_B)$. Are all possible $A$ and $B$ generated in a similar way (using other groups)?


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
- Problem #334
- Problem #336
- Problem #2
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

### S6 PREP — Mathlib bearer audit + sub-goal roadmap (2026-05-13, researcher-10)

Doc-only session at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Bearer audit results**:
- `Mathlib/Combinatorics/Schnirelmann.lean` (SHA `280c461ec9f7…`, 12 KB) — **PRESENT**. Provides `schnirelmannDensity`, ~20 lemmas, plus a TODO listing Mann's theorem + asymptotic density definitions as unformalized.
- Weyl equidistribution — **ABSENT** from Mathlib. Only mentioned in `docs/1000.yaml` as an unformalized "1000 theorems" target.
- Density-version Plünnecke–Ruzsa / Mann's theorem — **ABSENT** from Mathlib. The finite (cardinality) Plünnecke–Ruzsa is in `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean` but does not bear our density statement.
- Fractional-part density additivity — **ABSENT**; chains on Weyl + Mann.

**Forward sub-goals pinned for next session**:
1. S7 ACT — `schnirelmann_le_asymp` bridge lemma (~40–80 LOC, requires `[DecidablePred (· ∈ A)]`).
2. S8 ACT — `density_additive_zero_singleton : DensityAdditive {0} A` concrete witness (~10–20 LOC, no new imports).
3. S9 ACT — `Sumset_singleton_left : Sumset {k} A = (·+k) '' A` translate identity (~10–20 LOC, no new imports).

**Key insight surfaced**: the gap between Schnirelmann density and asymptotic density is real and important — `schnirelmannDensity (setOf Even) = 0` (because 1 ∉ Even) while `asympDensity (setOf Even) = 1/2`. Future S7 ACT must respect this directionality (`schnirelmann ≤ asymp`).

**State.md sync**: Phase "NEW" → "PREP", Iteration 1 → 6, populated merged-PR table.

**Lean code**: 0 LOC changed this session (pure documentation + state sync). 0 sorries / 0 axioms touched.

See: `sessions/2026-05-13-s06-prep-mathlib-bearer-audit-and-subgoal-roadmap.md`

---

*Generated from erdosproblems.com on 2026-01-13; sessions appended chronologically.*
