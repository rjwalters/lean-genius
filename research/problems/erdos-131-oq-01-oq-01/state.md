# Research State: erdos-131-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
Shipped a verified, axiom-free STRUCTURAL contribution (not the open exponent):
the Erdős–Ginzburg–Ziv bound `a ∈ A, a ≥ 2, IsNonDividing A ⟹ |A| ≤ 2a − 1`
(Proofs/Erdos131EGZBound.lean), generalizing the parent's mod-2 parity bound
(2 ∈ A ⟹ |A| ≤ 3) to every element via EGZ. Gallery entry erdos-131-oq-01-oq-01.
The growth-rate exponent OQ itself remains a hard open asymptotic, untouched.

## Active Approach
ACT: per-element structural upper bounds on non-dividing sets via Int.erdos_ginzburg_ziv.
Recovered the parent parity result as the a=2 corollary; sharp at a=2 via {2,4,5}.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2

## Blockers
The OQ (exact growth exponent of F(N)) is genuinely open in the literature
(window exp(c√log N) ≤ F(N) ≤ N^{1/4+o(1)}; Pham–Zakharov 2024). Not build-blocked —
research-blocked. OEIS A068063 cross-check pending (oeis.org 403 to fetcher).

## Next Action
Do NOT chase the exponent by enumeration. Structural follow-ups (open):
(1) Is |A| ≤ 2a−1 sharp for a > 2, or is the true max smaller? Characterize extremal sets.
(2) Aggregate the per-element EGZ bounds into a global F(N) bound (averaging / residue-class
EGZ) — an elementary route toward the Pham–Zakharov N^{1/4+o(1)} ceiling.
ALSO: the parent file Proofs/Erdos131Problem.lean does NOT compile on Mathlib v4.26.0
(orphan docstrings before `axiom` decls at lines 127/173; pre-v4.26 `Finset.card_sdiff`
arg order at line 479 → omega failure at 488). The erdos-131 gallery entry is therefore
falsely "verified" — flag for mechanic repair.
