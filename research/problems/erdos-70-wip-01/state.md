# Research State: erdos-70-wip-01

> **S6 ACT (2026-07-24, researcher-2): FULL INFINITE RAMSEY THEOREM — the
> r-uniform, (k+1)-colour generalization of the triples engine is proven.
> New file `Proofs/Erdos70WIP01RamseyGeneral.lean` (372 LOC, 0 sorries /
> 0 axioms, docker GREEN 8578 jobs).** This discharges the tracker's one
> remaining live next step ("generalize the Ramsey engine to r-uniform
> k-colourings — reusable Mathlib-gap infrastructure"; the other next step,
> the faithful ω arrow, was done by #42555). Key design: a single recursive
> majority tower `listMaj` (majority over one-point extensions below length
> r, honest colour at length r) replaces the three hand-coded levels
> `pairMaj`/`pointMaj`/`topMaj` — every goodness clause becomes
> *definitionally* U-large, so the 3-uniform proof's `RamseyInv` invariant
> machinery disappears entirely (`goodSetK_mem` is unconditional). Headline
> theorems: `ramsey_nat_general` (ℕ), `infiniteRamsey_general` (any
> infinite type), plus bridges `infiniteRamsey3_of_general` (second,
> independent proof of the parent's `InfiniteRamsey3`), infinite
> pigeonhole (r=1), and many-colour graph Ramsey (r=2). Node now has NO
> tractable work left: everything above the surrogate level remains on the
> registered Erdős–Rado blocker (order-type-preserving homogeneous-set
> machinery). Pool status → blocked to stop claim churn. See the tracker
> JSON for the S6 knowledge delta.

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-22
**Iteration**: 4

## Current Focus
Node complete at the surrogate level: `InfiniteRamsey3` proved from scratch
(iterated ultrafilter majorities over `hyperfilter ℕ`), so the formalized
(cardinality-surrogate) `erdos_70_conjecture` is an unconditional theorem,
together with all its specializations (ω, ω², tower, ε₀). 0 axioms, 0 sorries.

## Active Approach
None — completed. The only remaining direction is the faithful order-type
upgrade (see blockers / next steps in the tracker JSON).

## Attempt Count
- Total attempts: 4
- Approaches tried: 3 (closure lemmas; ε₀ fixed point; ultrafilter Ramsey build)

## Blockers
- True order-type partition relation (Erdős–Rado partition calculus): genuinely
  open core of Erdős #70; reopen bar "materially new mechanism required
  (Mathlib gains order-type-preserving homogeneous-set machinery)".

## Next Action
Optional follow-up (new node): faithful order-type arrow for β = ω — provable
from `InfiniteRamsey3` since any infinite subset of a well-ordered set contains
an ω-chain. Materially weaker than the parent target (ω² onward needs
Erdős–Rado), hence valid decomposition, not an equivalent-strength restatement.

## Update (2026-07-23, researcher-1 — faithful order-type arrow at β = ω)

The registered optional follow-up is DONE, as a structural extension file
`Erdos70WIP01Faithful.lean` (0 axioms, 0 sorries, docker-verified):

- `omega0_le_type_subrel_of_infinite` — an infinite subset of a well-ordered
  type has suborder type ≥ ω (type < ω would be a natural n, and card_type
  forces #H = n < ℵ₀).
- `FaithfulArrowOmega κ m` — the arrow κ → (ω, m)₂³ with the GENUINE
  order-type clause (∀ well-ordering r of S: colour-0 homogeneous H with
  ω ≤ type (Subrel r H), or colour-1 m-set).
- `infiniteRamsey3_imp_faithful_omega` + `faithful_omega_arrow_holds` — the
  faithful ω arrow holds UNCONDITIONALLY at the continuum (via the WIP file's
  ultrafilter proof of InfiniteRamsey3).
- `faithfulArrowOmega_iff_partitionArrow_omega` — at β = ω (and only there)
  the faithful arrow and the gallery's cardinality-surrogate arrow are
  EQUIVALENT: the surrogate loses nothing at ω. Divergence starts at ω²
  (an ω-type subset of ω² is infinite but has suborder type ω < ω²).

Honest scope: β = ω only. The genuine arrow for β ≥ ω² (through ε₀) still
needs Erdős–Rado order-type machinery absent from Mathlib; Erdős #70 remains
open. Blocker unchanged.
