# Problem: Prove diagInter_isUnbounded in Fodor's Pressing-Down Lemma

**Slug**: cantor-diagonalization-oq-02-oq-03-oq-02-oq-01
**Created**: 2026-04-05T05:30:16-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent proof `CantorDiagonalizationOQ02OQ03OQ02.lean` (Fodor's Pressing-Down Lemma)
has exactly one sorry:

```lean
theorem diagInter_isUnbounded {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (f : κ.ord.toType → Set κ.ord.toType) (hf : ∀ β, IsClub (f β)) :
    IsUnbounded (diagInter f) := by
  sorry
```

The `diagInter f` is the diagonal intersection: `α ∈ diagInter f ↔ ∀ β < α, α ∈ f β`.

### Plain Language

For a regular uncountable cardinal κ, if f(β) is a club (closed unbounded set) for every
β < κ, then the diagonal intersection of the f(β)'s is also unbounded (and hence, combined
with the already-proved closed part, is a club).

### Why This Matters

This resolves the single sorry in `CantorDiagonalizationOQ02OQ03OQ02.lean`, making
Fodor's Pressing-Down Lemma fully axiom-free and sorry-free. The lemma is used in the
Cantor-diagonalization family of proofs.

## Known Results

### What's Already Proven

- `diagInter_isClosedBelow` (PROVED in the file): diagonal intersection of clubs is closed
- `diagInter_isClub` uses BOTH parts; resolving this sorry completes it
- The finite intersection of clubs is a club (needs to be proved, but follows from ping-pong)

### What's Still Open

- `diagInter_isUnbounded`: the sorry we need to eliminate
- Intermediate lemma: `isClub_inter` — intersection of two clubs is a club

### Our Goal

Prove `diagInter_isUnbounded` in the existing Lean file by:
1. Proving `isClub_inter` (finite club intersection is a club) via ping-pong argument
2. Using it to build the ω-sequence for unboundedness

## Proof Sketch (from comments in Lean file)

Given α₀ < κ.ord, build an increasing ω-sequence:
- α₁ > α₀ in f(α₀) (exists since f(α₀) is unbounded)
- αₙ₊₁ > αₙ in ⋂_{β ≤ αₙ} f(β) (this intersection is a club since it involves < κ clubs)
- Let γ = sup αₙ < κ (since cf(κ) = κ > ω)
- γ ∈ diagInter f because for any β < γ, β < αₙ for some n, so αₙ ∈ f(β),
  and since f(β) is closed and αₙ → γ, we have γ ∈ f(β)

The intermediate `isClub_inter`: if C₁, C₂ are clubs, C₁ ∩ C₂ is a club via ping-pong:
build alternating sequence c₁ < c₂ < c₃ < ... with c_{2n} ∈ C₁ and c_{2n+1} ∈ C₂ above
the previous; the supremum is in both (by closure) and above α₀ (by unboundedness).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cantor-diagonalization-oq-02-oq-03-oq-02` | Parent proof (Fodor's Lemma) — contains the sorry | Club sets, diagonal intersection, regular cardinals |
| `cantor-diagonalization-oq-02-oq-03` | Grandparent — stationary sets and club filter | Club filter, stationary sets |

## Initial Thoughts

### Potential Approaches

1. **Direct ω-sequence construction** (from proof sketch in comments):
   - Build increasing sequence using unboundedness of each f(β)
   - Use regularity to bound sup < κ
   - Use closure to conclude sup ∈ f(β) for all β below it
   - Risk: Lean's ordinal arithmetic for the sup argument may be tricky

2. **Piggyback on Mathlib club filter lemmas**:
   - Check if `Ordinal.IsClub`, `Cardinal.IsRegular`, or `Filter.club` exist in Mathlib
   - Risk: Mathlib's API for clubs/regular cardinals may not match the file's definitions

### Key Difficulties

- The file uses custom definitions of `IsClub`, `IsUnbounded`, `diagInter` — not Mathlib's
- The sup argument requires `Ordinal.iSup_lt_ord_lift` or similar for regular cardinals
- Finite intersection lemma needs induction with ping-pong construction

### What Would a Proof Need?

- `Ordinal.IsLimit`: sup of ω-sequence is a limit ordinal < κ.ord (by regularity cf(κ) = κ)
- `IsClub.unbounded`: extract increasing sequence above any bound
- `IsClub.closed`: limit of sequence in a club is in the club
- `Cardinal.IsRegular.cof_eq`: regularity gives cf = κ, so ω-sequence sup < κ

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Complete proof sketch exists in the Lean file comments (lines 154–175)
- One sorry to resolve, no structural changes needed
- Club/ordinal infrastructure exists in the file (just needs assembly)
- The ping-pong argument for `isClub_inter` is standard set theory

**Estimated Effort**:
- Exploration (OBSERVE): read Lean file, find Mathlib ordinal API
- Implementation (ACT): 50–150 lines of new Lean

## References

### Lean File
- `proofs/Proofs/CantorDiagonalizationOQ02OQ03OQ02.lean` — the target file, lines 151–178

### Mathlib
- `Mathlib.Order.Ordinal.Basic` — ordinal arithmetic
- `Mathlib.SetTheory.Cardinal.Basic` — `Cardinal.IsRegular`, `Cardinal.cof`
- `Mathlib.Order.Filter.Basic` — filter API

## Metadata

```yaml
tags:
  - set-theory
  - ordinals
  - club-sets
  - regular-cardinals
  - fodors-lemma
related_proofs:
  - cantor-diagonalization-oq-02-oq-03-oq-02
  - cantor-diagonalization-oq-02-oq-03
difficulty: medium
source: gallery-gap
created: 2026-04-05T05:30:16-07:00
```
