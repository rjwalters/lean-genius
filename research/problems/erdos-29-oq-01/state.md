# Research State: erdos-29-oq-01

## Current State
**Phase**: OBSERVE (S1 complete — comprehensive axiom map + Mathlib bearer survey + sub-goal decomposition)
**Path**: full
**Since**: 2026-05-13 (researcher-10 S1)
**Iteration**: 1

## Parent slug
`erdos-29` — the gallery proof `Erdos29Problem.lean`. Status: **`axiomatized`** with 5 JPSZ axioms; 0 sorries; 523 lines. The parent is "solved up to" a citation of Jain–Pham–Sawhney–Zakharov 2024 (arXiv:2405.08650). This OQ asks whether those JPSZ axioms can be removed.

## Problem (verbatim from problem.md)
The JPSZ axioms (`JPSZ_set`, `JPSZ_is_basis`, `JPSZ_is_economical`) fail to load in Aristotle due to `harmonicSorry` axioms. Can the JPSZ construction be formalized in Lean WITHOUT axioms, using Mathlib's existing library for hash functions, pseudorandomness, or derandomization?

Note: `JPSZ_is_economical` is in fact a **theorem** in `Erdos29Problem.lean` (proved from `JPSZ_representation_bound`), so the listing in the OQ statement is slightly stale. The actual open-question reduces to removing the 5 independent axioms below.

## Axiom inventory (parent file `proofs/Proofs/Erdos29Problem.lean`)

Five independent `axiom` declarations contribute to the parent's `axiomCount: 5` (verified via `grep -nE '^axiom ' proofs/Proofs/Erdos29Problem.lean`):

| # | Name (line) | Type | Role |
|---|---|---|---|
| 1 | `JPSZ_set` (L158) | `Set ℕ` | The construction itself — the explicit additive basis. |
| 2 | `JPSZ_is_basis` (L164) | `IsAdditiveBasis JPSZ_set` | `JPSZ_set + JPSZ_set = univ`. |
| 3 | `JPSZ_representation_bound` (L281) | `∃ C > 0, ∀ n ≥ 2, r_A(n) ≤ exp(C·√log n)` | Subpolynomial representation count. |
| 4 | `JPSZ_explicit` (L419) | `ExplicitSet JPSZ_set` | Decidable membership (constructive). |
| 5 | `JPSZ_size_optimal` (L489) | `∃ C > 0, ∀ N ≥ 1, |A ∩ [1,N]| ≤ C·√N·√(log N)` | Density upper bound. |

Two further results are **theorems**, not axioms:
- `JPSZ_is_economical` (L170) — proved from #3 via squeeze on `exp(C√log n)/n^ε → 0`.
- `JPSZ_density_zero` (L241) — proved from #5 via squeeze on `C·√(log N/N) → 0`.

The interesting open-question structure: only axioms #1–#5 are needed; #2, #3, #4, #5 are all properties OF the set introduced in #1.

## Mathlib bearer audit (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

What Mathlib has that is structurally relevant:

| Mathlib path | Content | Bearing on JPSZ removal |
|---|---|---|
| `Mathlib/Combinatorics/Additive/AP/Three/Defs.lean` | `ThreeAPFree`, `rothNumberNat`, Salem–Spencer machinery | Defines 3-AP-free sets; primary structural analogue to JPSZ. |
| `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` | `Behrend.sphere`, `Behrend.map`, `roth_lower_bound` (`n / exp(O(√log n))`) | Explicit construction with the **same `exp(O(√log n))` scaling** as JPSZ's representation bound — directly relevant. |
| `Mathlib/Combinatorics/Additive/Energy.lean` | `Finset.addEnergy`, `Finset.mulEnergy` | Additive-energy machinery for representation counting. |
| `Mathlib/Combinatorics/Additive/Dissociation.lean` | `AddDissociated`, `Finset.addSpan` | Dissociation theory (Sidon-set analog for groups). |
| `Mathlib/Combinatorics/Additive/Randomisation.lean` | Random-shift method for dissociated supports | Probabilistic tool from additive Fourier theory. |
| `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean` | Plünnecke–Ruzsa sumset bounds | Standard tool for `|A+A| / |A|` ratios. |
| `Mathlib/NumberTheory/MaricaSchoenheim.lean` | Marica–Schönheim ≤ Graham conjecture for squarefree integers | Tangentially relevant (sumset extremal). |
| `Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean` | Fourier on finite abelian groups | Bedrock for circle-method-style arguments. |

What Mathlib does **not** have (verified via GitHub code search at the pinned SHA):
- No `Sidon` (B₂[1]) set predicate.
- No `Bh` / `Bₕ[g]` set predicate.
- No `IsAdditiveBasis` predicate on `Set ℕ`.
- No `representationCount` / `r_A(n)` defined for general sets.
- No JPSZ-style construction or anything resembling the algebraic-geometric Sidon-Bh-like primitives (projection from quadrics over finite fields with prescribed projection types).
- No `harmonicSorry` (those are Aristotle-internal placeholder axioms, not Mathlib).

The honest finding: **Mathlib has Behrend (3-AP-free, density `n · exp(−O(√log n))`) but does not have the dual notion (additive bases with subpolynomial representation count) that JPSZ resolves**.

## Tractability assessment

JPSZ 2024 (arXiv:2405.08650, Jain–Pham–Sawhney–Zakharov) resolves a 90-year-old problem using:
1. An explicit Sidon-like primitive in `(ℤ/p)²` from quadratic-residue projections.
2. A "lifting" from finite-field constructions to ℕ via a careful base-decomposition.
3. Density and representation-count analyses requiring delicate sieve estimates.

These are **research-level mathematics from 2024**. A full Lean formalization is realistically a person-year project, comparable in scope to (and dependent on technologies not yet in Mathlib at HEAD as of pinned SHA):
- A Sidon / B₂[1] set library (~5–10 KLOC).
- Algebraic-geometric primitives in `(ℤ/p)ⁿ` beyond what's in `Mathlib/NumberTheory/LegendreSymbol`.
- Quantitative sieve bounds adapted to subpolynomial representation counts.

**Verdict for this OQ**: removing all 5 JPSZ axioms is **out of scope for any one researcher session**. However, the OQ admits useful intermediate sub-goals that are each independently formalizable and contribute to closing the axiom gap.

## Sub-goal decomposition

Three forward sub-goals identified, each formalizable in `~50–200 LOC` of Lean, each doc-only PREP-able now and ACT-able in a later session:

### Sub-goal A (TRACTABLE — recommended next)
**Replace `JPSZ_size_optimal` (axiom #5) with a constructive upper bound on `|A ∩ [1,N]|` that does not depend on `JPSZ_set`.**

The current axiom says `|JPSZ_set ∩ [1,N]| ≤ C·√N·√(log N)`. Once `JPSZ_set` is concretely defined (sub-goal B/C), this bound becomes a finite combinatorial computation. **But** an axiom-free version of the WEAKER statement
> "Any additive basis A with `IsEconomical A` satisfies `|A ∩ [1,N]| ≤ C·√N·polylog N`"
is essentially the Erdős–Turán lower bound on B₂ bases and **may be derivable in Lean from `IsAdditiveBasis` + `IsEconomical` alone**.

**Mathlib bearers**: `Set.ncard`, `Finset.card_image_le`, `Nat.sqrt`, `Real.log`. No new imports required.

**Expected LOC**: 50–100 lines. Risk: low — the proof is standard pigeonhole. Won't remove axiom #5 in `Erdos29Problem.lean` directly, but it will provide a `JPSZ_size_optimal_general` theorem that subsumes #5 once `JPSZ_set` is defined.

### Sub-goal B (HARDER — defer to later session)
**Define a concrete candidate `JPSZSet : Set ℕ` via Behrend-like sphere construction and prove `JPSZ_explicit` (decidable membership).**

The Behrend construction in `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` provides an explicit, decidable subset of `{0, ..., n}^d` via sphere intersection. The JPSZ construction is morally a **dual** of Behrend: where Behrend gives a 3-AP-FREE set, JPSZ gives an ADDITIVE BASIS. Both use the `exp(O(√log n))` scaling that comes from the sphere/base-d encoding.

**Mathlib bearers**: `Behrend.sphere`, `Behrend.map`, `Behrend.box`, `DecidablePred`.

**Expected LOC**: 150–250 lines. Risk: medium — defining the set is easy (~30 lines); proving it's an additive basis (`JPSZ_is_basis`) is the hard part and likely requires axiom #2 to remain.

### Sub-goal C (HARDEST — research-level, very long horizon)
**Prove `JPSZ_representation_bound` (axiom #3) for the candidate from sub-goal B.**

This is the analytic core of the JPSZ paper. Requires sieve estimates and would take person-months even with full sub-goal B in hand. **Recommend axiomatizing this in the interim** with a clean `theorem`-shaped statement so downstream proofs depend only on the bound, not on the existence of `JPSZ_set`.

## Active Approach
None yet. Sub-goal A is the recommended ACT target for a future session.

## Attempt Count
- Total attempts: 1 (this OBSERVE session)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None for OBSERVE. For sub-goal A: zero. For sub-goal B: requires a more substantial Lean session and `Behrend.sphere` API familiarity. For sub-goal C: research-level, person-months.

## Next Action
Future session: pick up sub-goal A. Draft a `JPSZ_size_optimal_general : ∀ A, IsAdditiveBasis A → IsEconomical A → ∃ C, ∀ N ≥ 1, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) ≤ C * Real.sqrt N * Real.sqrt (Real.log N)` in a fresh `Erdos29OQ01.lean` companion file. Status will be `axiomatized` (depending on `IsAdditiveBasis`/`IsEconomical` from parent) but **0 new axioms relative to parent**.
