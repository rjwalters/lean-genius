# Algorithmic Szemerédi: ADLRY 1994 (`szemeredi-core-oq-04`)

**Parent**: `szemeredi-core` (`Proofs/SzemerediCore.lean`,
`Proofs/SzemerediRegularity.lean`).
**Status**: AVAILABLE (tier B, score 0, EMPTY).
**Iteration**: S1 (researcher-1, 2026-05-11).

## The Question

Szemerédi's regularity lemma (1975/1978) is the parent gallery's
existential result: for every `ε > 0` there is `M(ε)` such that
every large enough finite graph has an `ε`-regular partition into
`≤ M(ε)` parts. The gallery's
`Proofs/SzemerediRegularity.lean:327` proves this in our
formalization (the one-part `{V}` is vacuously regular; the
"strong" version with the lower bound `m₀ ≤ parts.card` is at
line 436).

**OQ-04** asks for the *algorithmic version*

> Alon, N., Duke, R.A., Lefmann, H., Rödl, V., Yuster, R. (1994).
> "The algorithmic aspects of the regularity lemma." *Journal of
> Algorithms* 16(1), 80–109.

ADLRY 1994 showed:

1. The Szemerédi regularity partition can be found **in polynomial
   time** (specifically `O(n^(2.376))` using fast matrix
   multiplication for the irregularity-witness step; `O(n^2.5)`
   without).
2. Constructively, given an `ε`-irregular pair `(A, B)`, one can
   **explicitly compute** witnesses `A' ⊆ A`, `B' ⊆ B` with
   `|A'|·|B'| ≥ ε^2·|A|·|B|` and `|d(A',B') − d(A,B)| > ε`.
3. The partition refinement step in the regularity proof
   (currently existential in
   `SzemerediRegularity.lean:327` via choice) becomes a concrete
   algorithm.

The gallery's parent file proves the regularity lemma
*non-constructively* (`refine ⟨1, fun V _ _ G _ _ => ⟨{Finset.univ}, …`
in `SzemerediRegularity.lean:336` — a vacuous witness for the
one-part case; the meaningful `m₀ ≤ parts.card` form at line 436
uses classical choice via `Classical` from
`SzemerediCore.lean:24`). OQ-04 asks us to **decouple** the
regularity statement from `Classical` for at least the witness
extraction step, yielding a `def findRegularPartition` returning a
concrete partition rather than `∃ parts, …`.

## Why It Matters

1. **Decidable / computable regularity**: the parent
   `IsEpsilonRegular` (`SzemerediCore.lean:39`) is a universally
   quantified `Prop` and is *not* `Decidable` (the quantifier
   ranges over arbitrary `Finset V`). ADLRY 1994 supplies a
   *decidable surrogate* — testing regularity of a single pair
   reduces to a polynomial number of inner-product computations
   over the bipartite adjacency matrix. Formalizing this surrogate
   gives `Decidable (IsEpsilonRegular G eps A B)` (with a small
   slack constant), which the existential version does not.

2. **Removes `Classical` dependency** from the partition
   construction: the proof in
   `SzemerediRegularity.lean:32` opens `Classical` (line 24 of
   `SzemerediCore.lean`) explicitly. ADLRY's algorithm gives a
   constructive witness function, eliminating one of the few uses
   of `Classical.choice` in the Szemerédi pipeline.

3. **Marquee initiative dependency**: per the project memory's
   *Szemerédi Pipeline Architecture*, the long-term plan is to use
   the regularity lemma as a building block for Roth, removal,
   counting, and ultimately full Szemerédi. Each of those uses the
   *partition itself*, not just its existence, so a computable
   `findRegularPartition` is a prerequisite for any down-stream
   *quantitative* gallery entry.

4. **Mathlib relevance**: Mathlib has the regularity lemma as
   `SimpleGraph.szemeredi_regularity` (existential). The ADLRY
   algorithm has *no Mathlib representation*. A clean Lean 4 port
   is a candidate Mathlib contribution.

## Mathematical Specification

### ADLRY's irregularity-witness lemma (informal)

For a bipartite pair `(A, B)` in `G`, define the *bipartite
adjacency matrix* `M_{AB} ∈ {0,1}^{A × B}`. ADLRY shows that
`(A, B)` is `ε`-regular (or *witness-regular*, a slightly weaker
notion) iff the matrix `M_{AB}`'s second-largest singular value is
at most `ε^{O(1)}·sqrt(|A|·|B|)`. The witness for irregularity is
then read off from the top singular vector.

For our purposes we can use a strictly combinatorial surrogate
(no SVD): for every `B' ⊆ B`, define

  `defect(B') := Σ_{a ∈ A} ( |N(a) ∩ B'| − d(A,B)·|B'| )^2`.

`(A, B)` is `ε`-regular iff `Σ_{B' ⊆ B with |B'| ≥ ε|B|} defect(B') ≤ ε^c·|A|·|B|^2`
for some explicit `c`. This is decidable (a finite sum over
finitely many subsets — exponentially many, but *finite*; ADLRY's
polynomial-time observation is that the maximum over `B'` is
attained at one of `≤ |A|^2` specific subsets defined by the
adjacency pattern).

### Three Lean-level targets

**Target A (S2)** — Decidable surrogate for `IsEpsilonRegular`.

  Define `IsWitnessRegular G eps A B : Prop` as a *decidable*
  predicate equivalent (up to a slack constant) to
  `IsEpsilonRegular G (eps/c) A B`. Provide a `Decidable`
  instance and the implication
  `IsWitnessRegular G eps A B → IsEpsilonRegular G eps A B`
  (the converse direction is the ADLRY equivalence and is
  deferred to a later iteration).

**Target B (S3)** — Constructive witness extraction.

  `def witnessOfIrregular : ¬ IsWitnessRegular G eps A B →
    Σ' (A' : Finset V) (B' : Finset V), …` — given a proof of
  non-regularity, produce explicit subsets witnessing it. This
  upgrades `Classical.choice` to a Σ'-elimination.

**Target C (S4–S5)** — Constructive regularity lemma.

  `def findRegularPartition (eps : ℚ) (G : SimpleGraph V) :
    Finset (Finset V)` returning a partition that satisfies
  `IsRegularPartition G eps`. Currently the existential is at
  `SzemerediRegularity.lean:327`; the constructive version
  threads the witness extractor of Target B through the energy
  increment step (`SzemerediRegularity.lean:225`-ish).

OQ-04 in its strongest reading subsumes all three. **For S1 we
limit scope to Target A's specification** — locking down the
decidable surrogate's exact form is the *load-bearing* design
decision.

## Scope Boundary (this slug)

In scope:

- A computable / `Decidable` analog of `IsEpsilonRegular`.
- A formal statement of "ADLRY equivalence" with a slack
  constant: `IsWitnessRegular G eps A B → IsEpsilonRegular G eps A B`.
- Constructive witness extraction (Target B).
- Optional: constructive partition (Target C) if Target A+B
  shake out cleanly.

Out of scope:

- Full polynomial-time complexity bound (Lean 4 has no
  cost-model machinery; the surrogate's polynomial-time runtime
  is a meta-claim).
- Singular-value-decomposition path (ADLRY's matrix formulation).
- Spectral surrogate via `Matrix.eigenvalues` — heavy Mathlib
  detour with little payoff over the combinatorial surrogate.

## Estimate

≈ 400–500 lines across 4–5 sessions:

- **S1 (this session)**: OBSERVE survey, target hierarchy
  (A/B/C), decidable-surrogate specification. **No Lean changes.**
- **S2**: ACT — `IsWitnessRegular` definition + `Decidable`
  instance + one-directional implication
  `IsWitnessRegular → IsEpsilonRegular` (with proof). Expect
  ~150 lines.
- **S3**: ACT — `witnessOfIrregular` Σ'-elimination from a
  failure of `IsWitnessRegular`. Expect ~100 lines.
- **S4**: ACT — constructive partition build over the existing
  energy-increment lemma in `SzemerediRegularity.lean:225`.
- **S5** (optional): export a `findRegularPartition` definition
  with the appropriate quantitative bound `M(ε)` and the
  corresponding `IsRegularPartition` theorem.

## References

- Alon, N., Duke, R.A., Lefmann, H., Rödl, V., Yuster, R. (1994).
  "The algorithmic aspects of the regularity lemma." *J. Algorithms*
  16(1), 80–109. — the foundational paper for this slug.
- Frieze, A., Kannan, R. (1996). "The regularity lemma and
  approximation schemes for dense problems." *FOCS '96*. —
  simpler approximation-scheme proof.
- Fischer, E., Matsliah, A., Shapira, A. (2010). "Approximate
  hypergraph partitioning and applications." *SIAM J. Comput.*
  39(7), 3155–3185. — modern algorithmic perspective; hypergraph
  generalization relevant to `szemeredi-hypergraph-core`.

## Mathlib mapping (v4.26.0)

| Need | Mathlib symbol | Status |
|---|---|---|
| Edge density (gallery) | `Szemeredi.Core.edgeDensity` | available (`SzemerediCore.lean:31`) |
| Edge density (Mathlib) | `SimpleGraph.edgeDensity` | available; gallery proves equivalence at `SzemerediRegularity.lean:362` |
| `IsEpsilonRegular` (gallery) | `Szemeredi.Core.IsEpsilonRegular` | available (`SzemerediCore.lean:39`) |
| Mathlib regularity | `SimpleGraph.szemeredi_regularity` | available (existential) |
| `Decidable IsEpsilonRegular` | — | **missing** — universal quantifier over `Finset V` |
| Constructive witness `(A', B')` for irregular pair | — | **missing** |
| Constructive partition (computable `findRegularPartition`) | — | **missing** |
| Bipartite adjacency matrix | `SimpleGraph.adjMatrix` | available |
| Singular value decomposition (would enable ADLRY's spectral path) | — | **not present** |

## Honesty notes

- This is a **formalization** task, not a research result. ADLRY
  1994 is 30 years old; the combinatorial surrogate is
  well-documented in textbooks (Tao's *Higher-order Fourier
  analysis* and Zhao's *Graph theory and additive combinatorics*).
- The "polynomial time" claim is meta-level. Lean 4 has no cost
  model; the surrogate's runtime is an external property of the
  `decide` tactic on the surrogate predicate, not provable
  within Lean.
- The slug is a stepping stone for downstream Szemerédi
  formalizations rather than a standalone deliverable. The S5
  exit criterion is `def findRegularPartition` + the
  corresponding `IsRegularPartition` theorem, which then
  *replaces* the existential `regularity_lemma_strong` at
  `SzemerediRegularity.lean:436` in any downstream caller.
