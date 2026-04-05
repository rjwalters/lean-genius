# Problem: Möbius Inversion on Boolean Lattice

**Slug**: inclusion-exclusion-oq-02
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{If } g(S) = \sum_{T \subseteq S} f(T), \text{ then } f(S) = \sum_{T \subseteq S} (-1)^{|S \setminus T|} g(T)
$$

For all functions f, g : 2^[n] → ℤ satisfying the above "zeta transform" relation.

### Plain Language

The Möbius inversion formula on the Boolean lattice (power set ordered by inclusion)
says: if you can write g in terms of f by summing over all subsets, you can recover f
from g by the alternating signed sum. This is the precise algebraic reason why
inclusion-exclusion works.

In Lean:
```lean
theorem mobius_inversion_boolean_lattice {α : Type*} [DecidableEq α]
    (f g : Finset α → ℤ) (S : Finset α)
    (h : ∀ T, g T = ∑ U ∈ T.powerset, f U) :
    f S = ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S.card - T.card) * g T
```

### Why This Matters

The Möbius inversion formula on the Boolean lattice is the algebraic backbone of
inclusion-exclusion: it explains *why* the alternating signs work. This fills a
conceptual gap between the gallery's concrete IE proofs (`inclusion-exclusion`,
`inclusion-exclusion-oq-01`) and their lattice-theoretic foundation.

The Boolean lattice Möbius function μ(A, B) = (-1)^{|B\A|} (for A ⊆ B) is the
simplest instance of Möbius inversion on posets (Rota 1964). Proving it from first
principles in Lean connects the combinatorial and algebraic perspectives.

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - combinatorics
  - algebra
  - mobius-inversion
  - lattice-theory
  - inclusion-exclusion
  - seeker-selected
```

**Significance**: 7/10 — Foundational algebraic result explaining inclusion-exclusion;
connects the concrete gallery proofs to abstract Möbius theory.

**Tractability**: 6/10 — The proof is inductive over subsets. Mathlib has `Finset.sum_powerset`
and related tools. The key step is showing the double sum telescopes. Likely 1-2 sessions.

## Known Gallery Context

### What's Already Proved

- **`inclusion-exclusion`** (verified/mathlib): 2-set and 3-set IE formula, symmetric difference
- **`inclusion-exclusion-oq-01`** (verified): Euler's totient, surjection counting, derangement formula, Stirling/Bell numbers via IE
- **`InclusionExclusionOQ03.lean`**: Uses `Finset.sum_comm'` and `Finset.mem_powerset` for more advanced IE arguments

### What's Still Open (OQ-02 Goal)

- The *abstract* Möbius inversion theorem for the Boolean lattice
- The connection: IE = Möbius inversion specialized to 2^[n]
- Possibly: the incidence algebra interpretation (if Mathlib has `IncidenceAlgebra`)

## Proof Approach

### Approach 1: Direct Induction on |S| (Most Tractable)

Induct on |S|. For the base case |S| = 0, both sides equal f(∅). For the inductive step,
expand g(T) using the hypothesis and exchange the order of summation.

Key step (double sum telescoping):
```
∑_{T⊆S} (-1)^{|S\T|} g(T)
  = ∑_{T⊆S} (-1)^{|S\T|} ∑_{U⊆T} f(U)
  = ∑_{U⊆S} f(U) · ∑_{T: U⊆T⊆S} (-1)^{|S\T|}
```

The inner sum `∑_{T: U⊆T⊆S} (-1)^{|S\T|}` = [S = U] (1 if S = U, 0 otherwise).
This is the key combinatorial identity: `∑_{k=0}^n (-1)^k C(n,k) = [n=0]`.

In Lean, this uses:
- `Finset.sum_comm` to swap order of summation
- `Finset.sum_powerset_insert` or `Finset.sum_powerset`
- The alternating binomial identity `∑ (-1)^k C(n,k) = 0` for n ≥ 1 (already in `InclusionExclusionOQ01.lean`)

### Approach 2: Via Mathlib's Incidence Algebra

Mathlib4 has `Algebra.IncidenceAlgebra` (`Mathlib.Algebra.IncidenceAlgebra.Basic`).
The Möbius function `mobiusAlgebra` for `Finset` ordered by inclusion might give a
one-line proof. Check `LocallyFiniteOrder` instance for `Finset`.

Look for: `MobiusInversion`, `zeta_mul_mobius`, `LocallyFiniteOrder (Finset α)`

### Approach 3: Explicit Witness for Boolean Lattice

Define the Möbius function for Boolean lattice directly:
```lean
def boolMobius (S T : Finset α) : ℤ :=
  if T ⊆ S then (-1 : ℤ) ^ (S.card - T.card) else 0
```
Then prove the defining property: `∑_T boolMobius S T = [S = ∅]`.

### Key Difficulties

- **Sum swapping**: Lean's `Finset.sum_comm` requires careful type setup when
  the inner sum's domain depends on the outer variable.
- **Powerset of powerset**: Need to show `{T | U ⊆ T ⊆ S}` is `(S \ U).powerset.image (· ∪ U)`.
- **Alternating binomial vanishing**: `∑ k : Fin (n+1), (-1)^k.val * C(n, k.val) = 0` for n ≥ 1.
  This is `InclusionExclusionOQ01.alternating_binomial_sum` if it's in the gallery.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `inclusion-exclusion` | Base proof: 2-set and 3-set IE formula |
| `inclusion-exclusion-oq-01` | Applications: this result generalizes the IE principle used there |
| `InclusionExclusionOQ03.lean` | Uses powerset sum techniques relevant here |

## References

### Papers
- Rota, G.-C. (1964). "On the foundations of combinatorial theory I. Theory of Möbius functions." *Zeitschrift für Wahrscheinlichkeitstheorie*, 2(4), 340–368.

### Mathlib
- `Algebra.IncidenceAlgebra.Basic` — Abstract Möbius inversion (check if Boolean lattice instance exists)
- `Mathlib.Data.Finset.Powerset` — `Finset.sum_powerset`, `Finset.mem_powerset`
- `Mathlib.Data.Finset.Lattice.Basic` — Finset lattice operations
- `Finset.sum_comm` — Key for swapping summation order

## Metadata

```yaml
tags:
  - combinatorics
  - mobius-inversion
  - boolean-lattice
  - inclusion-exclusion
  - lattice-theory
related_proofs:
  - inclusion-exclusion
  - inclusion-exclusion-oq-01
difficulty: medium
source: gallery-gap
```
