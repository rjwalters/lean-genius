# Problem: Groups of Order p² are Abelian

**Slug**: sylow-theorem-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: sylow-theorem

## Problem Statement

### Formal Statement

$$
|G| = p^2,\ p \text{ prime}\ \Rightarrow\ \forall\, a,b \in G,\ ab = ba
$$

### Plain Language

Let $p$ be a prime and $G$ a group of order exactly $p^2$. Then $G$ is abelian; consequently
$G \cong \mathbb{Z}/p^2$ or $G \cong \mathbb{Z}/p \times \mathbb{Z}/p$. The proof rests on the
fact that a nontrivial finite $p$-group has nontrivial center: $|Z(G)| \in \{p, p^2\}$. If
$|Z(G)| = p^2$ then $G$ is abelian directly; if $|Z(G)| = p$ then $G/Z(G)$ has order $p$,
hence is cyclic, and a group whose central quotient is cyclic is itself abelian — forcing
$|Z(G)| = p^2$, a contradiction. Either way $G$ is commutative.

### Why This Matters

This is the prime-square case of small-group classification and complements the sibling
entries that classify groups of order $pq$: it handles the one remaining two-prime-power
order type. None of the 9 existing siblings treat prime-square order (oq-01 and oq-03-oq-02
do order $pq$ with *distinct* primes; the oq-02 branch covers orbit counting / nilpotency /
characteristic Sylow subgroups; oq-03/oq-03-oq-01 are Schur–Zassenhaus; oq-04 is simplicity
of $A_5$).

## Known Results

### What's Already Proven

- Parent entry `sylow-theorem` is verified (0-axiom).
- Mathlib supplies `IsPGroup.commutative_of_card_eq_prime_sq` — the exact result — requiring
  only `[Group G] [Fact p.Prime]` and `Nat.card G = p^2` (finiteness derived internally).

### What's Still Open

- The headline below (currently `sorry`) plus its unfolded pedagogical proof and corollaries.

### Our Goal

Prove the sketch below as a verified (0-axiom) child of `sylow-theorem`.
Category: **extension** (finite-group classification).

## Target Lean Sketch

```lean
theorem group_of_prime_sq_abelian (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    (hG : Nat.card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
  IsPGroup.commutative_of_card_eq_prime_sq hG

-- substance beyond the re-export: center is everything, plus small examples
theorem center_eq_top_of_prime_sq (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    (hG : Nat.card G = p ^ 2) : Subgroup.center G = ⊤ := by sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `sylow-theorem` | Parent: Sylow's theorems | p-groups, group actions |
| `sylow-theorem-oq-01` | Sibling: groups of order pq | Sylow counting |
| `sylow-theorem-oq-04` | Sibling: simplicity of A₅ | conjugacy classes |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: The headline closes in one line with a Mathlib lemma; the entry's value
is a pedagogically unfolded proof (center dichotomy) and concrete instantiations (order 4,
order 9).

### Suggested First Steps

1. Close `group_of_prime_sq_abelian` with `IsPGroup.commutative_of_card_eq_prime_sq hG`.
2. Add `center_eq_top_of_prime_sq` and small `example`s at `p = 2` (order 4), `p = 3`
   (order 9).
3. Write an unfolded proof sketch in the docstring using `center_nontrivial`,
   `card_center_eq_prime_pow`, `cyclic_center_quotient_of_card_eq_prime_sq`,
   `commutative_of_cyclic_center_quotient` — explaining the $|Z(G)| \in \{p, p^2\}$ dichotomy.

## References

### Mathlib

- `IsPGroup.commutative_of_card_eq_prime_sq` — GroupTheory/PGroup.lean (the exact result)
- `IsPGroup.commGroupOfCardEqPrimeSq` — GroupTheory/PGroup.lean (CommGroup instance)
- `IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq` — GroupTheory/PGroup.lean
- `IsPGroup.center_nontrivial` — GroupTheory/PGroup.lean
- `IsPGroup.card_center_eq_prime_pow` — GroupTheory/PGroup.lean
- `commutative_of_cyclic_center_quotient` — GroupTheory/SpecificGroups/Cyclic.lean

## Metadata

```yaml
tags:
  - group-theory
  - sylow
  - p-groups
  - finite-group-classification
  - abelian-groups
related_proofs:
  - sylow-theorem
  - sylow-theorem-oq-01
  - sylow-theorem-oq-04
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
