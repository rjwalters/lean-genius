# Problem: Coprime-Order Subgroups Intersect Trivially - the Gcd Refinement of Lagrange

**Slug**: lagrange-theorem-oq-10
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: lagrange-theorem

## Problem Statement

### Formal Statement

$$
|H \cap K| \mid \gcd(|H|,|K|), \qquad
\gcd(|H|,|K|)=1 \Rightarrow H \cap K = \{1\},
$$
and if additionally $|H|\cdot|K| = |G|$ then $G$ is the internal direct product of $H$ and $K$.

### Plain Language

Lagrange's theorem forces $|H|$ to divide $|G|$ for every subgroup. Applied to
$H \cap K \le H$ and $H \cap K \le K$ it yields the sharp refinement that $|H \cap K|$
divides $\gcd(|H|,|K|)$. Consequently, subgroups of coprime order meet only in the
identity, and when their orders additionally multiply to $|G|$ they form an internal
direct product $G \cong H \times K$. This coprimality corollary is the algebraic backbone
of Sylow decomposition and the CRT-style splitting of finite abelian groups.

### Why This Matters

Mathlib states only the coprime special case (`Subgroup.inf_eq_bot_of_coprime`); the
gcd-divisibility general form `|H ⊓ K| ∣ gcd(|H|,|K|)` is not stated. It is distinct from
every existing sibling (Sylow, orbit-stabilizer, tower law, exponent, Cauchy, pq-center):
those describe a single subgroup's order, not the arithmetic of subgroup **intersections**.

## Known Results

### What's Already Proven

- Parent `lagrange-theorem` is verified (0-axiom).
- Mathlib has `Subgroup.card_dvd_of_le`, `Subgroup.inf_eq_bot_of_coprime`,
  `Subgroup.isComplement'_of_coprime`.

### What's Still Open

- The target theorems below (currently `sorry`), especially the gcd-divisibility core.

### Our Goal

Prove the sketch below as a verified (0-axiom) child. Category: **generalization /
corollary**.

## Target Lean Sketch

```lean
variable {G : Type*} [Group G] [Finite G] (H K : Subgroup G)

/-- New core: intersection order divides the gcd of the orders. -/
theorem card_inf_dvd_gcd :
    Nat.card (H ⊓ K : Subgroup G) ∣ Nat.gcd (Nat.card H) (Nat.card K) := by
  sorry -- Nat.dvd_gcd (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

/-- Coprime orders force trivial intersection (reproved from the gcd core). -/
theorem inf_eq_bot_of_coprime_card
    (h : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ := by
  sorry -- Subgroup.card_eq_one + card_inf_dvd_gcd

/-- With matching product of orders, H and K complement: internal direct product. -/
theorem isComplement'_of_coprime_card
    (hmul : Nat.card H * Nat.card K = Nat.card G)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) : H.IsComplement' K := by
  sorry -- Subgroup.isComplement'_of_coprime
```

Plus `eq_one_of_mem_both` (a common element is the identity) and a concrete instance for
two subgroups of coprime prime orders $p \neq q$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `lagrange-theorem` | Parent: Lagrange's theorem | coset counting |
| `lagrange-theorem-oq-06` | Sibling: tower law (chain of subgroups) | index multiplicativity |
| `sylow-theorem` | Uses coprime-order splitting | p-groups |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: Everything descends from `Subgroup.card_dvd_of_le` (Lagrange on the
sublattice) plus elementary Nat gcd/coprime facts. One honest new derivation
(`card_inf_dvd_gcd`); the rest wrap confirmed Mathlib lemmas. No custom definitions or
decidability.

### Suggested First Steps

1. Prove `card_inf_dvd_gcd` via `Nat.dvd_gcd` and `Subgroup.card_dvd_of_le` on both
   `inf_le_left` and `inf_le_right`.
2. Derive `inf_eq_bot_of_coprime_card` from the gcd core plus `Subgroup.card_eq_one`.
3. Wrap `Subgroup.isComplement'_of_coprime` for the internal-direct-product form; add the
   coprime-prime-order instance.

## References

### Mathlib

- `Subgroup.card_dvd_of_le` — GroupTheory/Coset/Card.lean
- `Subgroup.card_subgroup_dvd_card` — GroupTheory/Coset/Card.lean (core Lagrange)
- `Subgroup.card_eq_one`, `Subgroup.inf_eq_bot_of_coprime` — GroupTheory/Index.lean
- `Subgroup.isComplement'_of_coprime`, `Subgroup.IsComplement'.QuotientMulEquiv` — GroupTheory/Complement.lean

### Literature

- Any first-course algebra text: Lagrange's theorem and internal direct products.

## Metadata

```yaml
tags:
  - group-theory
  - lagrange-theorem
  - subgroups
  - direct-products
related_proofs:
  - lagrange-theorem
  - lagrange-theorem-oq-06
  - sylow-theorem
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
