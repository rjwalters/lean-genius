# Problem: Sylow Theorem: Complexity of Finding All Sylow p-Subgroups

**Slug**: sylow-theorem-oq-02
**Created**: 2026-04-23T02:30:21+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{What is the complexity class of the problem: given a finite group } G
\text{ by generators and relations, and a prime } p \mid |G|,
\text{ enumerate all Sylow } p\text{-subgroups of } G?
$$

More precisely, define:

$$
\textsc{SylowEnum}(G, p) = \{ H \leq G : |H| = p^k,\ p \nmid [G:H] \}
$$

The tractable Lean target: formalize a verified enumeration procedure using the orbit
$\{g \cdot P \mid g \in G\}$ of a fixed Sylow subgroup $P$, and prove its cardinality
equals $[G : N_G(P)]$ via the orbit-stabilizer theorem.

### Plain Language

Sylow's theorems guarantee that every finite group has Sylow $p$-subgroups (for each prime $p$
dividing the group order), and that they are all conjugate. But they are existential — they
say subgroups **exist** without giving an efficient algorithm to **find** them.

The question is: given a finite group by generators and relations, how hard is it to find
or list all Sylow $p$-subgroups? We cannot resolve the open complexity question in Lean, but
we can formalize a verified orbit-enumeration procedure with certified cardinality bounds.

### Why This Matters

1. **Computational group theory**: Sylow subgroup computation is a core primitive in
   group theory algorithms (GAP, Magma). Its complexity determines what is feasible.
2. **Lean formalization angle**: Mathlib has existential Sylow theory but not a
   constructive enumeration with orbit bounds. Formalizing the orbit procedure bridges
   the existential and constructive perspectives.
3. **Bridge to Mathlib**: `Mathlib.GroupTheory.Sylow` has `Sylow`, conjugacy, and
   count congruence. This problem extends it to the orbit-based enumeration setting.

## Known Results

### What's Already Proven

- **Sylow existence**: Every finite group has a Sylow $p$-subgroup — in gallery and Mathlib
- **Conjugacy**: All Sylow $p$-subgroups are conjugate — also in gallery and Mathlib
- **Count bound**: $n_p \equiv 1 \pmod{p}$ and $n_p \mid [G : P]$ — in Mathlib
- **Solvable groups**: Polynomial-time algorithms exist (Hall's theorem + Schur-Zassenhaus)
- **Orbit-stabilizer**: $|G| = |{\rm orb}(x)| \cdot |{\rm stab}(x)|$ — in Mathlib

### What's Still Open

- General complexity of Sylow enumeration for arbitrary finite presentations
- Whether the enumeration problem is in $\mathsf{P}$ for all finite groups
- Formal Lean verification of the polynomial-time solvable group algorithm

### Our Goal

**Option A** (recommended): Formalize the orbit enumeration. Given a fixed Sylow $p$-subgroup
`P : Sylow p G`, construct `Finset.image (· • P.toSubgroup) (Finset.univ : Finset G)` and
prove its cardinality equals `Nat.card G / Nat.card (P.toSubgroup.normalizer)`.

**Option B**: Formalize the unique Sylow product decomposition for nilpotent groups.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `sylow-theorem` | Parent proof — existence and conjugacy, 0 sorries | Lagrange, coset counting |
| `sylow-theorem-oq-04` | Schur-Zassenhaus (sibling OQ) | Extension theory, Hall subgroups |
| `chinese-remainder-non-coprime` | CRT — related to direct product decompositions | Group/ring homomorphisms |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Conjugation orbit enumeration** (recommended):
   All Sylow $p$-subgroups form the orbit of one under conjugation by $G$. Formalize:
   `{H : Sylow p G} = MulAction.orbit (ConjAct G) P` as a `Finset`, then invoke
   orbit-stabilizer to get `card = [G : N_G(P)]`.
   - Why it might work: `MulAction.orbit_eq_univ_iff_transitive` and Mathlib's
     `Sylow.conj_eq` establish transitivity; `card_orbit_mul_card_stabilizer` gives count.
   - Risk: The `ConjAct` action on Sylow types may require coercion boilerplate.

2. **Approach B — Nilpotent unique Sylow product**:
   For nilpotent $G$, each Sylow $p$-subgroup is unique (hence normal), and
   $G \cong \prod_p P_p$. Formalize this as a `MulEquiv`.
   - Why it might work: Mathlib has `IsNilpotent` and direct product lemmas.
   - Risk: The full decomposition may require significant new theory.

### Key Difficulties

- `Sylow p G` in Mathlib is a type with coercion to `Subgroup G`; orbit constructions
  need to work at the type level or require explicit coercions.
- The complexity question itself is metamathematical and cannot be formalized directly.
- Constructive enumeration may require decidability instances not yet in Mathlib.

### What Would a Proof Need?

- `Sylow.card_sylow_prime_pow_dvd`: count bound $n_p \mid [G:P]$
- `MulAction.card_orbit_mul_card_stabilizer`: $|G| = |\text{orb}| \cdot |\text{stab}|$
- `Subgroup.normalizer`: normalizer of a subgroup, `N_G(P)`
- `Finset.image` over `G` to construct the orbit as a finite set

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Existential Sylow theory is fully in Mathlib; Option A adds constructive enumeration.
- All component lemmas (orbit-stabilizer, conjugacy, count) are in Mathlib.
- The bottleneck is connecting `Sylow p G` type to `MulAction.orbit` machinery.

**Estimated Effort**:
- Exploration: 2-4 hours (auditing Mathlib `GroupTheory.Sylow` and `MulAction`)
- If Option A tractable: 1-2 days
- If coercion issues deep: 1 week

## References

### Papers
- Kantor, W.M. (1985). "Sylow's theorem in polynomial time." *JCSS* 30(2): 359–394.
- Luks, E.M. (1993). "Permutation groups and polynomial-time computation." *DIMACS* 11: 139–175.

### Mathlib
- `Mathlib.GroupTheory.Sylow` — `Sylow` type, existence, conjugacy, `card_sylow_prime_pow_dvd`
- `Mathlib.GroupTheory.GroupAction.Basic` — orbit-stabilizer, `MulAction.orbit`
- `Mathlib.GroupTheory.Nilpotent` — `IsNilpotent`, nilpotent decomposition

## Metadata

```yaml
tags:
  - group-theory
  - computational-complexity
  - sylow-theory
  - orbit-enumeration
  - formalization
related_proofs:
  - sylow-theorem
  - sylow-theorem-oq-04
difficulty: medium
source: gallery-gap
created: 2026-04-23T02:30:21+02:00
```

**Significance**: 7/10
**Tractability**: 5/10
