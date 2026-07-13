# Problem: Class Equation for Finite Groups

**Slug**: `lagrange-theorem-oq-02-oq-02`
**Parent**: `lagrange-theorem` (Lagrange's theorem for finite groups)
**Tier**: B
**Status**: VERIFIED (file at 0 sorries, gallery `status: verified`)

## Problem statement

### Plain language

Formalize the **class equation** for finite groups:

$$ |G| \;=\; |Z(G)| \;+\; \sum_{\substack{[x] \\ \text{non-central}}} [G : C_G(x)] $$

where the sum is over a complete set of representatives of non-central
conjugacy classes, and each `[G : C_G(x)]` equals the size of the
conjugacy class `[x]` by the orbit-stabilizer theorem.

### Formal statement (Lean-side)

```lean
theorem class_equation {G : Type*} [Group G] :
    Nat.card (center G) +
      ∑ x ∈ (ConjClasses.noncenter G).toFinset, Nat.card (Quotient.out x).carrier
    = Nat.card G

theorem card_conjClass_eq_centralizer_index [Fintype G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (centralizer {x}).index
```

(Plus 11 supporting / corollary results — `conj_orbit_eq_carrier`,
`conj_stabilizer_eq_centralizer`, `card_conjClass_eq_one_iff_mem_center`,
`pgroup_fixed_point`, `center_nontrivial_of_pgroup`, `p_sq_group_comm`,
and four `A_4`-specific calculations via `native_decide` /
`Mathlib.GroupTheory.SpecificGroups.Alternating`.)

## Why this matters

1. **Cornerstone of group theory** — Class equation underpins:
   - p-group center non-triviality (Cauchy / Sylow precursor),
   - "groups of order p² are abelian",
   - Burnside's normal-p-complement theorem,
   - character theory's orthogonality relations.

2. **Pedagogical bridge to Burnside / Sylow** — Sets up the
   counting argument used throughout group theory's bread-and-butter
   structural theorems.

3. **Mathlib-anchored verification** — Mathlib already provides
   `Group.nat_card_center_add_sum_card_noncenter_eq_card` in
   `Mathlib.GroupTheory.ClassEquation`. This slug wraps it with
   the orbit-centralizer index formula and standard corollaries.

## Classification

```yaml
tier: B
significance: 5
tractability: 8
tags:
  - seeker-selected
  - gallery-extracted
  - group-theory
  - class-equation
  - conjugacy-classes
  - p-groups
  - orbit-stabilizer
```

**Significance 5/10**: Standard textbook result. Important but not
distinguishing — appears in any first-semester graduate algebra course.

**Tractability 8/10**: Mathlib has the class equation directly
(`Group.nat_card_center_add_sum_card_noncenter_eq_card`). The work is
wrapping it with the orbit-centralizer index formula and corollaries,
not deriving the equation from scratch.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `lagrange-theorem` | Parent: classical Lagrange |
| `lagrange-theorem-oq-01` | Sibling: index version |
| `lagrange-theorem-oq-02` | Sibling: Cauchy's theorem (orbit-counting precursor) |
| `lagrange-theorem-oq-02-oq-02-oq-01` | Sibling: Burnside class-equation corollary (independent slug) |
| `burnside-counting` | Cousin: Burnside lemma (uses centralizer counting analogously) |
| `sylow-theorems` | Cousin: Sylow theorems (Class-equation-based p-group structure) |

## Out of scope (for this slug)

- Burnside lemma — handled in `burnside-counting`.
- Sylow theorems — handled in `sylow-theorems`.
- Character orthogonality — handled in `character-theory` (if present).
- General representation-theoretic class function decomposition — separate slug.

## References

* Mathlib4: `Group.nat_card_center_add_sum_card_noncenter_eq_card` in
  `Mathlib.GroupTheory.ClassEquation`.
* Mathlib4: `MulAction.orbitEquivQuotientStabilizer` in
  `Mathlib.GroupTheory.GroupAction.Basic`.
* Mathlib4: `ConjAct.stabilizer_eq_centralizer` in
  `Mathlib.GroupTheory.GroupAction.ConjAct`.
* Dummit & Foote, *Abstract Algebra* (3rd ed.), §4.3 (Conjugacy and
  the Class Equation).
* Lang, *Algebra* (rev. 3rd ed.), §I.6.
