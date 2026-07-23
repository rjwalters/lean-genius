# Problem: Completing the Lean Formalization of Erdős #117 (Covering Groups by Abelian Subgroups)

**Slug**: erdos-117-wip-01
**Created**: 2026-07-09T17:33:20-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
h(n) = \inf\Bigl\{\, k \in \mathbb{N} : \text{every group } G \text{ with the } n\text{-commuting property is a union of } k \text{ Abelian subgroups} \,\Bigr\},
$$

where $G$ has the *$n$-commuting property* if every $(n+1)$-element subset of $G$ contains two distinct commuting elements. Pyber's theorem gives constants $c_2 > c_1 > 1$ with $c_1^{\,n} < h(n) < c_2^{\,n}$ for all large $n$; the trivial case is $h(1) = 1$.

### Plain Language

We want to strengthen the Lean 4 formalization of a still-open Erdős problem in combinatorial group theory. A group has the "$n$-commuting property" when any batch of $n+1$ elements is guaranteed to contain a commuting pair; $h(n)$ is the fewest Abelian subgroups needed to cover every such group. Pyber (1987) proved $h(n)$ grows exponentially, $c_1^n < h(n) < c_2^n$, but the exact base is unknown. The gallery entry `erdos-117` defines the $n$-commuting property, Abelian subgroups, and the covering number $h(n)$ via `sInf`, but states Pyber's bounds only as docstrings with no formal declarations. Our goal is to formalize the elementary and well-definedness facts that Mathlib can check — the trivial case $h(1) = 1$, basic properties of the covering set, and the fact that an Abelian group has the $n$-commuting property for all $n$ — while keeping Pyber's exponential bounds as clearly stated assumptions, since they are deep and the exact rate remains open.

### Why This Matters

1. **Turning docstrings into checked lemmas**: The entry's known results live only as prose; formalizing the trivial and structural facts converts commentary into machine-verified content and honestly delimits what is assumed.
2. **Reusable Ramsey-group-theory API**: Formal definitions of the $n$-commuting property, Abelian subgroups, and covering numbers via `sInf` give reusable Lean infrastructure at the interface of Ramsey theory and group theory, currently absent from Mathlib.
3. **Sharp assumption footprint on an open problem**: Because the exact base of $h(n)$ is genuinely open, cleanly isolating Pyber's upper and lower bounds as named assumptions makes the entry's status transparent and prevents any overclaim of resolution.

## Known Results

### What's Already Proven

- Pyber's exponential bounds: there exist $c_2 > c_1 > 1$ with $c_1^{\,n} < h(n) < c_2^{\,n}$ for all sufficiently large $n$ — Pyber (1987).
- The exponential lower bound was independently known to Isaacs.
- The trivial base case $h(1) = 1$: for $n = 1$ the property forces $G$ to be Abelian, so one Abelian subgroup ($G$ itself) covers it.
- Every Abelian group has the $n$-commuting property for all $n$, since every pair of elements commutes.

### What's Still Open

- Whether $h(n) = \Theta(c^n)$ for a single constant $c$, i.e. whether the exponential growth rate converges.
- The identity of the extremal groups achieving $h(n)$ (p-groups, wreath products, or otherwise).
- Whether Pyber's upper-bound constant $c_2$ can be improved with modern finite-group-theory tools.

### Our Goal

Strengthen `Proofs/Erdos117Problem.lean` by (i) formalizing the trivial case $h(1) = 1$ and the fact that Abelian groups satisfy the $n$-commuting property for all $n$; (ii) proving basic well-definedness properties of `abelianCoverNumber` (monotonicity in $n$ where applicable, and that the `sInf` is over a nonempty-or-correctly-handled set); and (iii) retaining Pyber's exponential upper and lower bounds as two explicitly named assumptions disclosed in `meta.json`. The result should maximize the formally-verified definitional core while keeping the deep, still-open exponential-rate content clearly assumed.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-117 | Direct parent entry; supplies `HasNCommutingProperty`, `IsAbelianSubgroup`, and `abelianCoverNumber` definitions and Pyber's bounds to be formalized | Finset cardinality, subgroups, `sInf` over $\mathbb{N}$ |
| erdos-116 | Companion Erdős entry with the same pattern of formal definitions plus axiomatized deep bounds | Structure definitions, assumption isolation |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Prove the trivial case $h(1) = 1$ and the Abelian-group instance directly from the definitions.
   - Why it might work: For $n = 1$, the $n$-commuting property says every $2$-element subset commutes, hence $G$ is Abelian and is covered by itself; this is a short `Finset`-cardinality argument well within Mathlib.
   - Risk: The `sInf`-based `abelianCoverNumber` quantifies over all types/groups, so establishing membership in the covering set requires careful universe and quantifier handling.

2. **Approach B**: Establish well-definedness and monotonicity lemmas for `abelianCoverNumber`, deferring the Abelian-instance proof.
   - Why it might work: Monotonicity and non-emptiness facts about `sInf` over $\mathbb{N}$ are directly supported by `Nat.sInf` lemmas in Mathlib and give robust structural progress.
   - Risk: If the covering set is empty for some $n$ in the current encoding, `sInf` returns $0$, so the definition may need tightening before monotonicity is even true.

### Key Difficulties

- Pyber's exponential bounds rely on deep finite-group structure theory (bounded-index nilpotent subgroups, efficient Abelian covers) far beyond Mathlib, so they must remain assumptions.
- The universal quantification over all groups inside `abelianCoverNumber` makes even elementary membership arguments delicate with respect to universes and `sInf` conventions.

### What Would a Proof Need?

- Key lemma 1: For $n = 1$, the $n$-commuting property implies $G$ is Abelian, hence covered by one Abelian subgroup, giving $h(1) = 1$.
- Key lemma 2: Every Abelian group satisfies `HasNCommutingProperty G n` for all $n$.
- Technical requirements: A tightened `abelianCoverNumber` whose `sInf` set is provably nonempty or correctly handled, plus Pyber's two exponential bounds stated as disclosed assumptions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The tractable targets ($h(1) = 1$, the Abelian instance, `sInf` bookkeeping) are elementary `Finset`/subgroup arguments supported by Mathlib's group-theory library.
- Similar Erdős entries formalize definitions and trivial cases while assuming the deep bounds; the same division of labor applies cleanly here.
- Mathlib provides `Subgroup`, `Finset.card`, and `Nat.sInf`, sufficient for the definitional lemmas though not for Pyber's structure theory.

**Estimated Effort**:
- Exploration: 1–2 days to understand the `sInf` encoding and universe issues.
- If tractable: 1–2 weeks to formalize the trivial case, the Abelian instance, and well-definedness.
- If hard: Pyber's exponential bounds and the open exact rate remain assumptions.

## References

### Papers
- Pyber, "The number of pairwise non-commuting elements and the index of the centre in a finite group" / related covering work (1987) — the exponential bounds $c_1^n < h(n) < c_2^n$.
- Erdős, problem lists (1990, 1997) — original posing of the covering question.
- Isaacs — independent exponential lower bound.

### Online Resources
- https://erdosproblems.com/117 — problem statement and status.

### Mathlib
- Mathlib.GroupTheory.Subgroup.Basic — `Subgroup` type and Abelian-subgroup reasoning.
- Mathlib.Data.Finset.Card — `Finset.card` for the $(n+1)$-subset condition.
- Mathlib.Order.ConditionallyCompleteLattice.Basic — `Nat.sInf` / `sInf` for the covering number.

## Metadata

```yaml
tags:
  - group-theory
  - abelian-subgroups
  - covering-number
  - ramsey-theory
  - erdos-problems
  - formalization
related_proofs:
  - erdos-117
  - erdos-116
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:20-07:00
```

**Significance**: 6/10
**Tractability**: 6/10

## Adversarial Checklist (claim: h(3) = 3, exact and unconditional)

Recorded 2026-07-23 for the SOLVED claim `abelianCoverNumber_three : abelianCoverNumber.{u} 3 = 3`
in `Erdos117WIP01Exact.lean`. How THIS claim could be wrong:

- **sInf ∅ = 0 degeneracy**: the equality is only meaningful if the covering set is
  nonempty — confirm `coversWithAbelian_three_three : CoversWithAbelian 3 3` is a
  genuine membership proof (a uniform 3-cover for EVERY finite group in the universe
  with the property), not a vacuous or classical trick. `coversWithAbelian_three_nonempty`
  must be derived from it, not assumed.
- **Universe quantification**: `abelianCoverNumber.{u}` quantifies over `G : Type u`
  only. Confirm the cover proof (`exists_three_abelian_cover`) is universe-agnostic
  (`{G : Type*}`) so the membership holds at EVERY `u`, and the lower bound transports
  `Q₈` via `ULift` (in `Three.lean`) — no universe mismatch making either bound vacuous.
- **Wrong property orientation**: `HasNCommutingProperty G 3` = "every subset of card
  > 3 (i.e. ≥ 4) contains two DISTINCT commuting elements" — confirm the clique
  argument uses card-4 subsets (`no_four_clique` builds `{w,x,y,z}` with card = 4 > 3),
  not card-3, and that distinctness is derived (non-commuting ⟹ distinct), not assumed.
- **Cover but not abelian / abelian but not cover**: the three subgroups must satisfy
  BOTH conjuncts: `centralizer_abelian_of_three` needs the 5-case analysis to be
  exhaustive — cases (b~u,b~v), (b~u,¬b~v), (¬b~u,b~v), (¬b~u,¬b~v,b~uv),
  (¬b~u,¬b~v,¬b~uv) cover all of {T,F}³ restricted to reachable combinations. Confirm
  the mirror case really is `centralizer_case_left` with u,v swapped (huv symm'd).
- **Lower-bound circularity**: `three_le_abelianCoverNumber_three` (Q₈, from
  `Three.lean`) must not depend on any nonemptiness assumption other than the one now
  proved; confirm `#print axioms abelianCoverNumber_three` = propext/Classical.choice/
  Quot.sound only (verified in build log 2026-07-23, 8582 jobs).
- **Not the parent problem**: h(3) = 3 is one exact ladder value; Erdős #117 proper
  (the exponential growth base, Pyber's c₁ⁿ < h(n) < c₂ⁿ) remains OPEN and is NOT
  claimed. h(n) for n ≥ 4 remains open (well-definedness included).
