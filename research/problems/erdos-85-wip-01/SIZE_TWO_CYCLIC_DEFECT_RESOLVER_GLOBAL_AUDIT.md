# Global defect-resolver audit

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## Question

Divergence round 12 proposed alternating between collision tokens and the
sharp duplicate/missing circulation.  The intended transition was

```text
agreement in fibre t
  -> reverse its two routes
  -> duplicate-to-t defect in the target fibre
  -> resolve against a missing-to-t defect
  -> a new agreement.
```

Such a transition would retain the source pair and target label, unlike the
already-refuted aggregate and local-cycle arguments.  This audit checks
whether the existing Lean interfaces actually define it.

## What route reversal retains

`SizeTwoCyclicRouteDart.reverse` is a genuine involution.  A dart represented
by source base `x`, source difference `t`, and row offset `r` reverses to the
dart with

```text
source base       x + r
source difference targetDifference x t r
row offset        -r.
```

Consequently
`sizeTwoCyclicTargetFiberRouteReverseEquiv code t u` is a base-resolved
bijection between the *individual routes* in the `t -> u` and `u -> t`
blocks.  This is stronger than block-cardinality symmetry, but it does not
preserve the original source base.

In particular, if base `x` supplies two routes from `t` into `u`, with
distinct offsets `r₁,r₂`, reversal produces routes based at `x+r₁` and
`x+r₂`.  It does **not** produce two routes at one base in fibre `u`.
Thus a local duplicate-to-`u` token does not reverse to a local
duplicate-to-`t` token.

## What circulation forgets

The theorem `sizeTwoCyclicSharpDefect_circulation` states only

```text
D(t,u) + M(u,t) = D(u,t) + M(t,u),
```

where `D` and `M` are cardinalities of sets of source bases.  Its proof first
rewrites each sharp `2,0,1,...,1` profile as

```text
route mass + missing indicator = q + duplicate indicator
```

and then uses symmetry of the *sum* of route multiplicities.  A missing
defect has no routed dart, so route reversal cannot act on it.  The equality
therefore gives no map between the four defect sets and no compatibility
with the base translation `x -> x+r`.

Finite-cardinality choice could manufacture an equivalence

```text
Dup(t,u) ⊎ Miss(u,t)  ≃  Dup(u,t) ⊎ Miss(t,u),
```

but it would be arbitrary.  It need not retain either base coordinate, the
two offsets of a collision, the owner pair, or any affine winding label.
An alternating cycle built from such choices has no invariant supplied by
the code.

The displacement-resolved theorem
`sizeTwoCyclicSharpDefect_cocycle` does not repair this loss.  It identifies
the duplicate *count* with a translated missing count using the pointwise
residue equation for their fibre labels; it still does not identify the base
realizing either defect.  The explicit q=8 theorem
`exists_sharpFlowCountermodelEight` confirms that all presently extracted
row-mass, deleted-fibre, displacement, and circulation equations can hold
without a packing contradiction.

## Sharp repair does not supply a physical resolver

`SharpFiberProfile` canonically records the two preimages of the duplicated
value.  Repairing either occurrence to the missing value produces one of two
abstract bijections and the repairs have opposite signs.  The repaired arrow
is not an edge of the reciprocal code: it is precisely the absent route.
Reversing it therefore has no justification from reciprocity.  Choosing one
of the two repairs also introduces the already-audited completion bit whose
bare sign is generic permutation bookkeeping.

## Cut and exact missing lemma

The defect-resolver alternating-cycle proposal is **cut at its first
transition**.  Existing results provide:

1. a canonical involution on actual darts;
2. a pointwise duplicate/missing fibre-label displacement; and
3. an aggregate circulation equality.

They do not provide a base-resolved duplicate-to-missing resolver.  A revival
must prove new code-specific structure of the following strength:

> For every relevant sharp defect, select one of its two duplicate darts and
> a missing defect in the transposed block so that the selected bases obey an
> explicit affine formula, and prove that these selections are compatible
> with route reversal globally.

Merely proving an equicardinality or choosing a matching is insufficient.
The selection must expose a preserved owner pair or a nonzero binary winding;
otherwise the q=8 sharp-flow countermodel and the arbitrary matching freedom
remain valid controls.  No such selection theorem is currently present in
the repository.

## Consequence for the live candidates

This cut favors candidates that never invent an absent route: simultaneous
row/column projections, an integral symmetric/divided square, or direct
analysis of the self-transpose locus.  Those operate on the full incidence
tensor.  The defect circulation may be used as their scalar shadow, but not
as a token transition graph.
