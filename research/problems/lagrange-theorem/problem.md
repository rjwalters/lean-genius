# Hall's Theorem for Solvable Groups

## Source
Gallery proof: `lagrange-theorem` (open question #3)

## Problem Statement
Can Hall's theorem be formalized in Lean 4: for solvable groups, the full converse of Lagrange's theorem holds — subgroups of order n exist for every n dividing |G|?

## Mathematical Context
Lagrange's theorem states that the order of a subgroup divides the order of the group. The converse is false in general (A₄ has order 12 but no subgroup of order 6). However, Philip Hall proved that for **solvable groups**, the converse holds: if G is a finite solvable group and n divides |G|, then G has a subgroup of order n (a "Hall subgroup").

## Key Definitions Needed
- Solvable groups (available in Mathlib: `Group.IsSolvable`)
- Hall subgroups
- Sylow subgroups (foundation for Hall's proof)

## Suggested Approach
1. State Hall's theorem using Mathlib's solvable group API
2. Prove for p-groups first (Sylow theorems already in Mathlib)
3. Build up to the general solvable case via derived series

## Tractability
Challenging — Mathlib has strong group theory foundations but Hall's theorem itself is not yet formalized.

## Category
Extension of Lagrange's theorem
