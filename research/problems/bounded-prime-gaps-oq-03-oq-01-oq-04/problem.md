# Problem: Prove D(4)=8 from Scratch

**Slug**: bounded-prime-gaps-oq-03-oq-01-oq-04
**Created**: 2026-04-04T02:46:36-07:00
**Status**: Active
**Source**: bounded-prime-gaps-oq-03-oq-01 <!-- gallery-gap -->

## Problem Statement

Can D(4) = 8 be proved from scratch, extending the known pattern D(2)=2, D(3)=6?

D(k) is the diameter of admissible k-tuples: the smallest D such that there exists an
admissible k-tuple in {0,...,D}. For k=4, D(4)=8 means the tuple {0,2,6,8} is admissible
and no smaller span works.

## Context

- Source: `bounded-prime-gaps-oq-03-oq-01` (Improving the 246 Bound)
- Category: extension (number theory, prime gaps)
- Tractability: challenging but concrete (decidable computation)

## First Steps

1. Find admissible tuple definition in gallery proof
2. Prove {0,2,6,8} is admissible (no prime ≤ 4 divides all residues)
3. Prove no tuple with span < 8 is admissible for k=4
