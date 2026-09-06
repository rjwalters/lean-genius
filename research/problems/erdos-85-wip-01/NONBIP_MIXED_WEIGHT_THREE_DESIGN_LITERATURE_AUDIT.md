# Weight-three design literature: the missing coupling

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-3,3]`.
Date: 2026-09-06. Status: literature scope audit and exact reformulation;
the node remains OPEN. No new Lean theorem or general classification.

## What the Gram equation actually supplies

Let C have 3q points, H be a simple cubic symmetric adjacency matrix,
and B a binary matrix with q(q-3) columns, column sums 3 and row sums q-3.
Suppose D is a simple (q-1)-regular graph and

```text
H² + BBᵀ = (q-1)I + J - D.
```

The columns of `[H B]` are q² triples. Each point occurs in q triples;
each distinct point pair occurs once precisely when it is not a D-edge.
In particular all triples are distinct. Thus these columns give a regular
partial Steiner triple system with leave D. Triangle-free D makes it
maximal: every additional triple contains an already covered pair.

This interpretation does not supply the exterior adjacency T. Its
additional equations include `HB+BT=J` and
`BᵀB+T²=(q-1)I+J-D_F`, with T binary, symmetric and loopless and D_F
connected in this two-component branch. Even diagonal HD is already a
necessary consequence of reciprocal integral cross completion.

## Sources and precise scope cuts

[Colbourn and Rosa, *Leaves, excesses and neighbourhoods in triple
systems*, AJC 4 (1991), 143–178](https://ajc.maths.uq.edu.au/pdf/4/ocr-ajc-v4-p143.pdf),
§2.1, records degree parity, edge congruence, cut-density and fence
conditions for leaves. Section 2.3 treats maximal partial systems through
triangle-free leaves. These are conditions on the underlying design;
they do not assert the required reciprocal exterior completion.

There is an actual counterexample to exclusion at this scope, not merely
a missing theorem. The existing interval construction in
`NONBIP_MIXED_WEIGHT_THREE_TRIANGLE_FREE_GRAM_CUT.md` at q=16 gives
256 distinct triples on 48 points, replication 16, and 768 covered pairs.
Its leave is connected, nonbipartite, triangle-free and 15-regular.
The H columns are included among the triples. A fresh direct count checked
all these assertions, and the existing checker passed its full Gram and
32,640 ambient-pair checks. The obstruction to this example occurs at
even diagonal HD, not at partial-system existence.

The density literature has also moved since the survey.
[Delcourt and Postle, *A Proof of Nash-Williams' Conjecture*,
arXiv:2606.11178v1](https://arxiv.org/abs/2606.11178), submitted 9 June
2026, states the triangle-decomposition theorem for sufficiently large
triangle-divisible graphs of minimum degree at least 3n/4, and its
fractional counterpart. This is a preprint result; this audit checked
the authors' abstract, not the entire 120-page proof. Here the complement
of D has degree 2q on 3q vertices, below 3n/4. After reserving H's
neighborhood triples, the degree is only 2q-6. Neither meets the stated
threshold. Failure to meet a sufficient condition is not nonexistence.

## The existing signed-Gram obstruction is a residual cut obstruction

Define the simple residual graph

```text
L = 2I + J - D - H² = BBᵀ - (q-3)I.
```

Under the internal pair constraints, L is (2q-6)-regular with
3q(q-3) edges. Constructing B is exactly decomposing L into triangles.
For any vertex cut, a triangle contributes at most two crossing edges.
Consequently every cut of L must have size at most `2q(q-3)`.
This is the classical cut-density condition applied after the H triples
have been reserved.

For a sign vector s with entries ±1, this necessary condition is exactly

```text
sᵀDs + ||Hs||² <= 2q² + (sum s)².                 (*)
```

Indeed `sᵀLs=6q+(sum s)²-sᵀDs-||Hs||²` and
`cut_L(s)=(2|E(L)|-sᵀLs)/4`. Equivalently the signed sum on each B
column is odd, so its square is at least one; summing and using the Gram
identity gives (*). Thus merely replacing joint eigenvectors by arbitrary
sign vectors reuses the same obstruction class.

There is a useful graph formulation. Let m_H(s) count vertices whose
three H-neighbors all have the same sign. Then

```text
||Hs||² = 3q + 8m_H(s),
sᵀDs = 3q(q-1) - 4cut_D(s).
```

For a balanced cut, (*) becomes

```text
cut_D(s) >= q²/4 + 2m_H(s).                       (**)
```

The concrete Clebsch character has q=16, m_H=48 and cut_D=144;
(**) would require 160. Equivalently its residual cut has 432 edges,
exceeding the permitted 416 among 624 total edges. A fresh direct count
verified both descriptions against the existing construction.

## Divergence and decision

Potential routes considered at this checkpoint:

1. Exclude regular maximal partial-system parameters or triangle-free
   leaves. CUT: the interval example realizes them.
2. Use a general dense triangle-decomposition theorem. CUT as a direct
   application: both relevant degrees are below the source's threshold.
3. Force a violating cut of L using HD=DH and even diagonal HD.
   OPEN: (*) is necessary, but no theorem supplies such a cut for arbitrary
   admissible H,D. The fixed Clebsch translation family does not exhaust
   possible quotients.
4. Use more general edge weights or fences, beyond two-color cuts.
   OPEN: must obtain a uniform certificate from the coupled hypotheses;
   enumerating certificates for another fixed example is not that bridge.
5. Study the integral lattice of `BT=J-HB` with T symmetric and zero
   diagonal. OPEN: potentially retains the coupling lost by design-only
   results. A valid relaxation obstruction must be distinguished from
   constraints that merely restate even diagonal HD.
6. Use trades to extend a partial design to T. OPEN and speculative:
   preserving the Gram equations and symmetry is an additional requirement
   absent from ordinary design completion.
7. Couple component obstructions through the full ambient identity over
   F2. Sol3 is independently testing this route; no duplicate probe here.

Only routes 3 and 5 merit an immediate bounded algebraic check from this
audit: they retain H and can potentially distinguish known controls.
This is a shortlist, not a claimed theorem or a launched graph search.
No quotient census, order-64 enumeration, or further example-specific
formalization follows from this audit. The full triangle-free
weight-three branch, its triangle-containing sibling, and the connected
defect branch remain open.

## Bounded follow-up: full-rank modulo-two completion adds no parity test

This is an algebraic scope cut for route 5. Work over F2, and temporarily
write C for the rectangular right-hand side `J-HB`. If B has full row
rank, there exists an alternating matrix T satisfying `BT=C` if and only
if `CBᵀ` is alternating. Here alternating means symmetric with zero
diagonal; this is precisely the reduction modulo two of the corresponding
conditions on the desired integer T.

Necessity follows from `CBᵀ=BTBᵀ`. For sufficiency, choose a right inverse
R of B and put `M=CBᵀ`. Then the explicit formula

```text
T = RC + CᵀRᵀ + RMRᵀ
```

is alternating: the first two terms have zero diagonal and are transposes
of one another, and congruence preserves alternation of M. Since
`BCᵀ=Mᵀ=M` and `BR=I`, multiplication gives
`BT=C+MRᵀ+MRᵀ=C`.

In our integer setting the Gram equation and HJ=3J give

```text
CBᵀ = (q-6)J - (q-1)H + HD + H³.
```

At even q this matrix is symmetric when HD=DH. Its diagonal modulo two
is exactly diag(HD), since H is loopless and every diagonal entry of H³
counts twice the triangles through that vertex. Therefore, conditional on
full row rank of B modulo two, even diagonal HD is the ENTIRE obstruction
to solving the symmetric zero-diagonal cross equation modulo two.

A finite algebra check enumerated all 2,688 pairs of full-row-rank binary
2-by-3 matrices B and binary 2-by-3 right-hand sides C, and all eight
alternating 3-by-3 T, confirming the equivalence. The general proof is
the displayed right-inverse formula, not that finite check.

This does not assume or prove that every candidate B has full row rank
modulo two. Rank-deficient B, higher moduli, integer lifts, binary lifts,
and the exterior Gram still retain possible obstructions. In particular,
a solution over F2 is not an integral or graph completion. The direct
full-rank modulo-two refinement is stopped rather than formalized as
another parity wrapper.
