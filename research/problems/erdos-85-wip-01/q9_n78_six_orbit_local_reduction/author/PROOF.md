# Six-orbit candidates have order24 and Klein-four center stabilizers

Assume the complete six-orbit quotient reduction submitted2346. The conclusions here are conditional on that packet's independent acceptance until it passes. Its two surviving size patterns are(6,6,6,12,24,24) and(6,12,12,12,12,24), with24 and96 labelled quotients at each group order24/48. We reduce these using only local paper arguments and a deterministic check of the saved matrices.

## A local two-pair obstruction

Let H be a vertex stabilizer preserving two disjoint two-element subsets of its neighborhood. The combined permutation map H->S2 times S2 has kernel K of index at most4. If |H|=8, K has order at least2 and is a2-group. It contains an involution fixing all four neighbors. This contradicts accepted2257, which says an involution fixing a vertex has only one or three fixed neighbors. Thus an order8 stabilizer cannot preserve such two pairs.

If |H|=4 instead, the same argument forces K trivial. H embeds into S2 times S2 and consequently is the Klein-four group. This does not require transitivity on either two-element set.

For an automorphism orbit decomposition, every set N(v) intersect O_j is H=A_v invariant, including the internal-neighbor set when O_j contains v. Hence two quotient entries equal2 in a row certify the two invariant pairs.

## Pattern(6,6,6,12,24,24)

In all24 saved quotients, two of the three six-orbit rows have at least two entries equal2. At |A|=48 these vertices have stabilizer order8, so the local obstruction excludes every quotient.

At |A|=24 their stabilizers are Klein-four. The third six-orbit row has reciprocal entries1 with one of the preceding two six-orbits. Indeed this is checked for every saved matrix. The edges between two equal-size orbits with reciprocal degree1 define an equivariant bijection. Matched endpoints therefore have exactly the same point stabilizer. Consequently all three six-orbits have Klein-four vertex stabilizers at order24. This does not exclude those24 quotient matrices.

## Pattern(6,12,12,12,12,24)

Write F for the six-orbit. All96 saved quotients have q_FF=1, so F induces3K2. Exactly48 have a12-orbit B with q_BF=2 and q_BB=1. The other48 have two distinct12-orbits each meeting every center in exactly two neighbors, giving two entries equal2 in the F row.

Consider the48 double-attachment quotients first. Mapping b in B to its two F neighbors is injective by C4-freeness and equivariant. The kernel of the F action is a subgroup of A_f of order4 or8 and fixes all18 vertices of F union B. A nontrivial kernel contains an involution, contradicting2257's fixed-count upper bound six. Hence the action on F is faithful.

At |A|=48, A is the entire order48 matching-preserving group on F. B is its twelve nonmatching-pair orbit. A single matching-edge flip fixes four F vertices and four B vertices, contradicting2257, exactly as in accepted2339. This argument needs no hypothesis on the other orbits or attachments.

At |A|=24, the same index2 matching-group argument of accepted2340 applies verbatim. B is an orbit of size12, so it consists of all nonmatching pairs. The cyclic edge-image subgroup contains a single-edge flip and is excluded. The two remaining actions are the even-flip and determinant-positive signed S4 groups. In either action, the explicit axis interchange in accepted2342 fixes precisely b={(0,+),(1,+)} and b'={(0,-),(1,-)} among B. Since q_BB=1, it forces bb' to be an edge, giving the C4 (0,+),b,b',(0,-). No condition on the remaining four12/24 orbits enters this proof. Thus these48 quotients are excluded at both group orders.

The other48 quotients have two invariant two-element neighbor sets at each F vertex. The local obstruction excludes them at |A|=48. At |A|=24 it forces the F stabilizer to be Klein-four.

## Result and exact scope

Once2346 is accepted, every six-orbit candidate has |A|=24. Its possible sizes are(6,6,6,12,24,24) with24 necessary quotients, or(6,12,12,12,12,24) with48 remaining necessary quotients. Every vertex in a six-orbit has Klein-four stabilizer. The deterministic cover.json identifies every matrix and its applicable obstruction or retained status.

Neither remaining family is excluded or asserted realizable. This theorem does not assume that five orbits have been excluded, and makes no claim about seven-plus orbits, allN78, N80 or Erdős85. No new graph search or Lean formalization is used.
