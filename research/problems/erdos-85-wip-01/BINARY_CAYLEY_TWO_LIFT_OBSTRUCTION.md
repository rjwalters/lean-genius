# No square-order witness from a double cover of a binary Cayley graph

2026-09-08, Sol3. Independently reviewed by Claude (review #1472 PASS),
with Sol1 also checking the core argument. Uniform prose proof; not
Lean-checked. Extends Sol2's
odd-exponent obstruction in squad message #40749 to every exponent within
the same construction class. A-REG remains open.

## Statement

Let H be the simple Cayley graph of V = F_2^r with connection set
S contained in V minus {0}, and let d = |S|. If a two-sheeted graph cover
G of H is C4-free, then

    |V(G)| = 2^(r+1) >= d^2 + d + 2.

Consequently no q-regular C4-free graph on q^2 vertices can be a two-sheeted
cover of a simple elementary-abelian Cayley graph. In particular, taking
q=2^k and r=2k-1 rules out this construction for every k>=1, with no parity
restriction on k. Edge signs in the cover may be arbitrary; they need not
respect any Cayley symmetry. Neither the base nor the cover is required
to be connected, and the cover need not itself be a Cayley graph.

## Proof

Write the cover using bits epsilon(uv) on the undirected edges of H: its
edges join (u,i) to (v,i+epsilon(uv)), with bits added modulo two.
A base 4-cycle lifts to two 4-cycles when its four edge bits sum to zero,
and to one 8-cycle otherwise. Thus every base 4-cycle must have bit sum one.

First, H has codegree at most two. If u,v have three distinct common
neighbors, lift the three two-edge paths starting at (u,0). Two of these
paths end at the same lift of v. Their distinct intermediate base vertices
give a 4-cycle in G.

For z nonzero, the common neighbors of 0 and z in H are the elements s of S
with s+z in S. They occur in pairs {s,s+z}. Hence the codegree bound says
that all unordered sums s+t, s!=t in S, are distinct: S is a binary Sidon
set.

Second, H cannot contain K4. The three 4-cycles of K4 use each of its six
edges exactly twice in total. Their three bit sums therefore sum to zero,
whereas requiring all three to be one gives sum one, a contradiction.

If distinct s,t in S had s+t in S, the four distinct vertices
0,s,t,s+t would form K4 in H. Therefore S is also sum-free: no unordered
sum of two distinct elements of S belongs to S.

The following subsets of V are pairwise disjoint:

* {0};
* S, of size d;
* the unordered sums of two distinct elements of S, of size d(d-1)/2.

Their sizes give 2^r >= 1+d+d(d-1)/2. Doubling proves the assertion.
At d=q and |V(G)|=q^2, the inequality would require q^2>=q^2+q+2.

There is also a shorter, weaker obstruction at square order. Every triangle
in an elementary-abelian Cayley graph sits in one of the K4s just described.
Thus H and its cover G are triangle-free. A triangle-free, C4-free
d-regular graph has at least 1+d+d(d-1)=d^2+1 vertices by counting the
disjoint first and second neighborhoods of a vertex. This too excludes
order d^2, but does not give the stronger bound above.

## Verification and limits

`verify_binary_cayley_two_lift.py` independently builds all 64 double covers
of K4 and all 64 of K2,3, and finds a 4-cycle in each using common-neighbor
counts. It checks all 35 four-element connection sets in F_2^3 minus {0}:
each either repeats an unordered pair sum or contains a zero-sum triple.
It also checks every connection set in dimensions 1 through 4 satisfying
both set conditions against the counting inequality. A positive control
builds the odd double cover of C4, namely C8: it is C4-free and attains
the d=2 bound. These are finite checks of ingredients, not an exhaustive
search over square-order graphs or a machine-checked uniform proof.

The statement assumes a simple base and a genuine graph cover, with a
matching above each base edge. It does not cover quotients with loops or
parallel edges, covers of arbitrary bases, larger covering fibers, or
graphs with no such symmetry. In particular no theorem presently forces
an arbitrary A-REG counterexample to have this form. The extension to all
graphs stops at that missing hypothesis; no A-REG node is closed.

For terminology and the coding-theoretic context of sum-free binary Sidon
sets, see Czerwinski and Pott, [Sidon sets, sum-free sets and linear
codes](https://arxiv.org/abs/2304.07906). The argument above is self-contained
and uses no bound from that paper; no novelty claim is made.
