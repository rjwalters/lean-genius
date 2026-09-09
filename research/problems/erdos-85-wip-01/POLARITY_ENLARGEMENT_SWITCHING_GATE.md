# A size constraint on switch-and-enlarge polarity constructions

This is a preliminary gate for my round-114 entry, not an exclusion of all
constructions and not an Erdős 85 proof.

Let q>=4 be even. Start with a simple polarity graph P having
n0=q^2+q+1 vertices, q+1 vertices of degree q, and all other vertices of
degree q+1. Add h=q-3 new vertices, and permit arbitrary changes of edges
between old vertices. The proposed target is a C4-free graph G of minimum
degree d=q+1 on N=(q+1)^2-3 vertices. This would feed the odd-degree drop
criterion if constructed on a cofinal set.

Write r for the number of removed old edges and a for the number of added
old edges. Then necessarily

    r-a >= (q+1)(q-4)/2 - h(1+sqrt(4h-3))/4.       (1)

In particular, for every q>=16, at least q^2/4 old edges must be removed.
Thus the proposed construction cannot use only O(q) edge changes. This
does not forbid an explicit uniform construction with quadratic changes.

## Proof

First G must be d-regular. For any vertex v, the number of nonreturning
two-step walks starting at v is at least deg(v)(d-1). C4-freeness gives at
most one such walk to each other vertex, hence

    deg(v)(d-1) <= N-1 = d^2-4.

Since d>=5, this forces deg(v)<=d; the minimum-degree hypothesis gives
equality.

Let C count edges between old and new vertices, and e count edges within
the h new vertices. The original degree sum on old vertices is
d*n0-(q+1)=d*n0-d. Counting degrees in G on each shore gives

    C = d + 2(r-a),       d*h = C + 2e,

and consequently r-a=d(h-1)/2-e.

The new induced graph is itself C4-free. Its degrees x_i satisfy
sum_i binom(x_i,2)<=binom(h,2). Cauchy-Schwarz and sum x_i=2e imply

    4e^2/h - 2e <= h(h-1),
    e <= h(1+sqrt(4h-3))/4.

Substitution proves (1). Using h<=q gives the weaker bound

    r-a >= q^2/2 - q^(3/2)/2 - 7q/4 - 2.

For q>=16 the right side divided by q^2 is at least
1/2-1/8-7/64-1/128 = 33/128 > 1/4.
Since a>=0, the stated lower bound on removed edges follows.

The reasoning uses only the starting degree sequence, not unproved
properties of polarity graphs. It does not assume a particular switching
algorithm or bound the number of new-old edges by an induced-deletion
argument. Missing construction input: a quadratic-size organized change
that simultaneously fixes degrees and avoids every new C4.
