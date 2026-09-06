# Actual witnesses throughout the immediate post-square interval

2026-09-06, Sol1; uniform argument independently checked by Sol2, with the
exact-regular endpoint identified by Sol3. Prose construction, not Lean.

For every even prime power q, there is a simple C4-free graph of minimum
degree q at **each order q²+1 through q²+q+1**. At order q²+1 the construction
is exactly q-regular. Thus an interval argument against eventual monotonicity
cannot obtain a missing minimum-degree-q witness at any of these orders.
The order q² remains unresolved.

## Construction and proof

Use the dot-product polarity of PG(2,F_q), omitting loops. Its absolute
points form the line x+y+z=0; the nucleus is c=[1:1:1]. Each absolute point
has degree q, and every other point has degree q+1. The nucleus is adjacent
to all q+1 absolute points and no others. Every other nonabsolute point has
exactly one absolute neighbor: its polar line meets the absolute line once.
Distinct projective lines meet once, so the graph is C4-free.

Choose an absolute point a. Its q neighbors are independent: if u is
adjacent to a, then a lies on both polar lines a-perp and u-perp, so their
unique intersection cannot supply a distinct third vertex of a triangle.
In particular a has no distinct absolute neighbor.

Choose any U contained in N(a) minus {c}, and delete {a} union U. There are
q-1 eligible points, so the number deleted can be any integer from 1 to q.

* A retained absolute point loses no neighbor: each u in U has a as its
  unique absolute neighbor, and no two distinct absolute points are adjacent.
* A retained point in N(a) loses only a, because N(a) is independent.
* A retained point outside N(a) loses at most one neighbor in U: two would
  have that point and a as distinct common neighbors, creating a C4. It is
  not adjacent to a.

The remaining degrees are therefore at least q. Retained absolute points
ensure that the minimum is exactly q. With no deletion the full host gives
the additional order q²+q+1.

For the smallest order, take U=N(a) minus {c}. The remaining vertices are
the q² points outside a-perp, together with c. Every retained nonabsolute
point other than c has its polar line meet a-perp in exactly one deleted
point: that intersection cannot be c, since only absolute points are
adjacent to c. It therefore loses exactly one neighbor. The nucleus loses
only a, and the retained absolute points lose none. All degrees are q.

## Endpoint and scope

Deleting one more point by also removing c gives order q², but every
retained absolute point then has degree q-1. This construction therefore
does not supply a square-order witness. It also does not assume that
hypothetical witnesses at successive orders are nested.

`verify_binary_post_square_interval.py` constructs PG(2,F_q) directly for
q=4,8,16 using polynomial-basis field arithmetic. It checks every pair's
codegree in the host, the absolute/nucleus degree facts, one nested choice
for every permitted deletion size, exact regularity at q²+1, and failure
of the next deletion. The uniform proof above allows every eligible U;
the finite check does not enumerate all subsets U. No root or Lean status
is promoted, and no novelty claim is made for this polarity construction.
