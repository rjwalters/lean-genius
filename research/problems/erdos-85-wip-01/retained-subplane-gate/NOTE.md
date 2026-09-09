# Round115 S1: retained-subplane degree census and support gate

Let r>=5 be an odd prime power, q=r², and let S=PG(2,r) be the canonical
subplane of the orthogonal polarity plane PG(2,q). Let T subset S have
s=r-3 points. Retain all exterior points and the points of T, taking the
induced loopless polarity graph G_T. Then |V(G_T)|=q²-3, as required for
the odd-degree construction route. This note verifies its degree deficits
and rules out a trade confined to the induced union of the T-pencils.
It does not provide a repaired graph or exclude more broadly supported trades.

Write A_ext for the q-r exterior absolute points. For an exterior vertex x,
let o(x) be its unique subplane neighbor, whose existence was proved in the
reviewed Baer-deletion gate. Set

    U_ext={x exterior : o(x) in T},       U=T union U_ext.

Each owner class has q-r points, so |U_ext|=s(q-r). If a is the number of
exterior absolute points in U_ext and e_T the number of loopless edges
induced on T, the exact degrees are:

* Exterior x: deg_G_T(x)=q-1_{x absolute}+1_{o(x) in T}.
* Retained p in T: deg_G_T(p)=q-r+deg_T(p).

The second formula includes absolute p: it has q-r exterior neighbors,
plus exactly its loopless T-neighbors. In particular every retained point
has deficit r-deg_T(p)>=4 relative to q, since |T|=r-3.

Thus the exterior degree census is

    degree q-1: q-r-a;
    degree q+1: s(q-r)-a;
    degree q:   (q²-r)-(q-r-a)-(s(q-r)-a).

Summing q-deg over all vertices gives

    Delta=(1-s)(q-r)+sr-2e_T
         =(6-r)q-7r-2e_T.                         (1)

For example, at r=5 the initial graph has more edges than a q-regular graph
by 5+e_T, despite having deficient vertices. Edge deletion alone cannot fix
those deficiencies; an eventual construction must both delete and add.

Any C4-free graph on q²-3 vertices with minimum degree q must be q-regular:
for every vertex v, its non-returning two-walk endpoints are distinct, so
deg(v)(q-1)<=q²-4<(q+1)(q-1). Thus deg(v)<=q. Consequently, if a repair
removes f old edges and adds b edges, (1) forces

    f-b = -Delta/2 = ((r-6)q+7r+2e_T)/2.          (2)

This is an exact necessary net edge balance, not a construction or a bound
on both f and b separately. For r>=7 its leading size is r³/2.

## The induced-pencil support cannot repair the deficits

Each subplane point has at most two exterior absolute neighbors, since its
polar line meets the nonsingular absolute conic in at most two points.
Therefore a<=2s. The number of deficient exterior vertices outside U is
at least

    q-r-2s = r²-3r+6 > 0.                         (3)

Changing only edges with both endpoints in U leaves all those degrees
unchanged at q-1. It cannot reach minimum degree q. This rules out the
specific proposed replacement of matching bundles between halves of the
affected T-pencils, if all its changed endpoints are confined to U.

Allowing edges with only one endpoint in U is a different and broader
support condition: it may change those deficient degrees, and (3) does
not rule it out. Nor does this note rule out first enlarging U to include
all exterior absolute points. No such broader field-defined edge formula
has been supplied here, so no unrestricted search is launched.

## Deterministic checks, not graph search

`check.py` uses the already verified PG(2,25) coordinates and two prescribed
retained pairs: {(1,0,0),(1,0,1)} and {(1,0,0),(0,1,0)}. Both have622
vertices. It checks every vertex degree against the formulas, the total
balance, and the external deficient vertices untouched by induced-U edits.
The first pair has e_T=0,a=2,18 deficient exterior vertices outside U and
net required deletions5. The second has e_T=1,a=0,20 such vertices and net
required deletions6. The uniform conclusions are the proofs above.
