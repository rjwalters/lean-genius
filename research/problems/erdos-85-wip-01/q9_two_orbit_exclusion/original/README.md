# Two equal cyclic orbits cannot realize N80, minimum degree nine

Let a graph have a free cyclic action of order m with two vertex orbits. Let a and b be the two internal degrees and x the cross degree. These are constant within each orbit; equal orbit sizes make x the same on both sides. Internal graphs are undirected circulants.

A C4-free circulant has degree at most two. Indeed a symmetric generating set of size at least three contains distinct nonzero elements u,v with v != -u; then 0,u,u+v,v are four distinct vertices of a cycle. This includes even m and an involution generator. Hence a,b <= 2.

For the first orbit, count unordered paths of length two with distinct endpoints in that orbit. Centers in the first orbit contribute m*binom(a,2); centers in the second contribute m*binom(x,2). Every endpoint pair has at most one common neighbour. Thus

    a(a-1) + x(x-1) <= m-1.

For m=40 and minimum degree nine, a+x >=9 and a<=2 imply x>=7. Already x(x-1)>=42>39, contradiction. No regularity assumption is needed. Therefore the requested N80/m40 cyclic class is empty by a direct argument. This does not exclude other cyclic classes or all N80 graphs. It is a paper argument, not a Lean theorem or SAT verdict.

The same elementary condition leaves the N48/m24/degree7 positive control possible: x>=5 and x(x-1)=20<=23. The argument is not being used to reject that control.
