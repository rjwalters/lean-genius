# Residual cycles in the N78/F10 involution case

Assume accepted2225: the residual graph G[R] is C4-free on eight vertices, has a fixed-point-free involution, and has exactly A_count-4 edges, where4<=A_count<=10. In particular it has at most six edges. The four residual2-orbits have quotient row degrees m_j-1, with m_j the number of typeA attached groups missing orbit j.

## A triangle forces exactly two triangles and two isolates

A triangle T cannot be invariant under a fixed-point-free involution, since an invariant vertex set has even size. Thus tau(T) is a different triangle. If they share one vertex, their invariant union has five vertices, again impossible. If they share two vertices, their common edge and two distinct remaining vertices form a four-cycle, forbidden. They cannot share all three vertices. Hence T and tau(T) are disjoint. Their six edges exhaust the residual edge budget, so R is exactly two disjoint triangles and two isolated vertices.

## No five-cycle is possible

A five-cycle C also has a distinct involution image. Two distinct five-cycles have at most three common edges: four common edges of a five-cycle form a path of length four on all five vertices, and the fifth edge closing that path is uniquely determined in a simple graph. Thus their union has at least seven edges, exceeding the budget. This rules out every five-cycle.

## Complete cyclic alternatives

If R contains a cycle, its length is at most six because there are at most six edges. Length four is forbidden, length five was just excluded, and length three gives the two-triangle alternative. The only remaining possibility is a six-cycle, whose six edges exhaust the budget. Then R is exactly a six-cycle and two isolated vertices.

Therefore R is either a forest, or one of these two cyclic graphs:

* two disjoint triangles plus two isolated vertices;
* one six-cycle plus two isolated vertices.

In either cyclic case e(R)=6, so A_count=10. Every attached group is typeA. The six cycle vertices have residual degree2 and the two isolates have degree0. The involution preserves these degree classes, giving three residual2-orbits of degree2 and one of degree0. Hence the missing-count multiset is(3,3,3,1).

In particular, if any attached group is typeB or typeC, then A_count<=9 and R must be a forest. The converse is not asserted: a forest with six edges is still possible at A_count=10 under these constraints. No cyclic alternative or forest is asserted to extend to a full graph.

This is a paper corollary of2225, with no graph enumeration, solver run, phase choice, or whole involution-case exclusion.
