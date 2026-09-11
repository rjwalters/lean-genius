# Fixed graph classification for a six-fixed-point involution

Assume a simple C4-free graph G on N=78 or80 with minimum degree at least9 and a nonidentity involution fixing six vertices. Accepted2220 makes G9regular, its fixed graph H C4-free with odd degrees, and gives residual size R=N-60+S and capacity (9-r)(2+r)<=R for every occurring fixed degree r, where S is the sum of H-degrees.

We prove that atN78, H is one of three graphs: a matching of three edges; the star K1,5; a triangle with one pendant leaf attached to each triangle vertex. AtN80 there is one additional possibility: two adjacent degree3 vertices, each carrying two pendant leaves. These are necessary possibilities, not existence claims for G.

If H has a degree5 vertex v, it is universal. Any other vertex w cannot have two neighbors x,y other than v, since x-v-y-w-x would be a C4. Thus the induced graph on the other five vertices has maximum degree1. Its degrees are even, since all H-degrees are odd and v supplies one neighbor. Therefore it is empty and H=K1,5.

Otherwise every degree is1 or3. Let t be the number of degree3 vertices. Every degree3 vertex must neighbor a leaf: if all three neighbors had degree3, the six nonreturn two-step walks from it would end at only five other vertices, forcing C4. Distinct degree3 vertices need distinct leaves, since leaves have degree1. Thus t<=6-t, so t<=3.

If t=0, H is three disjoint edges. If t=1, S=8 and R=N-52<=28, whereas the degree3 capacity requires6*5=30<=R, impossible. If t=2, the two degree3 vertices must be adjacent: otherwise they require six distinct leaves, but only four exist. Once adjacent they use all four leaves, yielding the double-star. Here S=10 and R=N-50: capacity30 excludesN78, but notN80. If t=3, there are three leaves. Each degree3 vertex needs one and all leaves are used. Each degree3 vertex therefore has its other two neighbors among the other degree3 vertices, forming the triangle with one leaf at each vertex.

The exact auxiliary audit visits all32768 labelled simple graphs on six vertices once, checks odd degrees, pairwise codegree<=1, and the accepted residual capacity. Under the declared30-second cap it completes in about.083seconds. Labelled counts are15 for three disjoint edges,6 for the star,120 for the triangle with leaves, and90 for the double-star (onlyN80). These agree with6!/48,6!/120,6!/6,6!/8. The proof above does not depend on enumeration or those counts.

No residual graph search, full-graph feasibility claim, or further involution exclusion is made. This is a paper classification with a small finite arithmetic audit, not a Lean theorem.
