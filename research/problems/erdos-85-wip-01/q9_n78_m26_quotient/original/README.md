# Necessary quotient for N78, minimum degree nine, free cyclic order26

This is a proposed necessary condition only, awaiting independent review. No restriction has been added to the frozen generic CNF.

A C4-free graph on78 vertices with minimum degree9 must be9-regular. For a vertex of degree D, its neighbourhood induces a matching; each neighbour has at least7 neighbours outside the closed neighbourhood, and these outside sets are disjoint. Hence78>=1+8D, so D<=9.

For three26-vertex cyclic orbits, internal degrees a,b,c lie in{0,1,2}, since an internal circulant of degree>=3 has a C4. Let x,y,z denote the cross degrees for pairs12,13,23. Equal sizes imply symmetric degrees. Regularity gives
x=(9-a-b+c)/2, y=(9-a-c+b)/2, z=(9-b-c+a)/2.

Counting same-orbit endpoint pairs gives a(a-1)+x(x-1)+y(y-1)<=25, with its cyclic analogues. Checking the ten sorted triples 0<=a<=b<=c<=2, requiring integer x,y,z, leaves exactly:

- (a,b,c)=(1,1,1), (x,y,z)=(4,4,4).
- (a,b,c)=(1,2,2), (x,y,z)=(4,4,3).

The first pattern is impossible. An internal degree-one circulant on Z26 must use the antipodal shift13. If both orbits have this internal shift and even a single cross offset t, vertices A0,A13,B(13+t),Bt form a C4, since translating a cross edge by13 preserves it. Its cross degree4 is positive, a contradiction.

Therefore, up to permuting the three orbits, the only possible quotient is internal degrees(1,2,2) and cross degrees(4,4,3). This does not establish existence or nonexistence of that class. It may support a later diagnostic or reviewed redundant constraint; the original CNF remains unchanged.
