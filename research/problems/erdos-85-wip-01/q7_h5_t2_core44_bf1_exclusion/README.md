# No-sharing core44 forces b0-f2

Assume the reviewed T2/core44 support pattern A=012,B=034,C=13,D=14,E=23,F=24 and heavy edges A-D,A-E,B-C. Assume no singleton is shared by C and F. BC=J supplies exactly one common neighbour of each low vertex with each high vertex.

B has singleton neighbours b0,b2,b4. C has singleton neighbours c1,c2. F has f0,...,f4. The reviewed heavy-support compatibility shows that only C and F could share a singleton, so under the no-sharing assumption these are distinct and carry no additional heavy guests. There are five colour2 singletons: b2,f2,c2 and two heavy-free vertices p,q. No A,D,E singleton has colour2, because their heavy neighbours already cover high colour2.

Each of b0,b2,b4 needs exactly one singleton neighbour of colour2: their sole heavy neighbour B has support034 and empty neighbours cannot supply a high colour. Their three colour2 neighbours are distinct, because b0,b2,b4 already share B, so sharing any second neighbour would create a four-cycle.

None of the three can use c2: the four distinct vertices B,C,c2,b_i would form a cycle. None can use b2: b2 cannot be its own neighbour, while b2 already has B as its colour0 and colour4 common neighbour, precluding edges to b0 or b4. Finally b2 and b4 cannot use f2, because f2 already has F as its colour2 and colour4 common neighbour.

Thus b2 and b4 must use the two distinct vertices p,q. The only remaining available colour2 target for b0 is f2. Therefore b0-f2 is forced. In particular b0-f1 is impossible, since b0-f1-F-f2-b0 would be a four-cycle.

This proof is independent of the af choice, the within-colour matching normal form, and all empty-incidence configurations. It excludes the entire no-sharing bf1 branch. It does not exclude bf2, sharing at f1/f2, core44, or H5. Previously capped computational records retain their original status; this is a new paper exclusion rather than a retried computation.

check.py independently constructs a minimal20vertex graph from explicit supports, derives allowed targets by direct common-neighbour tests, and checks all60 possible injections of three distinct targets from five. Exactly two survive, both using b0-f2. Adding b0-f1 then creates the stated four-cycle. This is a finite sanity check, not a Lean proof. Independent squad review is pending.
