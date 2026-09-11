# Excluding the S4 pattern (3,3,4,8,12,24,24)

Assume G is simple, C4-free and nine-regular on78 vertices, A=Aut(G) is S4, and the vertex orbit sizes are (3,3,4,8,12,24,24). We give a paper exclusion independent of the character enumeration that suggested this case.

Let T be the normal Klein-four subgroup of double transpositions. Every Sylow2 subgroup of S4 contains T: their product with the normal2-subgroup T is a2-subgroup, so maximality forces containment. Each vertex in either three-orbit has stabilizer of order8, a Sylow2 subgroup, and hence is fixed by T. Write F for the union of the two three-orbits. Every nonidentity t in T fixes these six vertices; accepted2257 bounds its total fixed count by six. Thus T acts freely outside F.

The graph induced on the six fixed vertices of t is, by2257, a matching3K2 or a triangle with three pendant leaves. At a vertex f in F the outside neighbors are a union of free T orbits, so9-d_F(f) is divisible by4. The only available fixed degrees are1 and3, forcing degree1. Hence F is a matching.

Every vertex outside F has at mostone F neighbor. Otherwise it and its distinct image under any nonidentity element of T share two F neighbors, giving a C4. If an outside A orbit attaches to F, equivariance and transitivity make its unique-neighbor map surject onto precisely one of the two three-orbits; its size must therefore be divisible by3. The four- and eight-orbits cannot attach. A twelve-orbit contributes four neighbors to each center in its target three-orbit, and a24-orbit contributes eight. Each center requires eight outside neighbors. Since there is only one twelve-orbit, the equation8=4a+8b with a in{0,1} forces a=0 and b=1 at each three-orbit. The two24-orbits, called U and V, attach respectively to the two distinct three-orbits. The remaining R has size24 and is the union of the4-,8-,12-orbits, with no F neighbors.

For w in W=U union V, let f be its unique F neighbor. Among W it has at mostone neighbor attached to f, since two such neighbors give a C4 with f. It has no neighbor attached to the matching partner f', because w-f-f'-w'-w would be a C4. It has at mostone neighbor attached to each of the other four centers. Thus w has at mostfive W neighbors, and therefore at leastthree R neighbors.

Conversely a vertex r in R has at mostone W neighbor attached to each center, again by C4-freeness, so it has at mostsix W neighbors. Counting edges gives

 48*3 <= e(W,R) <=24*6.

Equality forces every r to have exactlyone W neighbor attached to each of the six centers, hence exactlythree neighbors in U and three in V.

Take r in the four-orbit. Its stabilizer H in A has order6 and preserves its set of three U neighbors. But A acts regularly on U, since |U|=|A|=24. The restriction of this action to H is free, so every H orbit in U has size6. An H-invariant subset cannot have size3. This contradiction excludes the stated orbit-size pattern.

Only2257's fixed-point bound and six-fixed graph classification are used beyond elementary group action and C4 counting. No finite character or quotient result, capped search, or Lean formalization is required. This does not exclude other S4 actions or the full N78 problem.
