# Core44 no-sharing singleton colour matchings

Assume the reviewed T2/core44 supports A=012,B=034,C=13,D=14,E=23,F=24, heavy edges A-D,A-E,B-C, and no singleton shared by C and F. These are the only heavy vertices that could share a singleton. Thus every heavy guest assignment is separate. The forced heavy-singleton neighbours are A:a0; B:b0,b2,b4; C:c1,c2; D:d3,d4; E:e3,e4; and F:f0,...,f4. Subscripts denote singleton colour. All other singleton vertices are heavy-free.

For any singleton x of colour c, its common neighbour with high vertex h_c is either a heavy neighbour whose support contains c, or a singleton of colour c. BC=J requires exactly one. Therefore those already covered by a heavy neighbour have no within-colour edge, and all other members of S_c induce a perfect matching. This argument also forbids edges between matching-eligible and exempt vertices, by reciprocity.

The colour classes and exempt vertices are:

| Colour | Class | Exempt vertices |
| --- | --- | --- |
| 0 | a0,b0,f0 and three heavy-free | a0,b0 |
| 1 | f1,c1 and three heavy-free | c1 |
| 2 | b2,f2,c2 and two heavy-free | f2 |
| 3 | f3,d3,e3 and two heavy-free | e3 |
| 4 | b4,f4,d4,e4 and one heavy-free | b4,f4,d4 |

The b2-c2 matching edge is impossible: B-C-c2-b2-B would be a four-cycle. Hence the two heavy-free colour2 vertices must respectively match b2 and c2. The sole heavy-free colour4 vertex must match e4.

Canonical naming makes colour0 edges f0-g0a,g0b-g0c; colour1 edges f1-g1a,g1b-g1c; colour2 edges b2-g2a,c2-g2b; colour4 edge e4-g4. In colour3 there are exactly two possibilities up to exchanging its heavy-free vertices: f3-d3 plus g3a-g3b, or f3-g3a plus d3-g3b. These renamings act independently inside each heavy-free colour class and are applied to the entire prospective graph, including all later empty and cross-colour edges. Consequently this is a cover of full graphs, not a restriction to a previously selected incidence witness.

The checker constructs the full37vertex high/heavy/singleton skeleton and independently enumerates every eligible perfect matching, using direct all-pair common-neighbour tests. The allowed labelled counts are3,3,2,3,1, giving54 combinations. All54 remain locally C4-free for each of the four existing af/bf choices, with f1-f3 imposed. Thus this lemma excludes no af/bf branch. It yields two canonical within-colour configurations per af/bf pair (eight37vertex configurations total), useful for a subsequent decomposition. Empty vertices, remaining cross-colour edges and full degree completion are still absent.

This is a necessary structural lemma with a finite sanity check, not a Lean proof or a core exclusion. It does not retry any capped search. Independent squad review is pending.
