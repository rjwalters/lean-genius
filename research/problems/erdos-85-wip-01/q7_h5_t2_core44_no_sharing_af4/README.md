# Core44 no-sharing: a0-f4 and b0-f2 are incompatible

Assume the reviewed core44 no-C/F-sharing structure (reviews2047 and2054), and the branch edges a0-f4 and b0-f2. This argument is independent of the distinguished-empty omitted pattern and of all remaining edges.

The colour0 singleton class consists of a0,b0,f0 and three heavy-free vertices x,y,z. The vertices a0,b0 already have their own-colour common neighbour through A and B. The other four have no heavy neighbour containing0, hence each requires exactly one singleton neighbour of colour0. Reciprocity makes their induced graph a perfect matching. Name f0's mate gA and name the other two heavy-free vertices gB,gC. Then gB-gC is an edge.

Every fi has exactly one colour0 singleton neighbour: its only heavy neighbour F has support24, so does not cover0. These five neighbours are distinct, because otherwise two fi would share both F and their colour0 neighbour. None can be f0: f0 cannot be its own neighbour, and an edge f_i-f0 for i!=0 would duplicate colour i at f0 when i=2 or4, or violate the reviewed forced internal matching when i=1 or3. Equivalently the already reviewed internal F-star graph is exactly f1-f3, with no edge incident to f0. Thus the five targets exhaust a0,b0,gA,gB,gC.

The targets of f0,f2,f4 are respectively gA,b0,a0. Consequently the targets of f1,f3 are gB,gC in some order. Together with the forced edge f1-f3 and matching edge gB-gC, these give the four-cycle f1-gB-gC-f3-f1 (or its relabelling). This contradicts C4-freeness.

Therefore no full graph in the no-sharing af4/bf2 branch exists. In particular this covers all four omitted patterns, including their formerly capped searches. The historical capped receipts remain UNKNOWN; this is a new universal exclusion, not a retry or reinterpretation of their termination status. It does not by itself exclude bf1, af3/bf2, all no-sharing, or core44.

The checker independently enumerates all three labelled S0 matchings and both remaining target permutations. All six explicit partial graphs contain the displayed cycle. This finite sanity check supports the paper argument; it is not a Lean proof. Independent peer review is requested.
