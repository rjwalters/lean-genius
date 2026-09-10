# Complete colour0 slots in the five open shared-f2 configurations

This proposed structural refinement applies to the five shared-f2 configurations capped in the previous ordinary-host pilot. Those capped results remain UNKNOWN. No capped search is rerun here.

All six colour0 singleton vertices are a0,b0,f0 and three heavy-free vertices. The first two have triple neighbours containing0, so have no colour0 singleton neighbour. The other four each require exactly one colour0 singleton neighbour. Thus the induced colour0 singleton graph is a perfect matching on f0 and the three heavy-free vertices.

Call f0's mate gA. The unique singleton neighbour of the shared vertex f2 has colour0 and is heavy-free: it cannot be a0 by reciprocal colours, b0 because B and f2 already share C, or f0 because f0 already covers colour2 through F. Call it gB. We have gA!=gB, because otherwise F and that vertex would share both f0 and f2. Calling the third heavy-free vertex gC, the matching forces gB-gC.

In the four no-internal-edge configurations under consideration, the five colour0 targets of the fi are respectively gA,b0,gB,gC,a0: injectivity leaves gC as f3's only remaining target. In the fifth configuration, internal edge f0-f1 replaces f1's target b0 by f0, and b0 is the omitted colour0 target; again f3 must target gC. Hence f3-gC is forced in all five configurations.

Each g vertex has no heavy neighbour, so its degree and required colours force exactly one empty neighbour and one singleton neighbour in each colour0,...,4. Existing a0,b0,f0 have respectively3,3,2 empty neighbours. These eight empties are distinct, because their hosts already share high0. The heavy A contributes the additional empty eA, also disjoint from those sets. The three remaining empties therefore correspond bijectively to gA,gB,gC.

After adding gA,gB,gC and the forced edges, every remaining singleton has nonzero colour and must have exactly one neighbour among the six colour0 singletons. For each colour-c request still missing at a colour0 singleton v, there is exactly one colour-c singleton neighbour of v. Distinct requests give distinct vertices: within a fixed colour, a repeated vertex would give high0 and that vertex two common neighbours. The remaining request counts are4,3,4,3 for colours1,2,3,4, exactly the remaining singleton multiplicities. Thus all fourteen remaining vertices can be named canonically by (colour, colour0 neighbour), without a permutation search.

`build.py` constructs the five resulting49-vertex partial skeletons and checks C4-freeness and the14slot count. Every nonempty vertex other than high0 already has exactly one neighbour in N(high0). Among the twelve empties, seven already have one; the remaining five must be assigned as two neighbours of f0 and one each of gA,gB,gC. This offers a complete-colour0-first decomposition before the other F-star empty incidences or remaining heavy/singleton edges.

This document claims a necessary relabelling reduction only. The partial graphs are not solutions, the remaining edges are not searched here, and no subcase or whole-core exclusion is asserted. Independent review is pending.
