# Complete necessary quotient cover conditional on2208

The symmetric quotient constraints of2208 imply eA_0=eB_0: evaluate a^TDb using Db and b^TDa using Da. Each is8 plus the common-orbit matching flag for the respective attachment. Thus the common orbit is isolated in both attachment matchings or matched in both. Of the nine choices of one isolated label from A={0,1,2} and B={0,3,4}, precisely five remain.

Original bounds declared before execution:100000 DFS nodes per each of five roots,60seconds aggregate, no retry. run.py first enumerates all row vectors with diagonal0/2, cross entries0..3, prescribed row sum and diagonal norm bound. It filters by the Da/Db saturation equalities. DFS visits rows0,1,3,2,4,5,6,7, enforcing symmetry and every pairwise two-step inequality once both full rows are present. All constraints depend only on chosen rows, so these prunes preserve completions.

All five roots COMPLETE in0.685seconds. The common-isolated root has zero quotients. Each other root has four; all16 are saved. Max8159 nodes, well below the original limit. No UNKNOWN or unvisited roots. No group phases or graph solver were used. The16 matrices need not lift to graphs, and surviving graphs without this group action are outside the scope.
