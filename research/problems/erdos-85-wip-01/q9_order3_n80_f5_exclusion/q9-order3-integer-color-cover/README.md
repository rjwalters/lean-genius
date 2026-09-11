# Integer color selections for576 fractional survivors

Input is exactly the576 EXACT_FRACTIONAL_FEASIBLE representatives from2201. Coverage remains conditional on the preceding symmetry/LP reviews. For each representative, enumerate all243 words and retain those with positive pair capacities and nonnegative b(w) capacities from accepted2194. Search for ten distinct words with coordinate margins433, pair agreement<=3, and all pair-contingency bounds.

Sorted-subset DFS traverses each possible selection once. It prunes exceeded margins/contingency capacities, insufficient remaining coordinate support, insufficient candidate count, and forbidden agreement pairs. Original100000node cap percase plus60second aggregate wall cap, no retry. All576 cases terminate without caps:518 INTEGER_COLORING witnesses and58 COMPLETE_NEGATIVE,1,949,407totalnodes,.415seconds. Only the first coloring per positive case is saved; these are not complete coloring payloads.

verify.py independently reconstructs every input candidate list and capacity from explicit paths, checks exact equality of the576-case input set, and checks all518 witnesses directly. Negative search completeness awaits peer audit. No residual Q or matching phases were tested. A failure to extend a saved coloring would not exclude its representative, since other colorings may exist.

All claims concern the N80/F5 order-three necessary relaxation. None establishes graph existence or excludes the full graph class.
