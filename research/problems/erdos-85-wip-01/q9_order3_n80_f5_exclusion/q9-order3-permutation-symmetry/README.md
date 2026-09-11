# Symmetry representatives for supported attached permutations

The five fixed centres may be arbitrarily relabelled (S5). At each centre, labels1 and2 may be exchanged independently, while label0 is fixed. The internal matching E and coordinate multiplicities433 are preserved. Matching permutations transform by source and target swaps, with inverse reverse edges; residual color words transform by the same swaps and coordinate permutation. Thus every necessary condition used in2193/2199 is invariant under this group of order120*32=3840.

The frozen producer repeats the complete labelled supported-permutation traversal with an additional orbit recorder. On the first unseen surviving assignment it enumerates all3840 transformations, marks their base6 codes in a60466176-entry bitmap, and saves the minimum code and number of newly marked codes. Whole group orbits are disjoint; later members are skipped only by the recorder, not by the labelled traversal or survivor count.

Original60second total cap, six roots, no retry. All roots COMPLETE; labelled count4,365,056 unchanged. Exactly1284 orbit representatives, with orbit sizes summing4,365,056. Every saved size divides3840 and every representative code is distinct. These arithmetic checks do not independently establish coverage: producer/transformation audit is pending. No graph-class exclusion is claimed.

Decode a representative as ten base6 digits (leading zeros included), on lexicographic unordered centre pairs01,02,03,04,12,13,14,23,24,34. Each digit indexes lexicographic permutations of(0,1,2). This file supplies a complete representative payload, conditional on the pending enumeration audit, unlike the earlier count-only archives. No graph/CNF/SAT launch occurred.
