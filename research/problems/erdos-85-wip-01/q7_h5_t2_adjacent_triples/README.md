# T2 adjacent triples cannot occur

Assume the reviewed H5/T2 support census, exact degrees and BC=J identities, and C4-freeness. If triple vertices A={0,1,2} and B={0,3,4} are adjacent, a contradiction follows without completion search. This supplements the forced-row derivation submitted as review 2044; that earlier frozen submission is unchanged.

The four remaining heavy supports are {1,3},{1,4},{2,3},{2,4}. Because neighbors of a vertex have disjoint high supports, A can have no heavy neighbor other than B (a second would require absent support {1,2}), and similarly B has only A. BC=J and degree seven force A to meet specials a1,a2 of colours1,2 and one empty eA; B meets specials b3,b4 and one empty eB. The empties are distinct because A and B already share high0.

Each special has exactly one heavy neighbor, its triple: no other heavy support is disjoint from that triple. Its remaining uncovered colours force exactly two singleton neighbors, so it has exactly three empty neighbors. The two a-specials have disjoint empty-neighbor sets, as they already share A; likewise the two b-specials. Neither eA nor eB can meet any of the specials: own-side edges violate disjoint support, and opposite-side edges close a length-three path through A-B.

There are twelve empty vertices. Remove eA,eB, leaving a ten-element set W. Let U_A=N_E(a1)∪N_E(a2) and U_B=N_E(b3)∪N_E(b4), both six-element subsets of W, and write k=|U_A∩U_B|.

The empty eA has exactly one heavy neighbor A, since no heavy support {3,4} exists. BC=J forces two singleton neighbors, hence degree seven gives four empty neighbors. It cannot meet eB (path eA-A-B-eB), or any vertex of U_A (path eA-A-ai-e). Therefore **N_E(eA)=W\U_A**, a four-element set. Likewise **N_E(eB)=W\U_B**.

It follows that eA and eB have k−2 common empty neighbors. C4-freeness gives **k≤3**.

But for each b-special bj, eA and bj have at most one common empty neighbor. Using the forced eA row, this says |N_E(bj)\U_A|≤1. Since |N_E(bj)|=3, at least two of its empty neighbors lie in U_A. The two b-special neighborhoods are disjoint, so **k≥4**. Contradiction.

Thus adjacent triples are excluded for every completion, independently of the pair-heavy edges or singleton/empty assignments. In the reviewed T2 heavy-core census, all remaining adjacent-triple cores are 1537, 6145, 9217 and 9729; the audit verifies the core-bit interpretation. This leaves core44 as the sole remaining candidate only if the already-reviewed other core exclusions and this argument are accepted. No original capped search was rerun or reclassified.

check.py independently enumerates the elementary set obstruction: fix U_A as any six of ten elements, then consider every ordered pair of disjoint three-element B-neighborhoods. The two required common-neighbor bounds never hold together. It also checks the T2 heavy-support list and adjacent-triple core IDs from the frozen census. This is a finite sanity check of the proof above, not a graph completion search. Independent mathematical review is pending; no Lean theorem or queue mutation is claimed.
