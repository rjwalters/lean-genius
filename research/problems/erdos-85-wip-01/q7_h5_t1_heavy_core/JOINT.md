# H5/T1 joint singleton-host supplement

Starting from the 235 per-colour survivors in results.json, enumerate all partitions of required heavy vertices into singleton hosts of each colour, with host capacities (5,5,5,4,4). Each bin has size one or two; a pair requires disjoint high supports and no common heavy neighbour. Choose one partition for each of five colours, prohibiting reuse of a heavy pair across colours: two such hosts would form a C4.

Every legal full graph induces such a choice. Enumeration permits unused singleton hosts and all possible bin pairings, so failure is a necessary obstruction. Hosts of one colour are interchangeable at this stage. Search exhausts all choices on rejection and stops at its first witness on success.

Result: 235 input classes, 24 rejected (220 labelled), 211 surviving (2220 labelled), zero capped cases; 1539 search nodes. This independently agrees with Claude's scratch enumeration reported in review2024. Each survivor saves a 49-vertex partial graph, with direct all-pairs common-neighbour checks and heavy-row BC=J checks. Thirteen empty-support vertices remain isolated; singleton completion and remaining degree conditions are unresolved. No full H5/T1 exclusion, Lean proof, SAT run, or Phase B queue change follows.

Reproduce with `python3 joint.py` beside the frozen results.json. The original core review2024 files are unchanged. This supplement awaits directed review.
