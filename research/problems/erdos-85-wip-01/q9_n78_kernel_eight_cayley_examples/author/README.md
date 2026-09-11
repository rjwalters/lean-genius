# Local cubic Cayley examples for two remaining kernel types

Two explicit groups of order24 are tested: D8 times C3, with D8 the square symmetry group of order eight, and (C2)^3 semidirect C3, where the order-three action cyclically permutes the three binary coordinates. Group elements and full multiplication tables are saved. Associativity and identity were checked directly; the formulas are also the standard direct/semidirect product definitions.

For each group, the designated kernel K consists of elements with last coordinate zero. Every tested connection set is {t,a,a^-1}, with t a nonidentity involution in K and a of last coordinate one. Thus it is inverse-closed and has one member in each K-coset. All40 sets in the first group and56 in the second were checked once under the original30-second limit. There are16 and48 C4-free cubic Cayley graphs respectively; all surviving adjacency lists are saved, with distinct-vertex codegrees checked directly.

These are local positive examples for the cubic24-orbit requirement of proposed2278. They do not assert a compatible graph on the other24-orbit, cross matchings, residual orbit, six fixed centres, or a complete78-vertex graph. They show only that this one induced-orbit requirement does not eliminate these two explicit group actions. No classification of all group extensions or fullgraph solver is used. Counts are labelled connection sets, not nonisomorphic graphs.

Run `python3 check.py` to reconstruct the group tables and finite local check. The current run is complete; no timeout/retry occurred. Independent review of positive examples is requested separately.
