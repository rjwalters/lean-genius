# High colours and pair hosts over the cycle-empty singleton projection

This package extends the 459 E/S graphs covered by review 2107. Its research pass is gated on live PASS for 2107 and the no-adjacent-same-high-singletons reduction 2096. It does not retry any earlier capped host census.

Each high has one single-empty singleton and one double-empty singleton. Name highs by the seven single-empty singleton vertices; every possible high assignment is then a bijection to the seven double-empty vertices. A matched pair must be nonadjacent (2096) and have disjoint E/S neighbour sets. The latter condition is exactly what prevents a new C4 when their common high is added. Different highs have disjoint singleton pairs and cannot create another C4 together.

Each empty now meets three distinct singleton high colours. Its two pair neighbours must partition the four missing high colours: exactly three perfect matchings. No high pair may be used at two empties, since a pair vertex has at most one empty neighbour. Conversely, these conditions suffice for the H/E/S partial graph to remain C4-free after inserting the 21 pair vertices, their high edges and the chosen empty incidences. Two pair vertices cannot share two highs, nor share both a high and an empty because each empty uses a matching. A pair and singleton cannot share both high and empty because only missing singleton colours are used. All other possible common-neighbour pairs inherit the E/S graph or have at most one new common neighbour. Every H/E common-neighbour count is exactly one.

Labels in the reconstructed graph are H=0..6, double-empty singleton=7..13, single-empty singleton=14..20, pair=21..41 in lexicographic high-pair order, empty=42..48. Original E/S labels are empty=0..6 and singleton=7..20. Each result stores its original X representative index, singleton completion index, pairing list (high -> double-empty index 0..6), and seven 21-bit matching masks.

`run.py` visits each E/S graph once, with 100000 recursive operations per graph and a single 60-second aggregate deadline. All pairings and complete host assignments reached are stored. A cap preserves UNKNOWN and explicit unvisited counts; neither can support exclusion. Existing results are never overwritten. The pass is only an incidence extension, with remaining singleton-pair and pair-pair edges absent.

`verify.py` independently enumerates all 5040 bijections per terminal case and uses reverse-empty breadth-first products over independently reconstructed matching options. It checks exact pairing and host-assignment sets, reconstructs every surviving 49-vertex partial graph, and checks all common-neighbour bounds, high/empty degrees and H/E incidences. It does not replay capped cases.

No claim about the entire F=C7 class, other empty graphs, H7, Lean closure or Erdős 85 follows merely from surviving partial graphs.

The guarded pass completed all 459 cases in 3.336 seconds, with 5,035,812 operations total and at most 44,880 per case. It stores 18,874 high pairings and 1,531,654 pair-host assignments. No case was capped or unvisited. Independent verification recovered these exact sets and checked all 1,531,654 full partial graphs in 10.832 seconds; 12,408,279 verification states total, with no cap. All remain candidates for residual-edge filtering, not complete graph witnesses.

`results.json.gz` is the deterministic compressed copy of the original terminal output `results.json` (both are preserved). `graphs.cpp` implements the independent full-graph check used through ctypes by `verify.py`; compile with `clang++ -std=c++17 -O2 -shared -fPIC graphs.cpp -o graphs.dylib`. Original source pins and live premise snapshots are retained.
