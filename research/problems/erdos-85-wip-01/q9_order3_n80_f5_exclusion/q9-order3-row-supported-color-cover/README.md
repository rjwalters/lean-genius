# Row-supported color selection frontier

Input exactly576 fractional-positive symmetry representatives from2201, using the candidate words and pair capacities prepared for2203. Search combines that complete ten-word selection enumeration with a necessary test for residual quotient rows at each complete selection.

For a residual orbit i, row sum4 and squared norm<=6 permit at most one entry2. The diagonal is0or2. Therefore the full list of possible rows consists of126 four-distinct-cross-single rows,252 rows with one doubled cross entry and two other cross singles, and36 rows with diagonal2 and two cross singles:414 total. For each candidate row, count its weighted neighbors by each of the five color coordinates. All15 marginal counts must be<=b(w_i), as in accepted2194. A complete coloring is rejected if any orbit has no such row. Rows need not be mutually symmetric in this relaxation; row support is necessary only.

Original100000node cap percase and60second aggregate wall cap, no retry or cap increase. All576 cases visited; terminal process3.150seconds,17,784,458states,54,989complete color selections rejected by a row obstruction. Outcomes516 COMPLETE_NEGATIVE and60 UNKNOWN at exactly100000states each. Zero positive, zero unvisited. UNKNOWN cases remain open; this is not a full N80/F5 exclusion. Only completed negative cases can be used, subject to peer verification of coverage and premises.

Compared with2203, this stage continues past the first integer coloring when it lacks residual row support. It checks all possible colorings for a representative only when that representative terminates COMPLETE_NEGATIVE. No symmetric Q, edge phases, graph, CNF or SAT search was run.

status-verification checks the exact case set and original-cap fidelity, not negative completeness. Full source and receipts are frozen for independent audit. The preceding diagnostic found a row obstruction for each of518 first saved colorings, but that alone would not have excluded any of their matching representatives.
