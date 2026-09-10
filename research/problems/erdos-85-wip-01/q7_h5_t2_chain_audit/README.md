# T2 reviewed reduction coverage audit

A separate direct enumeration checks all 32768 six-heavy-vertex edge sets by constructing the full graph on five high and six heavy vertices, testing every pair for at most one common neighbour, and checking support-weight and residual-degree requirements. It finds 52 labelled graphs and exactly the same 13 canonical cores under eight support automorphisms as the frozen census. It imports no census or search implementation.

The disjoint reviewed reductions are:

| Review | Excluded cores | Remaining count |
| --- | --- | --- |
| 2026 | 36,48,513,656,2049 | 8 |
| 2035 | 1,2120 | 6 |
| 2041 | 210 | 5 |
| 2045 | 1537,6145,9217,9729 | 1 |

Only core44 remains. The audit validates all four source manifests and binds the actual result and resolved PASS review files by SHA256. It checks exact set subtraction at every stage. The four underlying exclusions rely on their recorded mathematical and independent computational reviews; this audit does not rerun those searches or produce a Lean proof. Historical capped searches remain capped, including cases subsequently excluded by distinct arguments. No core44 branch result, solver queue, H5 closure, or global Erdős85 conclusion follows here.

Run `python3 check.py /absolute/path/to/research/problems/erdos-85-wip-01`. The output is written beside the checker. This audit itself has not yet received a separate squad review.
