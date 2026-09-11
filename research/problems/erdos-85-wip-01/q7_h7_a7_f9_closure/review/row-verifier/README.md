# Independent residual-row enumeration for review

rows.cpp enumerates candidate neighbors in increasing active-vertex order, as opposed to the production least-uncovered-high recursion. It removes candidates that would create a C4 with an existing neighbor, requires disjoint support colours and disjoint old neighborhoods among selected candidates, and checks exact total high-colour coverage and final degree. Singletons may only add pair vertices; pair vertices may add singleton or pair vertices. The output is a set of complete row masks; no search for simultaneous graph completion occurs.

Caller supplies a validated H/E/S/P-host a6 or a7 partial graph with all singleton edges fixed and no pair-low edges except empty hosts. The1024row buffer exceeds the structural maximum840 (pair degree5: choose3singleton support colours times2^3 times3pair matchings); pair degree4 has at most210, and singleton domains at most15. Negative return codes reject malformed inputs or unexpected buffer overflow.

The45existing a7/a6 fixtures give1575exact domain sets and5092rows, all matching accepted references. The independent traversal uses323550subset states. No residual family pass or new exclusion was performed for these tests.
