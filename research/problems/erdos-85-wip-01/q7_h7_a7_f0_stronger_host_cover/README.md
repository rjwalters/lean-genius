# F0 stronger necessary host cover

Accepted review 2674. The complete F0 high cover has 18,408 assignments.
Sixty empty inputs from review 2656 and eight from review 2672 are reused;
their exact complement of 18,340 inputs was covered by the cached pair-row
host API (2669). All completed, with 17,632 additional empty inputs and
3,012 residual leaves. The original cap records remain unchanged.

All saved coverage and 8,765,351 negative endpoints passed the independent
2670 checker, partitioned by queue index modulo four under one 240-second
deadline. Review 2674 independently reconstructed every graph, checked the
original reused inputs and full receipt accounting, and audited the checker
execution and partition join. It did not independently repeat every endpoint.

The scope is a necessary host cover for cube_F7_t0, mask 139591. Residual
checks remain required. Upstream review 2116 establishes S-enumeration
completeness by code audit rather than independent enumeration replay.
This package is not a whole-root exclusion, Lean proof, arbitrary CNF UNSAT
claim or solution of Erdős 85. See the pinned author status for exact budgets.

Author and review payloads are verbatim. BANK_PINS.json hashes every payload.
