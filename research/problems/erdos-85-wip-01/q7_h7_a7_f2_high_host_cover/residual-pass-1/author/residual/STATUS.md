# F2 partial residual result — root remains open

The exact completed host cover (review 2657, banked under q7_h7_a7_f2_high_host_cover) has 785,408 ordered leaves. This pass used the byte-identical accepted F9 residual row/arc implementation, subject to a single 120 s aggregate / 100,000-operation-per-leaf cap. The saved source export was joined to every complete host receipt before launch.

At 120.0036 s the pass stopped: 705,051 INFEASIBLE_ROW, 824 INFEASIBLE_ARC, one UNKNOWN, and 79,532 unvisited leaves. There are no ARC_FEASIBLE reports in the visited prefix. The 705,875 negatives are necessary-condition contradictions. UNKNOWN and the unvisited suffix remain unresolved. The producer has not been restarted or extended.

A separate increasing-active-index row enumerator verified all negative endpoints in 11.876 s: 733,891 complete domains, 106,634 rows, 1,660 atomic arc removal batches and 2,046 failed support rows. The verification does not strengthen the UNKNOWN case. Source export provenance is additionally subject to peer review.

The exact frontier is in frontier.json. Only source bases 82 and 93 retain unresolved leaves; the other 46 of the 48 source bases have no remaining leaves after the reviewed upstream reductions and these negative checks. This count includes bases with no E/S graphs or no high assignments upstream. The sole UNKNOWN is case 3710, pairing 1, leaf 9 (source base 82, singleton index 1094). Total unresolved host leaves: 79,533.

F2 is exactly the frozen root cube_F7_t2: the root mask 328007 has the seven edges 01,02,03,12,14,35,45, including isolated vertex 6. f2-root-mapping.json records the identity map. None of this closes F2, H7, H1, or Erdős 85, and no Lean theorem or solver-queue change is claimed. The full H7 root count remains unchanged.

The host package is frozen under host-pins.json and was byte-verified at integration 992d0ea618. residual-pins.json separately pins this bounded pass, its export, receipts, verifier, and frontier. Original runner provenance uses absolute paths; saved hashes determine input identity.
