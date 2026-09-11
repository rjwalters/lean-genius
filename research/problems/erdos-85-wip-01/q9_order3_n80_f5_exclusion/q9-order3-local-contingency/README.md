# Complete local attached-pair feasibility table

Conditional on the attached walk bound submitted as review2187, enumerate one direct S3 permutation and three independently specified S3 path compositions through the other attached groups: exactly 6^4=1296 cases. Treating the path compositions as independent enlarges the global possibilities and is appropriate for this necessary local filter.

The contingency table has margins (4,3,3); there are exactly 65 nonnegative integer tables with these margins. The producer tests each against the entrywise walk bound, retaining 1004 permutation cases and rejecting 292. Every rejection records either a negative upper capacity or a row-subset capacity obstruction. Original wall cap60seconds; all1296 COMPLETE in0.026363seconds, no UNKNOWN or unvisited case. No full permutation-system enumeration, matching phases, graph lift, CNF, or SAT run occurred.

verify.py independently forms the capacities by matrix multiplication and uses integral maximum flow instead of contingency-table enumeration. It checked all1296 feasibility classifications successfully. Its check supports feasible/infeasible classification, not the producer's exact number of allowed tables in each record.

This local lookup can prune later complete necessary-system enumeration; neither its retained cases nor its rejected cases settle the N80/F5 graph class.
