# a6 F16 necessary graph-cover exclusion

Accepted source/input chain 2118/2122/2125/2699 supplies 48759 quotient graphs covering 62985 raw highs. Host review 2701 accepts all 48759 COMPLETE inputs: 1963 zero-leaf highs and 500280 surviving assignments, with 931977 singleton prunes independently checked.

The residual API from reviews 2120/2126 rejects all 500280 assignments: 379324 ROW and 120956 ARC contradictions, with no positive, UNKNOWN or unvisited case. The producer completed in 81.795 seconds under 120 seconds/100000 nodes per leaf; 65.49 MB in two shards fits the 150 MB cap.

Independent raw-source reconstruction, exact host export and all negative endpoints pass in 39.455 seconds under 120 seconds. This checks 4612784 complete domains, 20546518 rows, 379027 ARC batches and 471809 unsupported removals.

The exact root is cube_F6_t15, mask 622659, with parent-to-source permutation [2,3,4,0,1,6,5] independently checked in review 2699. Whole closure awaits peer review. Source enumeration and quotient completeness remain inherited premises; this is no arbitrary CNF UNSAT, Lean/kernel, whole H7 or global theorem claim.
