# Complete high-colour cover for the F9 non-cycle a7 slice

The source is the independently accepted2116 non-cycle projection. F_index9 is the disjoint union of a triangle with one pendant leaf and a separate triangle, with edges01,02,03,12,45,46,56. All39 host bases for this F finished their S enumeration before the aggregate cap, giving1620 complete labelled E/S graphs. None belongs to the UNKNOWN or unvisited frontier.

In a7 every high pairs one single-empty singleton with one double-empty singleton. Name the highs by the seven single-empty vertices. Every high assignment is then a bijection to the seven double-empty vertices. As in accepted2110, a matched pair must have disjoint E/S neighbor sets, exactly preventing a C4 when its common high is added. It must also be a nonedge by2096. Naming the high vertices in this way loses no extension. This criterion does not depend on F being a cycle.

highs.py visited all1620 source graphs once under100000 recursive nodes per graph and60seconds aggregate. All completed:148 admit no high assignment;1472 admit28336 assignments in total. Maximum372 nodes per graph,161115 total,0.080seconds. No pair-host assignment or residual-edge filtering was run.

verify_highs.py independently enumerates all5040 bijections per graph and derives forbidden pairs by explicit shared-neighbor counting. Every saved pairing set and every source index match exactly:28336 pairings,1472 positive and148 negative graphs,2.227seconds. The input cover and original capped frontier are unchanged.

For the next stage, an empty e must partition its2deg_F(e) missing high colours into deg_F(e) pair hosts, with no pair vertex shared by two empties. F9 has degrees3,2,2,1,2,2,2, hence at most15 times3^5 raw matching combinations per fixed high pairing. This stage has not been launched. The reviewed singleton-host criterion can prune partial host assignments monotonically, but an implementation and its budget will be reviewed separately.

This is a complete high-colour cover only for the already complete F9 E/S slice. It is not an exclusion of F9, the other non-cycle shapes, a7, H7 or Erdős85, and supplies no Lean theorem. The previous UNKNOWN base and449 unvisited bases are not rerun or reclassified.
