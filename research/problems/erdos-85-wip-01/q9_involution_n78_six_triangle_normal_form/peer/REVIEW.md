# Independent review 2243 — PASS

Both source pins and the accepted 2220 premise digest verified. The fixed triangle-with-leaves has fixed degree sum 12, attached sizes three times six and three times eight, and residual size 30. Each cubic attached vertex can use only its own group and the other two leaf groups before reaching R. The six lower bounds of five exactly exhaust R, forcing every claimed matching/injection and all three partitions into six five-vertex classes. The matched-partner class prohibition and within-class codegree bound correctly give residual degree at most five and an unmatched vertex in every odd class.

Independently enumerated all internal matching sizes and even cross deficits. Exactly (m,D,e)=(4,0,28),(3,0,30),(4,2,30) survive. Three pairwise cross deficits with endpoint totals at most two form either no deficient edge or one edge of deficit two. Thus the type-C pairing statement holds. Injections from the two allowed cubic groups each miss a free two-vertex orbit; the two orbits may coincide. The pointwise formula 5-alpha+epsilon correctly counts the internal and two cross-leaf slots, with epsilon supported on exactly two vertices for either non-A type.

Every residual vertex has three cubic-attached neighbors and 3-h leaf-attached neighbors, so its residual degree is 3+h. Combining with the partition bound gives h<=2. Summing the two missing residual vertices for each type-A leaf group yields sum h=6-2t and residual edge count 48-t. No coincident missing-orbit pattern is silently excluded except the proved h<=2 condition.

All deductions are necessary only. This accepts no residual realization and excludes no triangle-with-leaves case. The proof is a paper argument and has not been fully formalized in Lean here.
