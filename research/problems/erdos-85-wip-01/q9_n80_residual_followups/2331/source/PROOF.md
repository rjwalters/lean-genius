# Uniform nine-edge residual bound in the N80/F10 cubic-fixed branch

Accepted2318 proves D=e(G[R])<=10 and lists exactly four possible equality patterns. All four are now independently excluded:

 01333 by2320;
 02233 by2324;
 11233 by2313;
 12223 by2316.

Therefore D<=9 and the attached incidence identity gives

 n_211+2n_221+2n_311=15-D>=6.

This conclusion uses only resolved PASS premises, not the pending stronger three-leaf-orbit reduction2330.

## Remaining nine-edge equality cases

Accepted2295 bounds residual degrees by three. With isolation and D=9, two or more isolated orbits would leave at most six active vertices. Exactly six active vertices would require nine edges, contradicting the accepted2320 seven-edge bound for a free involution; fewer active vertices cannot supply nine edges with maximum degree three. Thus exactly one isolated orbit remains. Four positive degrees at most three summing to nine give only01233 or02223. The latter is excluded by accepted2326. Hence the isolated equality pattern is01233.

Without isolation, use accepted2297: a+b+c=5, a>=1,c<=2 and D=10-a+c. Equality D=9 means a=c+1, giving12222,11223,11133 for c=0,1,2 respectively. Accepted2311 excludes11133. Thus the no-isolation equality possibilities remaining in this accepted-premise composition are12222 and11223.

Consequently the necessary D=9 list is exactly

 (0,1,2,3,3), (1,1,2,2,3), (1,2,2,2,2).

No realizability is asserted. The separately submitted2330 would remove the last two and strengthen the no-isolation bound to eight; that stronger claim is not needed or assumed here.

The finite arithmetic check only exhausts the56 sorted degree tuples under these explicit accepted restrictions. It is not graph enumeration or new graph nonexistence evidence. No full graph solver or Lean formalization is used; Erdős85 remains unresolved.
