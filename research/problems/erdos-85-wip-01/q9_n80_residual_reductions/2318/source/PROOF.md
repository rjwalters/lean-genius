# Uniform ten-edge residual bound in the N80/F10 cubic-fixed branch

Assume the N80/F10 cubic-fixed branch. Write d_1,...,d_5 for the residual degrees on its five free involution orbits, and D=sum d_i=e(G[R]). Accepted2295 gives0<=d_i<=3. The deficit identity is

 n_211+2n_221+2n_311=15-D.

If R has an isolated vertex, accepted2293 gives D<=10 directly.

Otherwise accepted2297 gives degree counts a,b,c for1,2,3 with a+b+c=5, a>=1 and c<=2. Therefore

 D=a+2b+3c=10-a+c<=11.

For D=11, necessarily a=1,c=2,b=2: the residual pattern is12233. Accepted2303 excludes precisely that pattern. Thus D<=10 also without isolation.

Consequently throughout this branch

 e(G[R])<=10,
 n_211+2n_221+2n_311>=5.

## All ten-edge equality patterns

Without isolation, D=10 means a=c. Since a>=1 and c<=2, the only possibilities are

 (1,2,2,2,3), or (1,1,2,3,3).

With isolation, two zero-degree orbits would give D<=3*3=9, so there is exactly one zero-degree orbit. Four positive integers at most three with sum ten are either1,3,3,3 or2,2,3,3. Thus the only isolated equality patterns are

 (0,1,3,3,3), or (0,2,2,3,3).

These four patterns are necessary alternatives, not existence claims. This argument deliberately uses only accepted2293/2295/2297/2303, and does not assume the pending exclusions2311/2313/2316. In particular it does not claim the stronger no-isolation D<=9 conclusion while those dependencies remain pending.

The accompanying small arithmetic verifier checks every sorted five-tuple in{0,1,2,3}, applying the stated accepted bounds, and reproduces precisely these equality patterns. It is an audit of the integer case list, not graph enumeration or new nonexistence evidence. No full graph solver or Lean formalization is used; Erdős85 remains unresolved.
