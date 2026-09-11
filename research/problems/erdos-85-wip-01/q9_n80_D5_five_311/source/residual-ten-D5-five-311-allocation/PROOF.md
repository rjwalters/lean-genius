# Five-311 aggregate defect allocation at D5

Conditional inputs2458/2460/2463 give the complete3856 necessary packing roots on seven residual action classes; the eighth class has no packing. Every high vertex has support size three, so every high W-neighbor contributes weight two to the endpoint budget.

Introduce one high defect variable Q[v,e] in[0,1] for each specified high vertex and residual endpoint, identifying involution images. For each residual singleton support r introduce L[r,e], the sum of defect edges from low vertices supported at r to endpoint e. Its bounds are0<=L[r,e]<=n_r, where n_r=9-d_R(r)-high incidence. Identify its involution images as well.

Residual-middle endpoints force Q[v,e]=0. If B_v=k_v+2-sum support degrees is zero, all its defect entries vanish. The high row sum is at most B_v, because any high W neighbors consume the remaining endpoint budget.

For low support r, an adjacent residual endpoint e forces L[r,e]=0. Its row sum is at most(3-d_R(r))*n_r. In particular the cubic-supported low rows vanish. Every residual column has exact prescribed degree q_e, counting all high variables and low aggregates.

Z=E_RR and D=CZ-ZC are reconstructed exactly from residual adjacency and all high supports. Each variable occurrence with support a and target t contributes [t=i][j in a]-[i in a][t=j] to the commutator entry(i,j). For an aggregate low occurrence a is the singleton support. All45 off-diagonal commutator equations are imposed exactly. The saved model includes every original bound and labeled equation/inequality.

## Additional parity lower bounds

For each high vertex, its defect row size equals B_v minus twice the number of high neighbors. Nonnegativity therefore gives row size at least B_v mod2. For an individual singleton-low vertex supported at r, the defect row size equals 3-d_r minus twice the number of high neighbors, so it is at least (3-d_r) mod2. Summing over its n_r low vertices gives the aggregate lower bound ((3-d_r) mod2)*n_r. Both lower bounds are imposed in the saved model, in addition to the original upper bounds. The model relaxes parity to these bounds and does not assert sufficiency.

No forced-cubic defect columns are imposed: the older one-isolated-orbit argument is not used on the two-isolated-orbit input classes. Everything here follows from generic endpoint budgets, exact columns and commutation, plus the all-high3 premise.

## Exact results

All3856 models are constructed in7.968866 seconds under the original30-second cap. A separately capped30-second allocation run completes in19.397819 seconds. The solver only discovers candidates; exact Fraction arithmetic checks every nonnegative Farkas combination for zero coefficients and strictly negative right side, or every witness against all original inequalities. Zero terms are omitted from arithmetic without changing equations.

There are832 exact Farkas contradictions, covering all72/240/208/312 roots in classes1/2/3/4. The remaining3024 exact rational witnesses are the960/720/1344 roots in classes5/6/7, respectively the three matching actions. Together with class0's empty packing list, this excludes all nonmatching residual shapes within D5/s5, conditional on independent acceptance of the input cover and this packet. Feasible rational aggregates do not establish graph realizations. Other s counts and global N80/Erdős85 remain open; no Lean theorem or capped-domain retry is claimed.
