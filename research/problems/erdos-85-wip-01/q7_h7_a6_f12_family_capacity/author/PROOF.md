# Coupled singleton-family capacity

Use the accepted H7 host branch and reviews 2706/2708. For every pair vertex p, let F(p) be an overestimate of its possible sets of singleton neighbours in a completion. If its singleton demand is one, F(p) contains every individually eligible singleton. If its demand is three, F(p) contains every eligible singleton triangle that passes the necessary two-pair high-colour support-matching condition of review 2706. An actual completion selects exactly one member A(p) of F(p) for each p.

Let c(s)=7-deg(s) be the residual degree of singleton s. Its remaining edges must all go to pair vertices. Thus the number of selected sets A(p) containing s is exactly c(s).

For any subset K of the fourteen singleton vertices, double counting gives

    sum_p |A(p) intersect K| = sum_{s in K} c(s).

Since A(p) belongs to F(p), necessarily

    sum_p min_{A in F(p)} |A intersect K|
        <= sum_{s in K} c(s)
        <= sum_p max_{A in F(p)} |A intersect K|.

A strict violation on either side is an integer certificate excluding the branch. Unlike a capacity test on the union of eligible edges, this retains correlations between the three singleton choices at a pair vertex. It remains a relaxation: satisfying every subset inequality does not imply a consistent simultaneous choice of families or a graph completion.

One bounded probe tests the 29 branches left by review 2708, considering at most 16382 nontrivial singleton subsets per branch with a shared 60-second limit. Any unclassified or unfinished branch remains explicit. The probe does not regenerate complete residual rows or run ARC, and leaves all historical capped evidence unchanged. This is a necessary finite graph criterion, not a Lean/kernel or global Erdős 85 proof.

The single probe completed all 29 cases in 2.048 seconds. Five branches have strict subset-capacity certificates and 24 remain unclassified. Independent set-based family reconstruction checked the five inequalities in 0.003 seconds; all five have deficiency one. The proposed combined negative count is 397210 of 397234 leaves, subject to peer review.
