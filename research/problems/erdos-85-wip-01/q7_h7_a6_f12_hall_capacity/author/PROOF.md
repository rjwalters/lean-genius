# Global singleton–pair Hall capacity

In the accepted H7 host branch, all singleton–singleton, high and empty incidences are complete. The only missing neighbours of a singleton are pair vertices, so singleton s has remaining capacity c(s)=7-deg(s), equal to two or three.

The high two-walk counting argument of review 2706 gives exactly seven high-support incidences around every pair vertex p. Its known neighbours are high or empty, hence have empty high support. If d=deg(p) is its saved degree (two or three), its new neighbours include a singleton vertices and b pair vertices, with a+b=7-d and a+2b=7. Thus its exact singleton demand is a=7-2d (three or one). In this a6 host shape the total demand and capacity are both 39; the verifier checks these totals per input.

Form a bipartite eligibility graph between the 21 pair and 14 singleton vertices. Remove an edge if adding it already creates a four-cycle using saved edges. For a degree-two pair vertex, also remove a singleton candidate unless it lies in some compatible singleton triangle whose remaining high colours have the necessary two-pair support matching from review 2706. This removes only impossible incidences, since every actual completion supplies such a triangle and matching.

For any set U of pair vertices, the completion requires sum_{p in U} a(p) distinct incidences into the singleton side. Singleton s can accommodate at most min(c(s), number of eligible neighbours of s in U) of them: its total missing degree gives the first bound and simplicity gives the second. Therefore

    sum_{p in U} a(p) <= sum_s min(c(s), |N(s) intersect U|).

A violated inequality is a direct certificate excluding the entire host branch. A small integral flow computation may discover U, but verification needs only eligibility checks and this inequality. No flow success implies a graph completion, and no residual rows or ARC are generated.

Apply this distinct global cut once to the 129 cases left by review 2706. Historical capped residual evidence remains immutable. This is a necessary finite graph statement, not a Lean/kernel or global Erdős 85 proof.

The single probe completed in 0.120 seconds: 100 Hall certificates and 29 unclassified cases. Independent verification regenerated eligibility with sets, checked 2916 triangle conditions and the 100 strict inequalities without calling max-flow, passing in 0.063 seconds. Deficiencies range from one to three. The proposed composed negative count is 397205 of 397234, subject to peer review.
