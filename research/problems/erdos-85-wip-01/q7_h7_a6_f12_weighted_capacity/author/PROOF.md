# Refined support families and weighted capacity

## Refinement of the necessary families

Reviews 2706–2711 establish exact high-support counting and singleton demands. A pair vertex with saved degree two needs three singleton neighbours and two pair neighbours; one with saved degree three needs one singleton and three pair neighbours. After choosing the singleton part, the remaining high colours must therefore admit a perfect matching by eligible pair supports (four colours/two edges or six colours/three edges). Eligibility rejects only known four-cycles against the saved neighbours and chosen singleton vertices. The test deliberately ignores four-cycles between the chosen pair vertices, so it remains a necessary relaxation.

Let F(p) consist of all singleton choices passing this refined support-matching condition. Every actual graph completion selects one member A(p) of F(p). If F(p) is empty, the branch is impossible.

## Weighted exact inequality

For any integer weights w(s), including negative weights, the singleton degree identities give

    sum_p sum_{s in A(p)} w(s) = sum_s c(s) w(s),

where c(s) is the singleton residual capacity. Since A(p) lies in F(p), necessarily

    sum_p min_{A in F(p)} sum_{s in A} w(s) <= sum_s c(s) w(s).

A strict reverse inequality is an integer certificate of impossibility. This extends subset weights from review 2711 to arbitrary signed weights and uses the stricter demand-one family cover above.

## Discovery and verification scope

A floating-point linear program searches bounded weights and auxiliary lower bounds, with two seconds per case and a shared 60-second probe limit. Its status is never an exclusion. Candidate weights are converted to rational numbers, cleared to integers and checked against the complete necessary families using integer arithmetic. Only a strict exact inequality (or an exactly empty necessary family) produces a negative certificate. Numerical failure, zero margin or a feasible relaxation leaves the case unclassified.

The probe acts once on the 24 cases remaining after review 2711, never invokes the old residual row/ARC API, and does not modify the historical capped frontier. This is a finite necessary graph obstruction, not a Lean/kernel or global Erdős 85 proof.

The probe completed all 24 inputs in 0.047 seconds. One exact weighted certificate rejects (227135,9), with minimum -51 exceeding capacity -55; 23 cases remain unclassified. Independent set reconstruction checked all 62 necessary family members and the exact inequality in 0.002 seconds. No numerical LP verdict was promoted. Proposed composed coverage is 397211 of 397234 leaves, subject to peer review.
