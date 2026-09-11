# Degree profiles when an involution fixes ten vertices

Use the graph/involution notation and necessary inequalities of2220, now with F=10. The fixed induced graph H has odd degrees1,3,5,7,9. Its degree sum is S and its unattached residual set has size R=N-100+S. The attached set B_v has size9-r_v.

In addition to the boundary, cherry, and residual-capacity inequalities from2220, every fixed vertex v satisfies

    sum_{w in N_H(v)} (r_w-1) <=9.

This counts distinct nonreturn two-step endpoints in the other nine fixed vertices. Consequently, for a proposed degree profile, the sum of the r_v smallest available values r_w-1, excluding v itself, is at most9. This is only a necessary profile test; it does not assume that the actual neighbors are the lowest-degree vertices.

Exact enumeration of all five degree counts summing10 leaves:

| N | counts at degrees1,3,5,7,9 | S | R |
|---|---|---:|---:|
|78|0,10,0,0,0|30|8|
|78|1,9,0,0,0|28|6|
|80|0,10,0,0,0|30|10|
|80|1,7,2,0,0|32|12|
|80|1,9,0,0,0|28|8|
|80|2,5,3,0,0|32|12|
|80|2,8,0,0,0|26|6|

## Degree-five profiles are impossible

In either surviving degree-five profile, every degree5 vertex needs a leaf neighbor: without one, its five neighbors all have degree at least3 and give at least10 nonreturn two-step paths, exceeding9. Distinct degree5 vertices cannot use the same leaf, since a leaf has degree1. But those profiles have respectively two degree5 vertices and one leaf, or three degree5 vertices and two leaves. Both are impossible.

## Residual size six forces saturation

For each degree3 fixed vertex v, the2220 capacity bound gives at least6 incidences from B_v (size6) into R. If R has size6, every residual vertex has exactly one neighbor in B_v, and each B_v vertex has exactly one residual neighbor.

A vertex x in B_v then has eight moved neighbors, one of them in R. Its possible attached neighbors consist of at most one in B_v itself and one in each of the six other fixed-centre groups not adjacent to v in H. Thus equality holds: all six allowed cross groups are met exactly once and the internal neighbor exists. In particular, whenever a leaf centre u is not adjacent to v, there are exactly6 edges B_v--B_u.

At N78, the one-leaf profile has nine degree3 centres and R6. Every residual vertex already has nine attached neighbors, so there are no edges from R to the leaf's B_u or inside R. The leaf group has size8 and total moved-degree64. It has at most8 internal incidences and exactly6 from each of the eight degree3 centres other than the leaf's fixed neighbor. This accounts for at most8+48=56, a contradiction.

At N80, the two-leaf profile has eight degree3 centres and R6. The two leaves cannot be adjacent to each other: that edge would be a fixed neighbor component of two leaves, leaving a cubic graph on eight vertices, impossible by the accepted cubic-small-order argument used in2176. Thus each leaf is adjacent to a degree3 centre. For either leaf group B_u (size8), the seven nonadjacent degree3 centres contribute42 incidences. Its own group contributes at most8, the other leaf group at most8, and R at most6. These bounds total64, its moved-degree sum, so equality holds. Both leaf groups therefore meet every residual vertex. Such a vertex has eight neighbors from the degree3 groups and two more from the leaf groups, contradicting degree9.

## Conclusion and scope

If an involution fixes ten vertices, then at N78 its fixed graph is cubic. At N80 its fixed graph is either cubic or has exactly one degree1 vertex and nine degree3 vertices. The corresponding residual sizes are8 at78, and10 or8 at80. No surviving fixed graph or full graph is asserted to exist. This is a necessary structural reduction only, not an involution-class exclusion or a solution of Erdős85.
