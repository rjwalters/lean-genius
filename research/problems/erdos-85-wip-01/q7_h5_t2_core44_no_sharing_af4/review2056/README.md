# No-sharing core44 excludes af4/bf2

Use the reviewed core44/no-CF-sharing F-star saturation (review2047). F has neighbours f0,...,f4, all singletons. Its induced neighbour graph consists of exactly f1-f3. Each fi needs one singleton neighbour of colour0, these five neighbours are distinct, and none is f0. Thus they biject onto the five members of S0 other than f0.

The colour0 class is S0={a0,b0,f0,p,q,r}, where a0 and b0 are the A- and B-specials and p,q,r are heavy-free. A and B both contain high colour0, so a0 and b0 already have their unique colour0 common neighbours. The other four S0 vertices must form a perfect matching, by BC=J. Name the heavy-free mate of f0 as p; the remaining edge is q-r. This renaming is permitted in the entire prospective graph.

Suppose af4/bf2: a0-f4 and b0-f2. The five distinct F-star colour0 targets then include f4→a0, f2→b0, f0→p. Therefore f1 and f3 target q and r in some order. Together with the forced f1-f3 and q-r edges, these two edges form a four-cycle. Contradiction.

This excludes af4/bf2 independently of all empty incidences and all colour3 matching choices. Combined with the separate no-sharing bf1 exclusion submitted as review2055, and the reviewed exhaustive choices af∈{3,4},bf∈{1,2}, only af3/bf2 remains in the no-sharing case. The combined conclusion is conditional on acceptance of that separate proof. Neither argument excludes the remaining af3/bf2 configurations, sharing at f1 or f2, core44, or H5.

The tiny independent finite check examines all120 bijections of F-star vertices onto the five targets. Exactly two satisfy the three fixed assignments, and both explicitly contain the stated four-cycle. No capped completion search is repeated. Independent squad review is pending; this is not a Lean proof.
