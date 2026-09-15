# Pair vertex singleton-triangle obstruction

## Necessary statement

Work inside an accepted H7 host branch. The seven high vertices and seven empty vertices have their final neighborhoods. Every other vertex is a singleton (one high neighbour) or a pair (two high neighbours). The graph is simple and C4-free. Its completion must give every low vertex degree seven.

Let a pair vertex u currently have degree two, so both its known neighbours are high. Its five missing neighbours must be active low vertices. Write s for singleton neighbours added and p for pair neighbours added. Then s+p=5. No two neighbours of u can have the same high neighbour: that would give a four-cycle through u and that high vertex. Thus their high supports are disjoint and s+2p<=7. Subtracting from twice the first equation gives s>=3. This uses only a capacity inequality, not an assumed exact high-support partition.

A possible new singleton neighbour v cannot share a neighbour with any known neighbour w of u: the edges u-w-x-v-u would form a four-cycle. This determines an overestimate C(u) of eligible singleton vertices using only the saved graph. Any two chosen singleton neighbours v,z must have disjoint known neighbourhoods, since a common neighbour x would form u-v-x-z-u. Define a compatibility graph on C(u), joining v and z exactly when their known neighbourhoods are disjoint.

If this compatibility graph is triangle-free, u cannot acquire its required three singleton neighbours. The entire host branch is impossible. All tests are direct adjacency and triangle tests. Neither residual-row domains nor ARC propagation are generated.

## Bounded application

The accepted F12 host cover (review 2130) has 397234 leaves. The accepted residual prefix (review 2135) rejects 395763 leaves, leaving one recorded UNKNOWN and 1470 unvisited leaves. This new probe takes exactly those 1471 leaves, preserving the historical files and statuses.

The single 60-second probe completed in 0.215 seconds. It supplies triangle-obstruction certificates for 1253 leaves, including the historical UNKNOWN (227088,0). The other 218 leaves remain unclassified by this criterion. Combining these new certificates with the accepted prefix would cover 397016 of 397234 leaves, subject to independent review. This is not a whole F12, H7, Lean/kernel or global Erdős 85 proof.

The initial invocation failed before creating launch.json because it used the wrong host-manifest filename; that path was corrected to pins.json. No criterion evaluation or capped search had started. The only completed criterion probe is recorded in launch.json/results.json.
