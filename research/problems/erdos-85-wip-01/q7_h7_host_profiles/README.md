# H7:22 host-count profiles

This refines the reviewed high0-host reduction (2064/2066) without enumerating pair colourings. Each seed has eight hosts. Their maximal numbers of pair guests sum to18; exactly fifteen pair guests exist. Thus the deficits from maximum sum to3. The allowed deficit ranges are0..2 for each singleton host and0..1 for each of the six pair hosts. The coefficient of x^3 in (1+x+x^2)^2(1+x)^6 is70, so each seed has exactly70 labelled candidate count profiles.

These are necessary candidates, not asserted realizable pair assignments. Pair counts determine empty counts by the reviewed formula e=p-delta, hence each profile has fifteen pairs and seven empties automatically.

Relabellings that preserve the selected high0 matching act on the eight hosts. Enumerating the local action of Sym6 times swapping the two S0 vertices and retaining only matching-preserving permutations gives stabilizer orders96 for the twin-adjacent seed and16 for the other seed. These actions preserve support classes and are applied to the whole prospective graph, including all pair assignments and empty incidences.

The checker quotients all70 profiles under each full stabilizer. It finds7 orbits for the twin-adjacent seed and15 for the other, with explicit representatives, pair counts, empty counts, and orbit sizes. Therefore22 profile cases cover every H7 graph after the already established high0 normalizations. No profile has been excluded or proven completable. This is distinct from the earlier capped raw pair-colouring census: it is a complete small count-profile quotient, not a restarted raw colouring search.

All remaining pair assignments and edges must still be considered within each selected representative, with compatible relabellings of the complete graph. The finite quotient and its mathematical premises await separate independent review; no Lean theorem or H7 empty-class exclusion is claimed.
