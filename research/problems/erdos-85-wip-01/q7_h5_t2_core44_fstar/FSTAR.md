# Core44 no-sharing F-star projection

Assume the reviewed four-pattern cover (2046) and isolated-F/no-sharing saturation lemma (2047). Only the branch where C and F share no singleton is considered here. The five neighbours f0,...,f4 of F are distinct from a0,b0,b2,b4, since each special already has a triple heavy neighbour overlapping F. Each fi has exactly two empty neighbours. Their only internal edge is f1-f3.

The five colour0 requests from the fi use all colour0 singletons except f0. In particular, a0 and b0 each meet one fi. The two uncovered singleton colours at a0 are3,4, so its F-star neighbour is f3 or f4. At b0 they are1,2, so its F-star neighbour is f1 or f2. These give four choices for each of the four reviewed empty-incidence skeletons.

`fstar_empty.py` constructs each skeleton with those forced edges, then enumerates all two-element empty-neighbourhoods of the five fi by direct C4 checks. At a complete incidence assignment it enumerates all empty-induced graphs with the exact degrees derived from the heavy support weights. It uses no symmetry pruning. The early empty-degree capacity check counts every currently legal empty partner; adding further edges cannot make a previously forbidden partner legal. Dynamic minimum-domain choices change traversal order only.

All sixteen choices finished within the fixed limits of100000 combined nodes per canonical skeleton and60seconds overall. Fourteen yield partial witnesses, directly checked for C4, exact empty degrees, and the forced F-star incidences. Two exhaust: omitted empty index11 or0, in both cases with a0-f3 and b0-f1. Independent review of those two negatives is pending. These results exclude neither the no-sharing branch as a whole nor core44. The C/F sharing branches at f1 or f2 were not searched.

`fstar-pins.json` freezes the source, input skeletons, results and direct positive verification. This is a different decomposition from the earlier capped E-first ordinary-singleton partition pilot. Those four capped results remain UNKNOWN and were not retried.
