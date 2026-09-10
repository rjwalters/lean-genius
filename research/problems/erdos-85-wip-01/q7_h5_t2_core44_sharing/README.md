# Core44 C/F-sharing saturation and projection

This is a proposed branch reduction, pending independent review. It assumes the reviewed four canonical skeletons (2046) and isolated-F constraints (2047). C and F share exactly one singleton fs, with s=1 or2. The other branch, where they share none, is separate.

The five neighbours f0,...,f4 of F are distinct from the four triple specials a0,b0,b2,b4: each triple support overlaps F, so no singleton can have both as heavy neighbours. Each ordinary fi has only heavy F24 and requires singleton colours0,1,3 and two empty neighbours. The shared fs has heavy C13 and F24, requires only singleton colour0, and has three empty neighbours.

All five fi therefore require a colour0 singleton neighbour. Their five targets are distinct, because a repeated target would share two common neighbours with F. There are six colour0 singleton vertices: f0,a0,b0, and three others. The internal graph on the fi has maximum degree one, since a two-edge internal path together with F would be a C4. Its edges must satisfy reciprocal required colours. Consequently:

- Sharing at f1 permits no internal edge, f0-f1, or f0-f3.
- Sharing at f2 permits no internal edge, f0-f1, f0-f3, or f1-f3.

If f0 is not internally matched, it is not a colour0 target, so every other colour0 vertex is a target; in particular a0 and b0 each meet an fi. If f0 is internally matched, exactly one of the other five targets is omitted, so at least one of a0,b0 is a target.

The triple special a0 requires singleton colours3,4, hence its F-star neighbour, if present, is f3 or f4. The special b0 requires colours1,2, hence its F-star neighbour is f1 or f2. It cannot meet the shared fs: B and fs already share C, and b0 would be a second common neighbour. Every candidate also passes direct C4 checks, which remove choices giving an fi two colour0 neighbours. This leaves ten edge choices per canonical skeleton for sharing f1 and nine for sharing f2:76 in total. Absence of an a0/fi or b0/fi edge records that this special is not an F-star target.

`branches.py` enumerates all1024 internal graphs before applying these necessary restrictions, then constructs the76 partial skeletons. `search.py` enumerates every required two- or three-element empty-neighbourhood of the fi. At each completed incidence assignment it enumerates empty-induced graphs with exact degrees. Degrees are derived from the fixed heavy rows as 2+sum(weight(h)-1), unchanged by which singleton is shared. No symmetry pruning is used. The early empty-degree capacity check uses all currently legal partners and is monotone under adding edges.

The fixed budget was100000 combined nodes per(shared,omitted) group and60seconds overall. All76 cases finished:64 exhausted and12 admit partial witnesses; none capped or unvisited. Shared-f1 groups omitted0 and4 have no survivors. Other groups retain respectively1,1,1,4,2,3 cases. Each saved positive graph was checked directly for C4, exact empty degrees, and all forced heavy/special/F-star incidences.

Negative completeness and the branch-cover argument require independent review. The12 positive cases remain open, as do the surviving no-sharing cases. This is a necessary projection, with remaining ordinary singleton vertices and edges absent; no whole-core exclusion, Lean theorem, or SAT queue change is claimed. Earlier capped searches remain UNKNOWN and were not retried.
