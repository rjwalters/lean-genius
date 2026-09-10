# Crossed H7 profile14: complete-row arc exclusion

One bounded pass on all448 LOCAL_FEASIBLE assignments in the frozen crossed14 local-filter input. All448 return INFEASIBLE_ARC, with zero UNKNOWN/unvisited. Combined generation/compatibility budget100000 perassignment; global60second deadline. Actual12,381,483 operations and7.40seconds. No retry or solver. The other32 of480 assignments are excluded in the upstream local-filter evidence, not recomputed here.

The22-profile host cover is reviewed2068, and pair assignment enumeration reviewed2070. Portable local-filter necessity reviewed2069. This package concerns only crossedprofile14 and requires those upstream premises plus the32 local negatives for a whole-profile exclusion. It does not close H7 or the original Erdős problem and is not a Lean theorem.

## Why complete rows cover all completions

At this complete host stage, every outside vertex has only its high neighbours and one host. New neighbours must be outside vertices. Two new neighbours cannot belong to the same host group: they would share both their host and the source vertex. C4 saturation against all seven degree8 high vertices requires exact missing-high-colour coverage. The generator enumerates each eligible group by skip-or-one choice, with required degree7, disjoint exact colours, and no existing common neighbour among selected neighbours. It retains all choices and uses no symmetry or first-witness cut. A completion's row therefore appears in its domain. Every domain completes before arc filtering starts.

## Why arc deletion excludes a graph

Rows at u and v must agree on the edge uv, and their final neighbour sets can have at most one common element. Existing neighbours are all highs/hosts and new neighbours all outside, so common-neighbour count splits into the existing count plus new-row intersection. If a row has no compatible row at another vertex, it occurs in no global completion. Sequential deletions preserve all completions; an empty domain proves impossibility. Results retain every initial domain and every deletion batch.

verify.py does not import the generator: it checks all rows for exact degree, common-high incidence, and new C4s using direct sets, and replays every deletion with full final-neighbour set intersections. This checks soundness and certificate execution; independent generation or audited exhaustive traversal remains the completeness premise.

Artifacts: input.json exact frozen source, filter.py reusable bounded API, run.py one-shot runner, summary.json terminal accounting, results.json.gz domains/traces, verification.json direct-set audit. UNKNOWN must never prune; ARC_CONSISTENT would not establish existence. No capped domains were rerun.
