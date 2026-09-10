# Complete-colour0 decomposition excludes five shared-f2 configurations

This is a proposed finite exclusion of exactly the five configurations covered by reviewed relabelling lemma2053. Independent review of the full finite reduction is pending. The earlier F-star-first capped runs remain UNKNOWN; this uses a different decomposition that first names every vertex through complete colour0 slots.

Starting from the five reviewed49-vertex skeletons, `empty_slots.py` enumerates all60 assignments of the five remaining colour0-empty slots in each skeleton. Direct C4 checks leave132 partials, with per-skeleton counts28,28,24,28,24.

The only missing heavy-to-singleton edges are C's colour1 neighbour and D/E's colour3 and colour4 neighbours. All are among the fourteen newly named vertices: triple specials cannot have another overlapping heavy guest, F-star vertices already have F (and C at f2), and gA/gB/gC have colour0. `heavy_slots.py` enumerates these five requests, checking degree, reciprocal colour coverage and C4. There are1740 heavy-complete leaves. A necessary local degree/colour candidate check retains713, in counts170,109,132,170,132. The reciprocal support test is also implied by the C4 check with high vertices; it excludes no valid completion.

`propagate.py` repeatedly constructs all currently legal low-edge candidates. An edge is forbidden if an endpoint is full, it would duplicate a covered high colour, or it closes a C4. A missing colour with a single candidate forces that edge. If the number of possible neighbours equals the remaining degree, every such edge is forced. Too few degree candidates or no candidate for a missing colour rejects the partial. Every candidate set can only shrink as edges are added.

The propagation records all7984 forced edges across the713 inputs. It rejects711; the only two unresolved inputs belong to omitted4 with no internal F-star edge, heavy indices80 and94. `verify_traces.py` independently checks every forced edge and terminal contradiction with direct graph sets, degree bounds and actual common-high-neighbour tests, without importing the author's bitmask propagation. All713 traces pass.

`complete.py` branches on a missing colour requirement, or a remaining degree requirement after colours are covered, propagating after each choice. The two surviving fixed graphs exhaust at7 and13 nodes. `independent_completion.py` uses a separate set-based implementation, reversed vertex/colour/candidate ordering, and no author imports; both exhaust at3 nodes each. Neither implementation hits its100000-node/60-second limit.

Thus the proposed chain is300 assignments→132 colour0 partials→1740 heavy leaves→713 necessary-domain survivors→711 deterministic contradictions and2 exhaustive completion contradictions. The five original shared-f2 configurations have no completion if this cover and the algorithms are accepted. This does not alone exclude the other shared-f2 configurations, shared-f1, no-sharing, core44, or Erdős85. It is not a Lean theorem or a SAT queue mutation.

`completion-pins.json` freezes the reviewed naming inputs and all scripts/results used in this submission. The older `README.md` and `pins.json` remain the original2053 relabelling submission; this supplement does not alter them.
