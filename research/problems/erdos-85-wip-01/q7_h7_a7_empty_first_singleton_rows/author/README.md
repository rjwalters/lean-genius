# Fixed empty-first singleton completion pilot

Inputs are the117C4free high+empty-complete partial graphs from the two positive fixed proper-colouring fixtures in reviewed2097. They are NOT a full Q-colouring, R/F or H7 domain. The other two fixed fixtures have noC4free singleton-host assignment at that earlier stage. This is a different variable decomposition; no old high0host census or capped case was rerun.

One necessary singleton-row pass uses100000operations perpartial/60seconds overall:92arc negatives and25arc-consistent cases, zeroUNKNOWN/unvisited,174099operations. Each singleton's inducedSdegree is5-2e, i.e.1or3. Same-high singleton edges are forbidden by2096. All remaining S-neighbour combinations are retained if adding that whole star is C4free. Pairwise rows must be reciprocal and have at most one common final neighbour; deletion of unsupported rows preserves every Sgraph completion.

One subsequent bounded enumeration of the25uncapped row products uses precomputed support bitsets and exact arc propagation,100000operations percase/60seconds total. All25complete, yielding33distinct Sgraphs on18bases; seven more bases are impossible. These Sgraphs still lack P-S/P-P completion. No surviving graph is claimed to be a full H7 witness.

verify.py imports neither generator. It independently enumerates every initial row by unrestricted singleton subsets and direct whole-star common-neighbour checks (9089rows), replays12576failedsupports, then independently completes all25Sgraphs by filling actual graphvertex stars with full49vertex C4 checks. It reproduces exactly the33graphs, with no caps. Source hashes, all117graph arrays, rowdomains, deletions and final Ssolutions are retained.

surviving-bases.json supplies the18base graphs before S edges are added, suitable for the independently developed generic E-first row API. The fixedscope remains explicit:92+7negative partials and18partial bases with33Sextensions, not a whole proper-colouring class, a7 or H7 exclusion. Original solver queues and historicalUNKNOWNs are unchanged.
