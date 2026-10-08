# Exact first-column decomposition of the H3 native search

Status: **source awaiting cloud verification**.

`Proofs.Erdos85ThreeHighFirstColumnSearch` expresses the existing native pair
search as the Boolean OR over its complete static-pruned first-column list.
Each branch retains the first prefix check, all seven remaining DFS levels,
and the original distinct-neighbor terminal. It caches U/R and fixed degree
data, as the original search does.

The assembly theorem requires rejection of **every** first-column candidate.
A subset of completed branches cannot establish a pair rejection. The final
consumer retains the cross-domain and external-cap hypotheses. No concrete
branch, pair, or stratum rejection is supplied by this module.

The equality proof and four associated exports are to be checked in an
isolated cloud branch. The running U1/R15 and Full261 jobs are unchanged.
This module enables smaller parallel proof units; no runtime improvement is
claimed until measured.
