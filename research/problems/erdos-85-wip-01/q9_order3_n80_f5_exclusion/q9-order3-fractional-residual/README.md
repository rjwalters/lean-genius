# Fractional residual model and58 exact negative certificates

PROOF.md derives a different necessary linear relaxation coupling optional color words to symmetric residual weights. Input focus is the60 UNKNOWN cases from2204; the capped integer searches were not rerun or extended.

A pilot on code669268 found a numerical candidate but exact rationalization failed before it was saved; terminal exit1 is recorded as UNKNOWN_RATIONALIZATION, no exclusion and no rerun. A separate batch covered the other59 cases under original60second aggregate cap (8.923seconds): one directly exact negative certificate,57 numerical candidates failing naive rationalization, and one code24538199 with no negative certificate (dual infeasible). The latter is unresolved: no exact primal witness has been verified.

repair.py processes only the57 saved numerical candidates, with no solver calls. It rounds weights to nonnegative integers at scale10^9, recomputes exact variable coefficients, and repairs each negative residual-edge coefficient by adding a nonnegative multiple of an existing y-2x<=0 inequality. This can only decrease x coefficients, which are then repaired by adding existing x<=1 inequalities. All final coefficients are nonnegative and the final RHS remains strictly negative. This is an exact Farkas contradiction; rounding accuracy is irrelevant once the resulting integers are checked. All57 repairs succeeded in0.681seconds.

verify.py separately recomputes all58 final integer weighted sums from model.py, proving nonnegative coefficients and negative RHS. It shares the model construction; independent reconstruction and proof review remain required. Complete certificates are in batch.jsonl (one original) and repaired.jsonl (57). Numerical candidates and initial statuses remain preserved, not rewritten as successful rationalizations.

Thus58 of the60 target cases have exact certificates conditional on the proposed model and prior finite coverage. Codes669268 and24538199 remain unresolved. No claim of N80/F5 exclusion, graph existence, or Erdős85 resolution. No graph/CNF/SAT launch occurred.
