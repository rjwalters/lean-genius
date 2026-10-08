# Exact second-column decomposition for H3

Status: **source-only, uncompiled, unqueued**.

The audited first-column diagnostic found a single empty first column for
Full U3/R3 and Deficient U26/R2. A first-column split alone cannot parallelize
those two pairs. `Proofs.Erdos85ThreeHighSecondColumnSearch` extends the exact
decomposition by one more column, preserving both prefix gates and all six
remaining search levels, including the original distinct-neighbor terminal.

Its four proposed exports require rejection of every candidate combination
before yielding pair rejection and the conditional no-joint conclusion.
No concrete branch, pair, or stratum rejection is supplied. No runtime
improvement is claimed. The fixed U/R matrices are cached in each executable
two-column branch as they are in the verified first-column function.

Cloud verification will use the existing warm first-column worktree after
the live one-branch native pilot releases it. That pilot and the whole-pair
U1/R15 and Full261 census jobs are unchanged.
