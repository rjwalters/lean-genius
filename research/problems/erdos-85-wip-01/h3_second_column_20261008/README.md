# Exact second-column decomposition for H3

Status: **first cloud build failed; local proof-script fixes awaiting verification**.

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

The first cloud build at `765b97a125f` failed on Boolean-expression precedence
and a rewrite blocked by local definitions. `first-build.json` and
`first-build.log` retain that failure. Parenthesizing the equality and reducing
the local definitions addresses those errors; the revised source still needs
a passing cloud build. Verification uses the existing warm first-column
worktree, with 16 GiB, one compiler thread, and a 15-minute timeout.
The whole-pair U1/R15 and Full261 census jobs are unchanged.
