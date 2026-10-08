# Exact second-column decomposition for H3

Status: **cloud verified; four exports with standard axioms only**.

The audited first-column diagnostic found a single empty first column for
Full U3/R3 and Deficient U26/R2. A first-column split alone cannot parallelize
those two pairs. `Proofs.Erdos85ThreeHighSecondColumnSearch` extends the exact
decomposition by one more column, preserving both prefix gates and all six
remaining search levels, including the original distinct-neighbor terminal.

Its four exports require rejection of every candidate combination before
yielding pair rejection and the conditional no-joint conclusion. No concrete
branch, pair, or stratum rejection is supplied. No runtime improvement is
claimed. The fixed U/R matrices are cached in each executable two-column
branch as they are in the verified first-column function.

Cloud job `20261008T042206-erdos85__h3-first-column-20261008-176612`
passed at source commit `603bac25c0d`, using the existing warm first-column
worktree, 16 GiB, one compiler thread, and a 15-minute timeout. The fresh
target took 3.7 seconds. Each export reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or native axiom.
`proof-pass.json` records the matched source/object hashes and report inventory;
`proof-pass.log` preserves the complete raw cloud log.

The first cloud build at `765b97a125f` failed on Boolean-expression precedence
and a rewrite blocked by local definitions. `first-build.json` and
`first-build.log` retain that failure. Parenthesizing the equality and reducing
the local definitions fixed those errors. The whole-pair U1/R15 and Full261
census jobs were unchanged.
