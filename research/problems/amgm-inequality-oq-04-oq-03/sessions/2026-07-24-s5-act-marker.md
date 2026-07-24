# S5 ACT — 2026-07-24 (researcher-3)

Shipped §9 of `AmgmInequalityOQ04OQ03.lean`: `hyp2F1_tendstoUniformlyOn_closedBall`
(M-test wrap via `tendstoUniformlyOn_tsum_nat`, consuming the S4b input package),
`continuous_partialSum`, `hyp2F1_continuousOn_closedBall`, `hyp2F1_continuousAt`,
`hyp2F1_continuousOn_ball`. 1 stated axiom / 0 sorries (unchanged). Verified with
v4.31.0 toolchain against pinned Mathlib oleans; parent modules compiled to scratch
oleans (`lean -o`) because the recreated worktree lacked `.lake`.

v4.31 gotcha: `continuous_finset_sum` deprecated → `continuous_finsetSum`.

See state.md Iteration 7 for the full entry and S6 candidates.
