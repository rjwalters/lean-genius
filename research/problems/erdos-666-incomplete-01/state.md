# State: erdos-666-incomplete-01

## Current Phase: ACT

**Phase**: ACT
**Status**: Active
**Started**: 2026-04-03T05:22:49
**Last Updated**: 2026-07-08 (researcher-3)

## Progress Summary

Added and VERIFIED the hypercube's structural invariants (researcher-3, 2026-07-08),
grounding the previously-bare numeric definitions in the actual graph `Hypercube n`:

- `hypercube_degree`: Qₙ is n-regular — every vertex has exactly `n` neighbours
  (the n bit-flips `x ⊕ 2ⁱ`, i<n). Proved via an explicit injection
  `Fin n ↪ neighborFinset x`, using `Nat.xor_lt_two_pow` for well-definedness,
  xor left-cancellation (`xor_assoc`/`xor_self`/`zero_xor`), and injectivity of
  `i ↦ 2ⁱ` (`Nat.pow_right_injective`).
- `hypercube_isRegular`: packaged `IsRegularOfDegree n` form.
- `hypercube_card_edges`: `(Hypercube n).edgeFinset.card = hypercubeEdges n = n·2ⁿ⁻¹`,
  derived from n-regularity via the handshake lemma
  `sum_degrees_eq_twice_card_edges`.

These carry no assumptions beyond the ambient `Classical.choice` (used only for
adjacency decidability). The entry's single deep axiom `chung_no_threshold`
(Chung's 4-partition of Qₙ into C₆-free subgraphs) is unchanged: eliminating it
requires the explicit combinatorial construction, which is not in Mathlib
(>1000 lines — BLOCKED). docker-build verified (Lean v4.26.0); the first attempt
hit a transient exit-135 volume corruption, clean on retry.

Entry file: 326 → 412 lines, theoremCount 5 → 8, axiomCount 1 (unchanged), 0 sorries.

## Current Focus

The formalization is complete apart from the deep `chung_no_threshold` axiom.
Remaining work is either (a) the full Chung edge-partition construction
(BLOCKED — large combinatorial build) or (b) further structural lemmas
(e.g. bipartiteness, C₄-freeness of 2-direction subgraphs).

## Blockers

`chung_no_threshold`: requires Chung's explicit 4-partition of Qₙ into C₆-free
subgraphs (constant-fraction density for all n). No Mathlib support; >1000 lines.

## Next Action

Optional follow-ups (not required — entry is otherwise complete):
1. Prove Qₙ is bipartite (2-colour by bit-parity), explaining absence of odd cycles.
2. Formalize a concrete C₆-free 2-direction subgraph (edges in 2 fixed coordinates).
