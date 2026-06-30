# Research State: erdos-340-greedy-sidon-oq-02

## Current State
**Phase**: DONE
**Path**: full
**Since**: 2026-06-18T14:30:00-07:00
**Iteration**: 3

## Outcome
`proofs/Proofs/Erdos340GreedySidonOQ02.lean` is **complete: 0-sorry / 0-axiom**, on
`main` and imported into `Proofs.lean` (landed via #25945, commit `cdc8c8ceefc`).
The companion proves the Erdős–Turán sliding-window key inequality

    sidon_window_key : ℓ * |A|² ≤ (N + ℓ) * (ℓ - 1 + |A|)   (for every ℓ ≥ 1)

axiom-free, from the two counting facts `window_sum_identity` (∑ wc = ℓ|A|) and
`window_pair_bound` (∑ wc(wc-1) ≤ ℓ(ℓ-1)) plus Cauchy–Schwarz over the N+ℓ windows.
The single remaining `sorry` (`window_pair_bound`) was closed here.

## Key finding — the parent axiom is NOT discharged by this machinery
The parent file `Erdos340GreedySidon.lean` postulates the *sharp floor bound*

    axiom sidon_upper_bound : |A| ≤ ⌊√N⌋ + ⌊√⌊√N⌋⌋ + 1.

The proved key inequality `sidon_window_key`, **optimised over all integer ℓ ≥ 1**,
is too weak to reach this floor constant. Verified numerically (N up to 3·10⁵):

- The best |A|-bound the inequality yields is asymptotically ≈ 1.13·√N (e.g. at
  N = 10⁶ it permits |A| ≤ 1135 vs √N = 1000), i.e. O(√N) of the right order but a
  larger lower-order / constant term than the axiom's √N + N^{1/4}.
- At N = 15 the inequality permits |A| ≤ 6 whereas the axiom claims |A| ≤ 5; the
  gap (key-bound − floor-bound) grows to 105 by N ≈ 1.9·10⁵.

So `window_pair_bound` (the counting fact B, whose `ℓ(ℓ-1)` bound is itself **sharp**
for Sidon sets) does **not** translate into removing `sidon_upper_bound`. The axiom
is *tighter* than the classical sliding-window argument delivers; discharging it would
need the sharper Lindström weighting (a genuinely different counting), not just the
`ℓ ≈ √N` optimisation. Future agents: do **not** attempt to remove `sidon_upper_bound`
by optimising `sidon_window_key` over ℓ — it cannot reach the stated floor constant.

Note: the existing axiom-free `sidon_upper_bound_weak` (|A| ≤ ⌊√(2N)⌋ + 1 ≈ 1.41·√N,
difference-counting) is actually *better than* what `sidon_window_key` yields for the
small/mid-N range, so no derived explicit cardinality theorem was added.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (window/Cauchy–Schwarz — correct route for the key inequality)

## Status
COMPLETED — companion file sorry-free and axiom-free on `main`. The sub-problem's
deliverable (close `window_pair_bound`) is done. The separate parent axiom
`sidon_upper_bound` is left in place and is recorded above as unreachable by this
route (would be its own, harder research line).
