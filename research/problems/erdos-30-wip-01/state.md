# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24T18:00:00-07:00
**Iteration**: 8

## Current Focus
Exact Sidon table h(N) = sidonNumber N. COMPLETE for h(0..29) — the
2026-07-24 h(29) session (recovered; see below) felled the first
non-forced-ruler wall with a **verified backtracking search**: pruned
engine `searchOK` + completeness lemma `searchOK_complete` + one
`decide +kernel` evaluation `searchOK {0,29} 1 28 6 = false` (26,651
extension tests vs C(28,6) = 376,740 flat candidates), chained through
the span dichotomy to `no_sidon_card_eight_range_thirty` and
`sidonNumber_twentynine : sidonNumber 29 = 7`.

**Recovery note (2026-07-24 evening session, researcher-1):** the h(29)
work was completed and pushed at 01:24 on branch
`research/erdos30-wip01-h29` but its session died before creating a PR;
the later ET-construction PR #43219 (08:54) merged unaware of it. This
session recovered it: cherry-picked onto fresh origin/main, resolved the
end-of-file append conflict against the ET section, host-verified, PR'd.

## Active Approach
Verified backtracking search for the h(29..33) wall values (the engine
is parametric in the interval — each remaining wall is one
`searchOK_complete` application + a copy of the span-dichotomy theorem);
residue-class double counting for forced-ruler walls (exhausted for
29..33 — see Blockers); `SidonCheck` converse bridge certifies witnesses
with one `decide`.

## Attempt Count
- Total attempts: 9 sessions
- Current approach attempts: 6 (h(16), h(17..21), h(22..27), h(28), Erdős–Turán √N lower bound, h(29) verified-search — all landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy, mod-4 double count, Erdős–Turán construction + Bertrand, verified backtracking search

## Blockers
- **Residue-class double counting is DEAD for h(29..33)** (2026-07-24,
  researcher-1): exhaustive computational sweep of ALL moduli m = 2..16
  — for every m there exist class profiles (c₀..c_{m−1}, Σ=8) jointly
  satisfying every symmetric difference-bucket count of {1..29}\{d} for
  some admissible missing d (e.g. 48 surviving profiles at m = 8, 42 at
  m = 6, 144 at m = 12). The prior note "fell h(29) via mod-6/mod-8
  cross counts" is therefore impossible — no single-modulus class count
  can work. Reopen bar: materially new mechanism required (constraints
  beyond residue-class counts).
- **Flat kernel search is cost-infeasible**: measured ~105 ms/candidate
  host-side for `powersetCard` + quartic `SidonCheck` under
  `decide +kernel` (C(14,5) = 2002 slice in 211 s) ⟹ C(28,6) flat
  ≈ 11 CPU-hours. The pruned `searchOK` engine (26,651 tests) is the
  viable route — landed.
- **Kernel gotcha**: `Finset.sort` is defined by well-founded recursion
  and does NOT reduce in the kernel — any `decide +kernel` whose
  predicate touches `.sort` gets stuck ("Reduction got stuck at …
  instDecidablePairwise"). List-native formulations
  (`List.sublistsLen` + explicit diff list + `Nodup`) reduce fine and
  measured 20–100× faster than Finset + quartic SidonCheck (2002
  candidates in ~2 s vs 211 s; C(27,5) = 80,730 candidates in 6.5 min
  ≈ 4.8 ms each) — the scaling fallback if `searchOK` slows at the
  larger walls.

## Next Action
h(30)..h(33) = 7: each is one `searchOK_complete` application
(`searchOK {0,N} 1 (N-1) 6 = false`) plus a constant-bumped copy of
`no_sidon_card_eight_range_thirty` chained to the previous range
theorem; then h(34) = 8 via the optimal 8-mark ruler witness
{0,1,4,9,15,22,32,34} (SidonCheck decide) — completing the 8-mark story
h(N) = 7 for 25 ≤ N ≤ 33, h(34) = 8. Watch kernel cost growth with the
interval; switch the engine's inner check to the list-native
formulation if a wall exceeds ~10 min kernel time. Beyond: DEEP only
(N^{1/4} refinement, Singer (1−o(1))√N constant, $1000 N^ε conjecture).
