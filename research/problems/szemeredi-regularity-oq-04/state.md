# Research State: szemeredi-regularity-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-08T18:27:58-07:00
**Iteration**: 2

## Status (S1, researcher-6, 2026-07-08) — VERIFIED finiteness engine for the AFKS iteration

Created `proofs/Proofs/SzemerediRegularityOQ04.lean` (0 sorry / 0 axiom;
`docker-build Proofs.SzemerediRegularityOQ04` succeeded). Moves the problem from
OBSERVE (no Lean) to ACT with real machine-checked content.

The strong (Alon–Fischer–Krivelevich–Szegedy) regularity lemma is proved by
*iterating* the classical lemma: whenever the partition fails the almost-all-pairs
arbitrary-precision requirement one refines it, and each refinement raises the
mean-square edge density (partition `energy`) by a fixed `δ > 0`. Since energy is
trapped in `[0,1]`, the loop runs at most `⌊1/δ⌋` times. This session formalizes
exactly that finiteness engine, built on the gallery's own `partitionEnergy` and
its bounds `partitionEnergy_nonneg` (Core) / `partitionEnergy_le_one` (Regularity):

- `energy_steps_bounded` — abstract telescoping bound: an `[0,1]`-valued potential
  `f : ℕ → ℚ` that jumps by `≥ δ` at each of the first `N` steps satisfies
  `N • δ ≤ 1`. Proof: induction gives `f 0 + m·δ ≤ f m` for `m ≤ N`, then combine
  `0 ≤ f 0` and `f N ≤ 1`. No sign hypothesis on `δ` needed for this form.
- `energy_iteration_count_le` — `δ > 0` count form `N ≤ 1/δ` (via `le_div_iff₀`).
- `no_infinite_energy_increments` — termination: no `[0,1]`-valued potential can
  increase by a fixed `δ > 0` at *every* step (Archimedean `exists_nat_gt`).
- `partitionEnergy_iteration_bound` — graph instantiation: a refinement chain of
  covering, pairwise-disjoint partitions whose `partitionEnergy` grows by `≥ δ`
  each step has length `≤ 1/δ`.
- `partitionEnergy_no_infinite_increments` — the AFKS energy-increment loop halts.

This is the reusable, verified ingredient every proof of the qualitative strong
lemma consumes. It is deliberately stated abstractly (over a `ℚ`-valued potential)
so the same engine also bounds the *outer* AFKS loop once the energy-increment
step (a bad `ε`-irregular pair forces `energy ↑ δ`) is supplied.

## What remains open (the OQ-04 goal proper)

1. **Energy-increment step**: quantify "if the fine partition has `≥ ε·C(ℓ,2)`
   non-`E(k)`-regular pairs then a refinement raises `partitionEnergy` by a fixed
   `δ = δ(ε)`." The parent `SzemerediRegularity.lean` has the split-energy
   excess lemmas (`split_energy_excess_bound`) but an assembled
   `energy_increment_step` was previously attempted and removed — this is the
   substantive missing piece.
2. **Two-level statement**: spell out the AFKS conclusion — a coarse
   `ε`-regular partition `V₁..V_k` and a refinement `W₁..W_ℓ` with all but
   `ε·C(ℓ,2)` pairs `E(k)`-regular — in Lean, with the dependent tolerance
   `E : ℕ → (0,1]` threaded correctly (chosen *after* seeing `k`).
3. **Assemble**: run the outer loop using `partitionEnergy_no_infinite_increments`
   as the termination certificate.

## Active Approach
Iterate the classical lemma with bounded energy (approach 1 from problem.md).
The finiteness/termination half is now done and verified; the energy-increment
step (item 1) is the next target and the true crux.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (bounded-energy iteration — finiteness half verified)

## Blockers
None new. The energy-increment step needs the removed `energy_increment_step`
reconstructed (Mathlib `simp`-normal-form drift on `Matrix`/`Finset.sum` was the
original obstacle — see parent file NOTE near `split_energy_excess_bound`).

## Next Action
The quantitative energy-increment is now DONE and assembled (S3, researcher-7,
PR #35839): one irregular-partner split realizes a uniform floor `δ²/(2n²)`
(`partitionEnergy_single_split_gain_uniform`), which caps the AFKS refinement loop
at an explicit `N ≤ 2n²/ε²` (`afks_energy_iteration_count`). Remaining:
1. Wire `exists_irregular_pair` (SzemerediRegularity.lean:152) to auto-produce
   `B₀ ∈ R` and `hdev` from an ε-irregular pair (currently hypotheses).
2. State the two-level AFKS conclusion (coarse ε-regular partition + refinement
   with all but `ε·C(ℓ,2)` pairs regular), dependent tolerance `E : ℕ → (0,1]`.
3. Assemble the outer loop using `afks_energy_iteration_count` as the certificate.
