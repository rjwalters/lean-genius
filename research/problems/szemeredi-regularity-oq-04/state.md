# Research State: szemeredi-regularity-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-08T19:18:01-07:00
**Iteration**: 3

## Status (S7, researcher-2, 2026-07-11) — VERIFIED PART III + count-form variance atom

Verified the whole `SzemerediRegularityOQ04.lean` axiom-free via the Docker-free path
(`bin/lake env lean`, prebuilt oleans): S6's variance-atom additions
(`weighted_variance_eq`, `weighted_variance_atom_bound`, `weighted_variance_subset_bound`,
`weighted_sq_mean_le`) — previously UNVERIFIED under a Docker blackout — all report
`#print axioms = [propext, Classical.choice, Quot.sound]`.

Added `weighted_variance_card_bound`: the **count form** of the variance atom. With a
uniform weight floor `w₀ ≤ wⱼ` on the deviating cells `J`, the energy floor becomes
`(|J| : ℚ)·w₀·d² ≤ (∑ wᵢxᵢ²) − (∑ wᵢ)·μ²` — i.e. "`≥ N` cells of weight `≥ w₀`, each
deviating by `≥ d`" raises partition energy by a fixed `δ = N·w₀·d²`, exactly the
per-step jump that `energy_steps_bounded`/`energy_iteration_count_le` cap (iteration
count `≤ 1/(N·w₀·d²)`). Proof: `weighted_variance_subset_bound` + `Finset.sum_const`
pooling of the weight floor. VERIFIED axiom-free. This closes the abstract gap between
the pooled-weight atom and the AFKS irregular-pair *count*; the remaining open piece is
still the quantitative `d = d(ε)` from ε-irregularity (item 1 analytic input).

## Status (S6, researcher-6, 2026-07-09) — the variance atom (remaining item 1), UNVERIFIED docker-down

Discharged the abstract half of "Next Action" item 1 (the variance atom bound
`Σ wᵢ xᵢ² − (Σwᵢ)μ² ≥ w₀·d²`) in `Proofs/SzemerediRegularityOQ04.lean`, PART III:
- `weighted_variance_eq` — König/Huygens identity `Σ wᵢ(xᵢ−μ)² = (Σ wᵢxᵢ²) − (Σ wᵢ)μ²`,
  stated multiplicatively (`Σ wᵢxᵢ = (Σ wᵢ)·μ`) so no division by total weight.
- `weighted_variance_atom_bound` — nonneg weights + a single index `j` with
  `d² ≤ (xⱼ−μ)²` give `wⱼ·d² ≤ (Σ wᵢxᵢ²) − (Σ wᵢ)μ²` (drop all non-`j` terms via
  `Finset.single_le_sum`; the surviving `wⱼ(xⱼ−μ)² ≥ wⱼd²`).

This is the reusable abstract engine behind the AFKS energy-increment step: a
refinement whose sub-cell densities deviate from the parent mean by defect `d`
raises `partitionEnergy` by `≥ wⱼ·d²`, the positive `δ` that `energy_steps_bounded`
caps in number. Pure `Finset.sum` algebra, 0-sorry/0-axiom, no new API. Docker
infra down all session (containerd meta.db I/O error) → shipped UNVERIFIED with
hand-audit. The remaining *quantitative* input `d = d(ε)` from ε-irregularity, and
the two-level AFKS statement + outer-loop assembly (items 2–3), are unchanged.

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
Both whole-partner one-sided energy increments are now proved (S5, researcher-7):
`partitionEnergy_Aside_gain_of_irregular` (refine A vs whole B) and its mirror
`partitionEnergy_Bside_gain_of_irregular` (refine B vs whole A), each realizing the
uniform floor `ε²/(8n²)`. Confirmed (S5) that no single-triangle decomposition of a
witness deviation gives both legs against whole parts — the mixed second-difference
(defect) obstructs it, so full closure needs the 4-cell simultaneous refinement +
variance/second-moment bound (the hard analytic core). Remaining:
1. Prove the abstract variance atom bound `Σ wᵢ xᵢ² − (Σwᵢ)μ² ≥ w₀·d²`, then
   instantiate over the 4 sub-cells for the true ε⁴ energy increment.
2. State the two-level AFKS conclusion (coarse ε-regular partition + refinement
   with all but `ε·C(ℓ,2)` pairs regular), dependent tolerance `E : ℕ → (0,1]`.
3. Assemble the outer loop using `afks_energy_iteration_count` as the certificate.

## Update (2026-07-11, researcher-8 — variance minimizer / energy-monotonicity core)

The variance-atom bounds (`weighted_variance_atom_bound`, `weighted_variance_subset_bound`)
were already present; item 1 of the prior "Next Action" is done. Added the complementary
*variational* half of the variance toolkit — the abstract reason partition energy is monotone
under refinement (3 theorems, 0 sorry / 0 axiom, VERIFIED `bin/lake env lean`, all
`[propext, Classical.choice, Quot.sound]`):
- `weighted_variance_nonneg` — `0 ≤ (∑ wᵢxᵢ²) − (∑ wᵢ)μ²` (the `d = 0` skeleton of the atom
  bound; energy never drops below a coarsening's).
- `weighted_variance_le_of_mean` — the weighted mean minimizes weighted MSE:
  `∑ wᵢ(xᵢ−μ)² ≤ ∑ wᵢ(xᵢ−c)²` for every centre `c`, via the parallel-axis expansion
  `∑ wᵢ(xᵢ−c)² = ∑ wᵢ(xᵢ−μ)² + (∑ wᵢ)(μ−c)²`. This is exactly why replacing a part's mean
  density by sub-cell (conditional) means increases the partition energy.
- `weighted_variance_le_second_moment` — the directly-consumable multiplicative form:
  `(∑ wᵢxᵢ²) − (∑ wᵢ)μ² ≤ ∑ wᵢ(xᵢ−c)²`.

Remaining (unchanged): the two-level AFKS conclusion (item 2) and the outer-loop assembly
(item 3). No gallery meta change (research-only file; parent slug tracks the base proof).
