# Knowledge Base: szemeredi-regularity-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

The strong (Alon–Fischer–Krivelevich–Szegedy, 2000) regularity lemma is the
classical Szemerédi lemma applied *iteratively* with a decreasing tolerance. Its
proof splits into two halves:

1. **Energy-increment step (the analytic crux)**: if a partition is far from the
   almost-all-pairs / arbitrary-precision requirement, a refinement raises the
   partition energy (mean-square edge density) by a fixed positive amount `δ`.
2. **Finiteness / termination**: partition energy lives in `[0,1]`, so the
   `δ`-increment step can fire only `⌊1/δ⌋` times; the loop terminates.

Half (2) is elementary (bounded monotone potential) and fully reusable; half (1)
carries all the graph-theoretic content.

---

## Insights

- **Finiteness is a standalone, abstract fact** (S1, researcher-6): the
  termination half needs nothing about graphs — only a `ℚ`-valued potential
  `f : ℕ → ℚ` confined to `[0,1]` that jumps by `≥ δ`. Formalized abstractly in
  `SzemerediRegularityOQ04.lean` as `energy_steps_bounded` (`N·δ ≤ 1`),
  `no_infinite_energy_increments` (termination), then instantiated on the
  gallery's `partitionEnergy` via `partitionEnergy_nonneg` /
  `partitionEnergy_le_one`. Doing it abstractly means the *same* lemma bounds
  both the inner classical loop and the outer AFKS loop.
- The gallery already supplies the `[0,1]` confinement for free:
  `partitionEnergy_nonneg` (unconditional, Core) and `partitionEnergy_le_one`
  (needs cover + pairwise-disjoint, Regularity). No new energy analysis is
  required for the termination certificate.
- `le_div_iff₀` / `div_lt_iff₀` are the current (v4.26) subscripted names; the
  un-subscripted `le_div_iff` / `div_lt_iff` are deprecated.

---

## Dead Ends

- (None confirmed yet.) The energy-increment step (half 1) had a prior
  `energy_increment_step` attempt in the parent file that was removed due to
  Mathlib `simp`-normal-form drift on `Matrix`/`Finset.sum`; reconstructing it
  (probably via the surviving `split_energy_excess_bound`) is the next concrete
  task, not a dead end yet.

---

## Session 2026-07-08 (researcher-7) — Quantitative single-part energy increment

**Mode**: REVISIT (continuing own thread) · **Outcome**: progress (VERIFIED 0/0)

### What I Did
- Proved `pairEnergy_row_split_gain` (Energy file): summing the split contribution
  over a whole row of `B`-parts, one irregular partner `B₀` drives a definite gain
  `(|A₁||A₂|/(|A₁|+|A₂|))·(|B₀|/n²)·δ²`; other row terms are nonneg by
  `pairEnergy_split_mono`. Mechanism: `Finset.single_le_sum` on the per-term surplus
  `g B = f'(B) − f(B)`, then `Finset.sum_sub_distrib` + `linarith`.
- Proved `partitionEnergy_single_split_gain` (Bridge file): the actual quantitative
  energy-increment for the gallery `partitionEnergy`. Refining `A₁∪A₂ → A₁,A₂` with
  an irregular partner `B₀ ∈ R` raises `partitionEnergy` by the same δ² gain. Same
  block decomposition as `partitionEnergy_single_split_mono`, but the row block now
  carries the surplus; `linarith [h1, h2gain, h3]` assembles it.

### Key Findings
- The whole-partition jump localizes to **one** strengthened block. Diagonal and
  column blocks stay pure-monotone; only the row block against `R` needs the gain.
- The gain expression must be written syntactically identically in the row lemma and
  the partition-level goal so `linarith` matches it as a single atom.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Energy.lean (+pairEnergy_row_split_gain)
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (+partitionEnergy_single_split_gain)

### Next Steps
- Bolt the δ² gain onto the `[0,1]`-potential termination engine
  (`energy_steps_bounded` / `no_infinite_energy_increments`) to cap AFKS step count.
- Wire `exists_irregular_witness` to produce `B₀` and `hdev` from an ε-irregular pair.
