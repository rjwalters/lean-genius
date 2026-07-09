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

## Session 2026-07-08 (researcher-7) — Uniform floor + explicit AFKS count; recovered wrongly-superseded gain

**Mode**: REVISIT (continuing own thread) · **Outcome**: progress (VERIFIED 0/0), PR #35839

### What I Did
- Recovered the quantitative gain lemmas (`pairEnergy_row_split_gain`,
  `partitionEnergy_single_split_gain`) that PR #35809 carried — that PR was
  auto-closed as "superseded" by `check-superseded.sh`, a **false positive**: the
  guard flags a branch when the file *paths* it touches exist on `main`, ignoring
  that the specific theorems were never on `main`. Rebasing onto current `main`
  (files exist at merge-base ⇒ `NOT_SUPERSEDED (modifies existing files only)`)
  fixes it.
- Proved `parallel_resistance_ge_half`: `x·y/(x+y) ≥ 1/2` for `x,y ≥ 1`
  (`nlinarith` on `(x-1)(y-1) ≥ 0`).
- Proved `partitionEnergy_single_split_gain_uniform`: floors the exact
  size-dependent gain `(|A₁||A₂|/(|A₁|+|A₂|))·(|B₀|/n²)·δ²` to the clean,
  part-count-free `δ²/(2n²)` using resistance ≥ 1/2 and `|B₀| ≥ 1`.
- Proved `afks_energy_iteration_count`: a refinement chain whose `partitionEnergy`
  climbs by the uniform floor `ε²/(2n²)` each step has length `N ≤ 2n²/ε²` — a thin
  corollary of `partitionEnergy_iteration_bound` via `one_div_div`, pinning the
  AFKS step count to an explicit polynomial in `n`, `1/ε`.

### Key Findings
- The whole AFKS finiteness now reads as one clean chain: an irregular-partner
  split *realizes* the fixed floor (`..._uniform`), and the floor caps the loop at
  `2n²/ε²` (`afks_energy_iteration_count`).
- **Build gotcha**: three line-less `exit-135` SIGBUS crashes MASKED a real
  `No goals to be solved` error (`gcongr` already discharged the `1 ≤ |B₀|`
  subgoal via `assumption`, so a trailing `exact hB` was redundant). Only
  `docker-build --repair-cache` (fresh olean force-refresh) let elaboration
  complete and surface the genuine error at 4.7 s.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Energy.lean (pairEnergy_row_split_gain, recovered)
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (partitionEnergy_single_split_gain recovered; + parallel_resistance_ge_half, partitionEnergy_single_split_gain_uniform, afks_energy_iteration_count)

### Next Steps
- Wire `exists_irregular_pair` to auto-produce `B₀`, `hdev` from an ε-irregular pair.
- State the two-level AFKS conclusion with the dependent tolerance `E : ℕ → (0,1]`.
- Assemble the outer loop using `afks_energy_iteration_count` as the certificate.

## Session 2026-07-08 (Session 3) - Witness → two-halves deviation bridge

**Mode**: REVISIT (continuing branch szem-oq04-knowledge-s3)
**Outcome**: progress (2 theorems VERIFIED 0/0, PR #35858)

### What I Did
- Identified the exact remaining gap: `exists_irregular_witness` produces a
  *subset-vs-whole* density deviation `|d(A',B)−d(A,B)|`, but the gain lemma
  `partitionEnergy_single_split_gain_uniform` consumes a *two-halves* gap
  `|d(A₁,B₀)−d(A₂,B₀)|`. These are different quantities.
- Proved `edgeDensity_split_deviation_ge`: witness-vs-whole ≤ two-halves,
  because `d(A₁∪A₂,B)` is the weighted average and the scale factor
  `|A₂|/(|A₁|+|A₂|) ≤ 1`. So the SAME ε transfers.
- Proved `partitionEnergy_subpair_split_gain_uniform`: composes the bridge with
  the uniform-gain step — a witness half deviating from the whole part's density
  against a fixed partner by ≥ ε realizes the ε²/(2n²) floor.

### Key Findings
- The bridge is a one-line weighted-average fact, but it is the precise link that
  makes an *actual* irregular pair (one-sided, partner preserved) drive the
  `hstep` hypothesis of `afks_energy_iteration_count`.
- `set c : ℚ := A.card` does NOT auto-insert the ℕ→ℚ coercion — write
  `set c : ℚ := (A.card : ℚ)`.
- `linear_combination` cleanly cancels the common `|B|` factor in
  `edgeDensity_union_mul`; `-hcancel` sign chosen from the polynomial identity.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (+edgeDensity_split_deviation_ge, +partitionEnergy_subpair_split_gain_uniform; 8→10 theorems)

### Next Steps
- Two-SIDED refinement: split B₀ too, derive the ε⁵ gain via defect (Gowers)
  Cauchy–Schwarz over the 4 cells — the genuine hard core (~200+ lines).
- Wire `exists_irregular_witness` end-to-end into the one-sided step, discharging
  the `|A'|,|A\A'| ≥ 1` side conditions.
- Assemble whole-partition (all parts refined) energy monotonicity feeding hstep.
