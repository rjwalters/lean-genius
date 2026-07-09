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

## Session 2026-07-08 (Session 4) - ¬IsEpsilonRegular → one-sided deviation → A-side energy jump

**Mode**: REVISIT (continuing branch szem-oq04-knowledge-s3)
**Outcome**: progress (4 theorems VERIFIED 0/0)

### What I Did
- `exists_irregular_witness`: unfolds `¬ IsEpsilonRegular` via `push_neg` into an
  actual witness `(A',B')` with the size thresholds and strict deviation `>ε`.
  The named entry point every downstream docstring referenced but never defined.
- `edgeDensity_two_sided_le`: `abs_sub_le` triangle through the mixed density
  `d(A',B)`, splitting the two-sided witness deviation into a **B-side** term
  `|d(A',B')−d(A',B)|` and an **A-side** term `|d(A',B)−d(A,B)|`.
- `exists_onesided_deviation_of_irregular`: the structural reduction — from a
  witness deviation `>ε`, at least one of the two one-sided terms is `≥ε/2`
  (by-contra + `linarith` on the triangle bound). Turns two-sided irregularity
  into one-sided at a factor-½ tolerance cost.
- `partitionEnergy_Aside_gain_of_irregular`: closes the A-side branch fully —
  presenting `A = A' ∪ (A\A')` via `Finset.union_sdiff_of_subset` and feeding
  `partitionEnergy_subpair_split_gain_uniform`, an A-side deviation `≥ε/2`
  realizes the uniform floor `(ε/2)²/(2n²) = ε²/(8n²)`. **First end-to-end
  irregular-pair → concrete energy-increment link.**

### Key Findings
- The definitional witness is genuinely two-sided; the whole difficulty of
  connecting irregularity to energy is that the energy machinery only sees
  one-sided splits. The triangle-through-mixed-density trick is the clean bridge.
- The A-side branch closes because `A', A\A'` are honest sibling parts of the
  refined partition. The B-side branch needs a *second* refinement (split `B`
  against the fixed sub-part `A'`, which is not itself a part) — the ε⁵ defect
  Cauchy–Schwarz core, still ahead.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (+4 theorems, 388→~470 lines)

### Next Steps
- B-side branch via two-level refinement + 4-cell defect Cauchy–Schwarz.
- Outer AFKS loop assembly feeding `afks_energy_iteration_count`.
- Discharge `|A'|,|A\A'|≥1`, `∉R` side conditions from `|A'|≥ε|A|>0` + equipartition.

## Session 2026-07-08 (researcher-8) — B-side energy increment + split-gap⇒irregular converse

**Mode**: REVISIT (continuing own thread) · **Outcome**: progress (VERIFIED 0/0), branch research/szemeredi-oq04-bside-and-converse-r8

### What I Did
- Synced stale worktree to origin/main (was ~7 commits behind; #35858/#35862 had
  already wired the A-side irregularity→deviation→energy-jump chain end-to-end,
  incl. `partitionEnergy_Aside_gain_of_irregular`). Re-scoped to what was genuinely
  missing.
- `partitionEnergy_Bside_gain_of_irregular`: the symmetric mirror of the A-side
  end-to-end lemma. `partitionEnergy` sums over *ordered* pairs, so refinement is
  coordinate-agnostic — a witness sub-partner `B'⊆B` deviating from the whole
  partner `B`'s density against a fixed part `A₀∈R` (`|d(A₀,B')−d(A₀,B)|≥ε/2`)
  drives the uniform floor `ε²/(8n²)` when `B` splits into `B', B\B'`. Transport the
  deviation via `edgeDensity_comm` to partner-second orientation, feed
  `partitionEnergy_subpair_split_gain_uniform` with split part `B`, partner `A₀`.
- `edgeDensity_balanced_union_sub`: balanced (`|A₁|=|A₂|`) union density is the
  arithmetic mean of the halves, `d(A₁,B)−d(A₁∪A₂,B)=(d₁−d₂)/2`. Cancel `|B|` then
  `|A₁|` out of `edgeDensity_union_mul` (two `mul_left_cancel₀` + `linear_combination`).
- `split_gap_not_regular_balanced`: the CONVERSE of the energy machinery. A δ-gap
  between two equal-size halves against `B₀` forces `(A₁∪A₂,B₀)` to fail
  ε-regularity for `ε<δ/2`, `ε≤1/2` — witness `A₁` (half the union, deviation δ/2).

### Key Findings
- The two one-sided energy-increment branches (A-split, B-split) are the SAME
  lemma up to relabelling which part is pulled out of `R`; no fresh analysis.
- Energy-gain hypothesis ⟺ ε-irregularity, up to the constant 1/2 (both directions
  now formalized).
- **Honest crux for full closure**: the triangle reduction `edgeDensity_two_sided_le`
  always leaves one branch measuring deviation against a SUBSET partner (`A'` or
  `B'`), which the whole-partner increment lemmas cannot consume. A clean
  unconditional dichotomy [split-A vs whole-B₀] ∨ [split-B₀ vs whole-A] does NOT
  follow from the triangle; genuine closure needs the 2×2 defect-Cauchy–Schwarz
  increment (refining both coordinates at once).

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (+3 theorems: 15→18; PARTS VII, VIII)

### Next Steps
- Prove the 2×2 defect-Cauchy–Schwarz energy increment (both coordinates).
- State the two-level AFKS conclusion with dependent tolerance E:ℕ→(0,1].
- Assemble the outer loop using afks_energy_iteration_count (N≤2n²/ε²).

## Session 2026-07-08 (researcher-8) — two-level B-side closure + unified AFKS increment

**Mode**: REVISIT (continuing own thread) · **Outcome**: progress (VERIFIED 0/0), branch research/szemeredi-oq04-bside-and-converse-r8, PR #35902

### What I Did
- `partitionEnergy_Bside_gain_via_promotion` (PART IX): resolves the honest crux
  flagged the last two sessions — the B-side branch of
  `exists_onesided_deviation_of_irregular` hands a deviation
  `|d(A′,B′)−d(A′,B)|≥ε/2` measured against the witness **subset** `A′`, which is
  not a part, so the whole-partner increment cannot fire. Fix: split `A` into
  `A′, A\A′` first — by `partitionEnergy_single_split_mono` energy never
  decreases and `A′` becomes a genuine part — then the existing
  `partitionEnergy_Bside_gain_of_irregular` fires with `A₀=A′`, netting the full
  floor `ε²/(8n²)`. Two `Finset.insert_comm` rewrites make `B` the split part and
  `A′` a present partner so the two lemmas compose.
- `partitionEnergy_gain_of_irregular_pair` (PART X): unifies both one-sided
  branches. Given the dichotomy `hdich` (exactly what
  `exists_onesided_deviation_of_irregular` produces), returns `∃ P'` refined
  partition with `partitionEnergy (insert A (insert B R)) + ε²/(8n²) ≤ energy P'`.
  A-side → split `A` (Aside lemma, `B₀=B`); B-side → promote-then-split
  (PART IX). Existential because the two branches yield different refinements but
  clear the SAME floor.

### Key Findings
- The 2×2 defect Cauchy–Schwarz is NOT needed to close the B-side branch. The
  insert-model already has refinement-monotonicity, and promoting the witness
  subset to a part is free (energy non-decreasing), so the one-coordinate
  increment machinery suffices for BOTH coordinates via sequential refinement.
- The remaining honest gap is the full existential capstone straight from
  `¬IsEpsilonRegular`: freshness (`∉R`, distinctness) of the *internally chosen*
  witness `A′,B′` cannot be guaranteed by the insert-based single-part-split
  model. Two ways forward: work with the common refinement abstractly (no
  per-part `∉R` conditions), or thread freshness as hypotheses (as PARTS IX/X do).

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (+2 theorems: 17→19; PARTS IX, X)

### Next Steps
- Assemble the outer AFKS loop: feed `partitionEnergy_gain_of_irregular_pair` as
  the `hstep` of `afks_energy_iteration_count` to bound refinements by `2n²/ε²`.
- Full ∃-capstone from `¬IsEpsilonRegular` via the common refinement.
## Session 2026-07-08 (Session 5) - B-side energy increment (whole-partner mirror)

**Mode**: REVISIT (continuing branch szem-oq04-knowledge-s3)
**Outcome**: progress (1 theorem VERIFIED 0/0)

### What I Did
- `partitionEnergy_Bside_gain_of_irregular`: the exact second-coordinate mirror of
  `partitionEnergy_Aside_gain_of_irregular`. A witness sub-part `B' ⊆ B` whose
  density against a fixed WHOLE part `A₀ ∈ R` deviates from the whole part's
  density by `≥ ε/2` (`|d(A₀,B') − d(A₀,B)| ≥ ε/2`) realizes the uniform floor
  `ε²/(8n²)` when `B` is refined into `B', B∖B'`.
- Since `partitionEnergy_subpair_split_gain_uniform` splits the FIRST coordinate,
  the deviation is flipped onto it with `edgeDensity_comm` (2 rewrites) so `B`
  plays the `A₁∪A₂` role against partner `A₀`; then reuse the verified subpair
  lemma verbatim. ~30 lines.

### Key Findings
- **The two whole-partner one-sided branches are now both discharged**
  (A-side against whole B; B-side against whole A). This is the complete
  "refine the deviating coordinate against a genuine whole part" toolkit.
- **What still blocks full closure**: neither of the two single-triangle
  decompositions of the witness deviation `|d(A',B')−d(A,B)|` gives *both* legs
  against whole parts — each yields one whole-partner leg (GOOD) and one
  sub-part-partner leg (BAD):
    * through `d(A',B)`: A-leg `|d(A',B)−d(A,B)|` vs whole B (GOOD), B-leg
      `|d(A',B')−d(A',B)|` vs sub-part A' (BAD).
    * through `d(A,B')`: B-leg `|d(A,B')−d(A,B)|` vs whole A (GOOD), A-leg
      `|d(A',B')−d(A,B')|` vs sub-part B' (BAD).
  The obstruction is the mixed second difference (defect)
  `d(A',B')−d(A',B)−d(A,B')+d(A,B)`; killing it is exactly the 4-cell defect
  Cauchy–Schwarz. So full closure genuinely requires the simultaneous
  refinement of BOTH coordinates (4 cells) + a variance/second-moment bound
  `Σ wᵢ xᵢ² ≥ (Σwᵢ)μ² + w₀d²` — the hard analytic core, NOT reducible to
  triangle inequalities. Confirmed dead-end for the elementary route.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (+partitionEnergy_Bside_gain_of_irregular)

### Next Steps
- 4-cell simultaneous refinement: abstract variance atom bound
  `Σ wᵢ xᵢ² − (Σwᵢ)μ² ≥ w₀·d²` (one atom of weight ≥ w₀ deviating ≥ d from mean),
  then instantiate over the 4 sub-cells to get the true ε⁴ energy increment.
- Outer AFKS loop assembly feeding `afks_energy_iteration_count`.

## Session 2026-07-08 (Session 6, researcher-7) - Variance atom bound (the analytic core)

**Mode**: REVISIT (continuing branch szem-oq04-bside-s5)
**Outcome**: progress (2 theorems VERIFIED 0/0)

### What I Did
- `weighted_variance_identity` (Energy file): the Finset generalization of the
  two-cell `split_energy_identity`. For nonnegative weights `w` on a finite `s`,
  with weighted mean `μ = (Σ wⱼxⱼ)/(Σ wⱼ)`:
  `Σ wᵢ(xᵢ−μ)² = Σ wᵢxᵢ² − (Σ wᵢ)·μ²`. Sole hypothesis `Σ wᵢ ≠ 0`. Proof:
  termwise `sub_sq` expansion → three sub-sums via `Finset.mul_sum` +
  `sum_sub/add_distrib` → substitute `(Σw)·μ = Σwx` (`mul_div` cancel via
  `field_simp`) → `ring`.
- `variance_atom_bound` (Energy file): the analytic core session 5 flagged as the
  genuine blocker. If one cell `i₀` has weight `≥ w₀ ≥ 0` and value deviating from
  the mean by `≥ d ≥ 0`, then `Σ wᵢxᵢ² − (Σ wᵢ)μ² ≥ w₀·d²`. Proof: variance terms
  all nonneg → `Finset.single_le_sum` isolates the `i₀` term → `sq_le_sq'`/`sq_abs`
  give `(xᵢ₀−μ)² ≥ d²` → two `mul_le_mul` steps give `wᵢ₀(xᵢ₀−μ)² ≥ w₀d²` →
  `linarith` with the identity.

### Key Findings
- This is the **variance ≥ single-atom-contribution** fact that dodges the
  session-5 obstruction (the mixed second difference / defect that no single
  triangle inequality kills). Instead of decomposing the two-sided witness
  deviation through a mixed density, one refines BOTH coordinates simultaneously
  into cells and treats the density distribution as a weighted point set; the
  witness cell is a single atom whose deviation is bounded below, and its energy
  contribution alone is ≥ w₀d² by this bound. No triangle detour, no defect term.
- Abstract over an arbitrary index type `ι` (not tied to `V`), so it is reusable
  as a clean standalone weighted-variance lower bound.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Energy.lean (+weighted_variance_identity,
  +variance_atom_bound; +~90 lines)

### Next Steps
- Instantiate `variance_atom_bound` over the 4 (or general m×k) sub-cells of a
  simultaneous two-coordinate refinement: weights `|Aᵢ||Bⱼ|/n²`, values
  `d(Aᵢ,Bⱼ)`, mean `d(A,B)`, witness atom `(A',B')` with deviation `≥ ε/2` from
  the block average → energy gain `≥ (|A'||B'|/n²)·(ε/2)²`. This closes the
  genuine ε⁴ increment that the two whole-partner one-sided branches (S4/S5)
  could only approximate.
- Wire the resulting increment into `afks_energy_iteration_count`.

## Session 2026-07-08 (Session 7, researcher-7) - The 2×2 ε⁴ energy increment (closure of the increment core)

**Mode**: REVISIT (continuing branch szem-oq04-bside-s5)
**Outcome**: progress (5 theorems VERIFIED 0/0, capstone `pairEnergy_prod_refinement_gain`
built green on retry attempt 4 after a sustained fleet SIGBUS/SIGSEGV write window)

### What I Did
- `weighted_second_moment_atom_gain` (Energy file, VERIFIED): the directly
  consumable form of `variance_atom_bound`. Takes an *external* mean `μ` plus the
  *mean identity* `Σ wᵢxᵢ = (Σwᵢ)·μ` and concludes `(Σwᵢ)·μ² + w₀·d² ≤ Σ wᵢxᵢ²`.
  No internal division, no `(Σwx)/(Σw)`. Case-splits on `Σw = 0` (all weights
  vanish, both sides collapse to 0) vs `≠ 0` (μ is the honest mean, apply the
  atom bound). This is the exact shape the block-energy increment needs.
- `edge_count_union_right` + `edgeDensity_union_mul_right` (Energy file, VERIFIED):
  the second-coordinate mirrors of the existing A-side edge-count/weighted-average
  identities. (`edgeDensity_comm` is in OQ01, which the Energy file does not import,
  so the B-side split is proved directly from the raw product-filter, not via comm.)
- `edgeDensity_prod_split` (Energy file, VERIFIED): **the law of total density for
  a 2×2 refinement.** `|A||B|·d(A,B) = Σ_{i,j} |Aᵢ||Bⱼ|·d(Aᵢ,Bⱼ)` for `A=A₁∪A₂`,
  `B=B₁∪B₂` disjoint. Proved by one A-side split then a B-side split of each
  resulting term (`ring` closes the reassociation). This is precisely the *mean
  identity* the variance atom bound consumes — it certifies `d(A,B)` is the honest
  `|Aᵢ||Bⱼ|`-weighted centroid of the four sub-densities.
- `pairEnergy_prod_refinement_gain` (Energy file, VERIFIED): **the genuine
  ε⁴ energy increment.** Refining `(A,B)` simultaneously into the 2×2 grid raises
  the normalized energy by ≥ `(|A₁||B₁|/n²)·d²` whenever the corner cell's density
  deviates from `d(A,B)` by ≥ d. Assembled by instantiating
  `weighted_second_moment_atom_gain` over the 4-element index `Bool × Bool`
  (weights `|Pᵢ||Qⱼ|` unnormalized, densities `d(Pᵢ,Qⱼ)`, mean `d(A,B)`), with the
  mean identity discharged by `edgeDensity_prod_split` and the final `1/n²` scaling
  applied through `mul_le_mul_of_nonneg_left` + two `ring` identities.

### Key Findings
- **This closes the elementary-route obstruction of Sessions 4–5.** The witness
  deviation from an ε-irregular pair is `|d(A',B') − d(A,B)| > ε` *directly against
  the whole density* — which IS the coarse mean. So one does not need to decompose
  it through a mixed density (the S5 defect / second-difference that no triangle
  inequality kills). Refine BOTH coordinates at once; the witness cell A'×B' is a
  single variance atom of the 4-cell density distribution whose deviation from the
  centroid d(A,B) is bounded below, and `variance_atom_bound` converts that lone
  atom into a definite energy gain. No defect term, no Cauchy–Schwarz on the
  cross-terms. The variance-atom viewpoint (S6) was exactly the right dodge.
- With `|A₁| ≥ ε|A|`, `|B₁| ≥ ε|B|`, `|d(A₁,B₁)−d(A,B)| > ε`: weight
  `≥ ε²|A||B|`, deviation `> ε`, gain `≥ ε²·ε²·|A||B|/n² = ε⁴·|A||B|/n²`. The true
  ε⁴ increment the AFKS iteration consumes.
- `linear_combination` sign: expanding `Σ w·x` over `Bool × Bool` vs the
  `edgeDensity_prod_split` RHS needs coefficient **−1** (default +1 leaves a `2×`
  residual — the identity's orientation is `whole = Σcells`, opposite the goal).
- `Fintype.sum_prod_type` + `Fintype.sum_bool` cleanly expand a `Bool × Bool` sum
  to its four named terms; wrap in a local `expand` helper + `ring`.
- Final `/n²` scaling: do NOT `convert ... using 2` (descends into the `+` tree and
  mis-pairs one pairEnergy term with the whole scaled sum). Instead prove
  `goalLHS = 1/n²·(rawLHS)` and `goalRHS = 1/n²·(rawRHS)` as explicit `ring`
  identities (each `unfold pairEnergy; ring`), `rw` both, then `exact` the scaled
  inequality — bulletproof against association mismatch.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Energy.lean
  (+weighted_second_moment_atom_gain, +edge_count_union_right,
   +edgeDensity_union_mul_right, +edgeDensity_prod_split,
   +pairEnergy_prod_refinement_gain; +~150 lines)

### Build note
- The capstone repeatedly reached `[7745/7745] Building … (1.1s)` with **zero
  elaboration errors** (only pre-existing unused-section-variable linter warnings)
  and then exited 135/139 at the olean-write stage — the fleet-memory write
  corruption, not a math error. Attempts 1–3 of a bounded retry-loop crashed at the
  write; **attempt 4 landed clean exit-0** (`Build completed successfully (7745
  jobs)`), confirming the whole file VERIFIED (0 sorry, 0 axiom). Lesson: a
  `[N/N] … (1.1s)` line with zero type errors followed by 135/139 is purely a write
  race — keep retrying, do NOT touch the proof.

### Next Steps
- Generalize the 2×2 grid to an m×k product refinement (`Finset (Finset V)` families
  + `card_biUnion` disjoint + `edge_count` over a product partition via
  `Finset.biUnion`); the abstract atom gain already covers arbitrary finite index.
- Wire `pairEnergy_prod_refinement_gain` + `exists_irregular_witness` (Bridge) into
  the whole-partition energy monotonicity feeding `afks_energy_iteration_count`.
