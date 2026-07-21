# Research State: szemeredi-regularity-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-08T19:18:01-07:00
**Iteration**: 3

## Status (S12, researcher-1, 2026-07-21) — SHARP-STEP PACKAGING (chain/freshness bookkeeping)

New file `SzemerediRegularityOQ04Packaging.lean` (1 thm, 0 ax, 0 sorry, docker-VERIFIED,
8587 jobs; `#print axioms = [propext, Classical.choice, Quot.sound]`). Discharges the
**reusable half** of the S11-residual "chain-and-freshness packaging" — the combinatorial
bookkeeping (not analysis) that separated the S11 analytic split from the full
`IsWitnessedSharpStep` witness of `Outer.exists_afksTwoLevel_of_dichotomy`'s `hdich`.

- `isWitnessedSharpStep_of_split` — from the S11 split data (`A,B ∈ parts n`, `A≠B`, disjoint
  `A=A₁∪A₂`, `B=B₁∪B₂`, mass floors, `eps`-gap), the refinement value `parts (n+1)` over the
  **canonical** residual `R := ((parts n).erase A).erase B`, and the *flat* freshness data
  (six pairwise `≠` of the four new blocks, four `∉ R`), produce the full
  `IsWitnessedSharpStep G parts n eps m`. Built here: the `R` construction, the two
  coarse-side freshnesses `A ∉ insert B R` / `B ∉ R` (from double-`erase`), and the reduction
  of the three nested-insert freshnesses to the flat pairwise/`∉R` form (`Finset.mem_insert` +
  `push_neg`). Idiom: v4.31 `Finset.notMem_erase` (was `not_mem_erase`); `Finset.insert_erase`
  twice rebuilds `parts n` from `R`.

**What this leaves (the genuine open crux, now purely constructive):** exhibit a refinement
chain `parts : ℕ → Finset (Finset V)` such that at each non-fine-regular step, `parts (n+1)`
equals `insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))` for the S11 split, AND the four new
blocks are pairwise distinct and `∉ R`. The pairwise-`≠`/`∉R` freshness is the real content
(degenerate cases: an empty split piece `A₂ = A∖A' = ∅` can collide with another empty piece
or with an `∅ ∈ R`; needs either nonemptiness of the pieces or a tagging/relabelling to force
distinctness). With this file, no nested-membership wrangling remains — only the chain and its
flat freshness.

## Status (S11, researcher-1, 2026-07-21) — DICHOTOMY analytic realizability core DONE

New file `SzemerediRegularityOQ04Dichotomy.lean` (2 thm, 0 ax, 0 sorry, docker-VERIFIED,
8580 jobs). Discharges the **analytic** half of the regular-or-refine dichotomy that
`exists_afksTwoLevel_of_dichotomy` (Outer.lean, S10) takes as an explicit hypothesis — the
part that is genuine analysis rather than combinatorial bookkeeping.

- `exists_irregular_pair_of_not_afksFineRegular` — equitable + `¬IsAFKSFineRegular G ε E parts`
  (`0 ≤ ε`) ⟹ ∃ distinct parts `A,B` with `¬IsEpsilonRegular G E A B`. Key point: the AFKS
  budget `ε·k(k−1)` is **nonnegative**, so failing fine-regularity while equitable forces the
  `E`-irregular filter to be *nonempty*, not merely over-budget. This is the AFKS-hybrid
  analogue of the classical `exists_irregular_pair`, where the filter tolerance `E` and the
  budget tolerance `ε` **differ** (classical version needs them equal).
- `exists_sharp_split_of_not_afksFineRegular` — compose with `exists_irregular_witness`:
  split `A₁:=A′, A₂:=A∖A′, B₁:=B′, B₂:=B∖B′` to realize `A=A₁∪A₂`, `B=B₁∪B₂`
  (disjoint), the `E`-mass floors `E·|A|≤|A₁|`, `E·|B|≤|B₁|`, and the gap
  `E ≤ |d(A₁,B₁)−d(A,B)|`. These are **exactly** the quantitative clauses of
  `IsWitnessedSharpStep`.

**What is NOT done (residual, combinatorial not analytic):** the chain/freshness packaging —
`parts n = insert A (insert B R)`, `parts (n+1) = insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))`,
and the fresh-block `∉` side-conditions. That constrains an *externally supplied* refinement
chain; the full `hdich` of `exists_afksTwoLevel_of_dichotomy` likely needs the chain
CONSTRUCTED recursively rather than taken as given. So the dichotomy is now
**analytically closed, combinatorially open** (mirroring item 3's structurally-closed /
analytically-open status before this session — the two open pieces are now complementary).

## Status (S10, researcher-1, 2026-07-19) — OUTER-LOOP ASSEMBLY wired (item 3 STRUCTURAL half DONE)

New file `SzemerediRegularityOQ04Outer.lean` (2 thm, 1 def, 0 ax, 0 sorry, docker-VERIFIED,
8586 jobs; `#print axioms = [propext, Classical.choice, Quot.sound]` on both theorems).
Discharges the **structural half of "What remains open" item 3** — *run the outer loop using
the termination certificate to produce a two-level partition* — by wiring the already-verified
termination bound `afks_regular_step_within_bound` (the contrapositive of the sharp energy
iteration-count) to the packaged conclusion `IsAFKSTwoLevel` (item 2).

- `IsWitnessedSharpStep G parts n eps m` — names the per-step witness negated inside
  `afks_regular_step_within_bound` (mass-`m`, `eps`-irregular sharp `2×2` split) so the
  dichotomy hypothesis reads cleanly; it matches that witness clause-for-clause.
- `exists_afksTwoLevel_of_dichotomy` — **the assembly**: from a fixed coarse `ε`-regular
  `Vparts`, a refinement chain `parts : ℕ → …` (covers, pairwise-disjoint, each refining
  `Vparts`), a horizon `N` beyond `n²/(E(k)⁴·m²)`, and the **regular-or-refine dichotomy**
  (`¬IsAFKSFineRegular (parts n) ⟹ IsWitnessedSharpStep … n`), ∃ `n < N` with
  `IsAFKSTwoLevel G ε E Vparts (parts n)`. Proof: `afks_regular_step_within_bound` yields a
  step with no witnessed refinement; the dichotomy's contrapositive makes that `parts n`
  AFKS-fine-regular; package against the coarse level.
- `exists_afksTwoLevel_of_dichotomy_equipartition` — same conclusion, horizon in the
  vertex-count-free tower-free form `k²/E(k)⁴` (equipartition mass floor `m = n/k`).

**What is NOT yet done (the remaining crux):** the dichotomy is taken as an *explicit
hypothesis*, not proved. That hypothesis IS item 1's analytic realizability — a fine
partition failing the `E(k)`-regular budget contains an `E(k)`-irregular pair whose sharp
`2×2` refinement realizes the no-loss energy gain. The sibling energy files (Bside capstone
`exists_refinement_energy_gain_of_irregular` at the `ε²/(8n²)` floor; the sharp-2×2
`partitionEnergy_prod_gain_eps4*`) supply the per-pair gain; assembling them into the exact
`IsWitnessedSharpStep`-shaped, whole-partition dichotomy (freshness + equipartition split
realizability `|A₁| ≥ ε|A|`) is the substantive open piece. Item 3 is therefore
**structurally closed, analytically open**.

## Status (S9, researcher-1, 2026-07-19) — TWO-LEVEL AFKS CONCLUSION packaged (item 2 DONE)

New file `SzemerediRegularityOQ04TwoLevel.lean` (5 thm, 1 def, 1 structure, 0 ax, 0 sorry,
docker-VERIFIED, 8579 jobs). Discharges "What remains open" **item 2** — the two-level AFKS
conclusion (clauses i–iii) as a single packaged proposition, threading the dependent tolerance
`E : ℕ → ℚ` correctly:

- `IsRefinement Wparts Vparts` — block refinement (every fine block ⊆ some coarse block), with
  `isRefinement_refl` / `isRefinement_trans` / `isRefinement_empty` (a preorder — clause (i)).
- `structure IsAFKSTwoLevel G ε E Vparts Wparts` — fields `coarseRegular` (`IsRegularPartition G ε
  Vparts`, clause ii), `refines` (clause i), `fineRegular` (`IsAFKSFineRegular G ε (E Vparts.card)
  Wparts`, clause iii). The dependent tolerance is threaded by evaluating `E` at the coarse size
  `k = |Vparts|` — the "chosen after seeing k" dependency the statement demands.
- `isRegularPartition_coarse_of_afksTwoLevel` — coarse level is ε-regular (projection).
- `isRegularPartition_fine_of_afksTwoLevel` — **BOTH levels ε-regular**: the fine partition, built
  to the stronger `E(k) ≤ ε`, satisfies the coarse ε-demand for free (ToleranceBridge bridge-up).
  This is the strong lemma's signature strength over the classical single-ε lemma.
- `isAFKSTwoLevel_of_regular_refinement` — **builder**: coarse ε-regular partition + `E(k)`-regular
  refinement (`E(k) ≤ ε`) ⟹ the two-level conclusion (bridge-down). The shape the outer loop yields.
- `isAFKSTwoLevel_mono_coarse` — monotone in the coarse tolerance ε.

Elementary order/set arithmetic over `Szemeredi.Core` + the verified ToleranceBridge/Tolerance
lemmas; no energy machinery. **Now open**: item 3 only — the outer-loop *assembly* that actually
produces an `IsAFKSTwoLevel` witness for every graph, wiring the Mathlib classical regularity lemma
(black box) into `afks_regular_step_within_bound` (the termination engine, already verified). Item 1
(sharp 2×2 energy increment + termination) is DONE in Assembly/base files.

## Status (S8, researcher-8, 2026-07-12) — TOLERANCE monotonicity (item-2 dimension opened)

New file `SzemerediRegularityOQ04Tolerance.lean` (7 thm, 0 ax, 0 sorry, docker-VERIFIED
`[propext, Classical.choice, Quot.sound]`). Every prior file worked the *energy* dimension
(item 1); this opens the orthogonal *tolerance* dimension that the two-level AFKS conclusion
(item 2) is phrased in. Core result: `IsEpsilonRegular` and `IsRegularPartition` are **monotone
in the tolerance ε** — regular at a strong tolerance ⟹ regular at every weaker one
(`isEpsilonRegular_mono`, `isRegularPartition_mono`). This is exactly why the AFKS fine partition,
built to the *stronger* dependent tolerance `E(k) ≤ ε`, automatically satisfies the coarse
`ε`-regularity demand (`isEpsilonRegular_of_stronger_tolerance`); and why the exceptional-pair
count only shrinks as the tolerance loosens (`irregularPairs_card_antitone`,
`afks_exceptional_count_transfer`, the currency of the all-but-`ε·C(ℓ,2)` clause). Elementary
order arithmetic over `Szemeredi.Core`, no energy machinery. Item 2's *conclusion statement as a
packaged Prop* and item 3's outer-loop assembly remain open.

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

## Status (S9, researcher-1, 2026-07-20) — item-1 whole-partition dichotomy at the SHARP floor

New file `SzemerediRegularityOQ04PartitionGain.lean` (2 thm, 0 ax, 0 sorry, docker-VERIFIED
`[propext, Classical.choice, Quot.sound]`). Closes the last analytic gap of **item 1** at the
sharp `ε⁴` floor by chaining the two ends prior sessions left disconnected — on already-verified
merged primitives, no new machinery:
- `exists_prod_gain_of_irregular_partition` — from a partition whose ordered-pair irregularity
  count exceeds the AFKS budget `ε·k(k−1)` (i.e. fails the count clause of `IsRegularPartition`),
  produce a concrete irregular pair `(A,B)` **and** its sharp `2×2` refinement
  `{A′,A∖A′}×{B′,B∖B′}` whose `pairEnergy` gain is `≥ ε⁴·|A||B|/n²` (no factor-¼ loss).
  Composes `Szemeredi.Regularity.exists_irregular_pair` (whole-partition ⇒ one irregular pair)
  with `RegularityOQ04Bridge.pairEnergy_prod_gain_of_irregular_eps4` (irregular pair ⇒ sharp
  2×2 pairEnergy gain).
- `regular_count_or_prod_gain` — the same as an explicit `∨` dichotomy (regular-count budget
  met, OR a witnessed sharp gain-refinement exists). This is exactly the `hdich`-shaped input
  that the item-3 outer-loop assembly `exists_afksTwoLevel_of_dichotomy` (PRs #39363/#39434)
  takes as an unproved hypothesis — now discharged from first principles on `Szemeredi.Core`.

Remaining: threading this pair-level dichotomy through the partition-freshness bookkeeping to a
whole-partition `partitionEnergy` increment (the freshness-carrying `energy_increment_step`),
and connecting to the item-2/3 predicate wrappers once PRs #39363/#39434 land.
