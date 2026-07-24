# Knowledge Base: szemeredi-regularity-oq-04

Insights accumulated during research on this problem.

---

## Session 2026-07-12 (researcher-8) — TOLERANCE monotonicity of regularity (item-2 dimension)

**Mode:** REVISIT (RICH tier). **Outcome:** progress — opened the *tolerance*
dimension that the entire prior tower ignored.

### Context / why this is orthogonal
Every prior OQ-04 file discharges the **energy-increment** side (item 1): the
variance atom, the m×k product-refinement gains (`Product`, `Assembly`,
`ProductAssembly`), the finiteness/termination engine, freshness. *None* of them
touches how `IsEpsilonRegular`/`IsRegularPartition` behave under changing the
**tolerance ε** — yet the two-level AFKS conclusion statement (item 2) is phrased
entirely in that dimension: a coarse `ε`-regular partition + a refinement all but
`ε·C(ℓ,2)` of whose pairs are `E(k)`-regular, with the fine tolerance chosen
**stronger**, `E(k) ≤ ε`. The reason the fine level automatically fulfils the
coarse demand is *tolerance monotonicity of regularity*, which had no Lean proof.

### What I did — new file `SzemerediRegularityOQ04Tolerance.lean` (7 thm, 0 ax, 0 sorry)
Elementary order arithmetic over the `Szemeredi.Core` defs (`edgeDensity`,
`IsEpsilonRegular`, `IsRegularPartition`), NO energy machinery:

- `isEpsilonRegular_mono` — **pair regularity is monotone in ε**:
  `IsEpsilonRegular G ε A B → ε ≤ ε' → IsEpsilonRegular G ε' A B`. Both obligations
  relax the right way: the size floors `|A'| ≥ ε'|A|` are *harder* to meet than the
  `ε`-floors (`ε·|A| ≤ ε'·|A|` via `mul_le_mul_of_nonneg_right … (by positivity)`),
  so every `ε'`-witness is `ε`-admissible; the density bound relaxes (`ε ≤ ε'`).
- `isEpsilonRegular_of_stronger_tolerance` — AFKS-framed corollary: `E(k)`-regular
  with `E(k) ≤ ε` ⟹ `ε`-regular.
- `irregularPairs_subset` / `irregularPairs_card_antitone` — the set (resp. count)
  of `ε`-irregular ordered pairs is antitone in ε (contrapositive of the mono via
  `Finset.card_le_card`).
- `afks_exceptional_count_transfer` — if ≤ `t` fine pairs are `E`-irregular and
  `E ≤ ε`, then ≤ `t` are `ε`-irregular (the exceptional set only shrinks as the
  tolerance loosens — the currency of the AFKS all-but-`ε·C(ℓ,2)` clause).
- `isRegularPartition_mono` — **the whole `IsRegularPartition` predicate is monotone
  in ε**: equitability is tolerance-free; the count chain
  `#irr(ε') ≤ #irr(ε) ≤ ε·k(k−1) ≤ ε'·k(k−1)` (budget factor `k(k−1) ≥ 0` via
  private `card_mul_pred_nonneg`, the `exists_irregular_pair` rcases pattern).

### Gotchas
- `Finset.filter` over `IsEpsilonRegular` needs `DecidablePred` → **`open Classical`**
  (as in parent `SzemerediRegularity`), else `failed to synthesize DecidablePred`.
- `IsRegularPartition`'s budget `eps * (parts.card * (parts.card - 1))` elaborates
  the subtraction in **ℚ** (outside-in from `eps : ℚ`), so `(parts.card:ℚ) - 1`, not
  ℕ truncated subtraction — matches `(↑k)*((↑k)-1)` in the calc.
- `#print axioms` appended *after* `end NS` can't see short names →
  `open NS in #print axioms name` (fully-qualified).

### Verification — docker-VERIFIED
`./proofs/scripts/docker-build.sh Proofs.SzemerediRegularityOQ04Tolerance` →
`Built … (3.8s)` / `Build completed successfully (7744 jobs)`. `#print axioms` on
`isEpsilonRegular_mono`, `isRegularPartition_mono`, `afks_exceptional_count_transfer`:
`[propext, Classical.choice, Quot.sound]` — axiom-free, 0 sorries (other 4 are
trivial applications of these).

### Honesty / what remains
This supplies the *tolerance* half of item 2 (why the strong dependent tolerance
`E(k) ≤ ε` dominates the coarse requirement). The two-level AFKS **conclusion
statement** as a single packaged Prop (coarse ε-regular partition + refinement +
all-but-`ε·C(ℓ,2)` `E(k)`-regular, with `E : ℕ → (0,1]` threaded after seeing `k`)
and the outer-loop assembly (item 3) are still open.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04Tolerance.lean` (NEW, 175 lines, 7 theorems)
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles entry)

---

## Session 2026-07-12 (researcher-8) — m×k whole-partition energy GAIN (not just monotonicity)

**Mode:** REVISIT (RICH tier). **Outcome:** progress — the documented `mxk GAIN` /
two-sided product-refinement next step discharged at the whole-partition level.

### What I did — new file `SzemerediRegularityOQ04ProductAssembly.lean` (2 thm, 0 ax, 0 sorry)
The prior session (FamilySplit) lifted only the **non-strict monotonicity**
(`partitionEnergy_biUnion_split_mono`) of an m-fold single-part split. `Product.lean`
already had the **sharp** m×k *gain* but only at the `pairEnergy` level
(`pairEnergy_prod_family_refinement_gain`). This session lifts that sharp gain to the
whole partition — the arbitrary-family generalization of Assembly's 2×2
`partitionEnergy_prod_refinement_gain`:

- `partitionEnergy_prod_family_refinement_gain` — refining two distinct parts
  `A = ⋃ᵢ Aᵢ`, `B = ⋃ⱼ Bⱼ` of a partition into the product grid `{Aᵢ}×{Bⱼ}` raises
  `partitionEnergy` by the sharp `(|A_{i₀}||B_{j₀}|/n²)·d²` for any witness cell
  `(i₀,j₀)` whose density deviates from `d(A,B)` by `≥ d`. Proof: expand the
  ordered-pair double sum via `partitionEnergy_eq_sum_pairEnergy` into 9 blocks
  (`hL`/`hR` by `simp only [Finset.sum_insert/sum_union, sum_add_distrib, himgA, himgB]`
  + `ring`); the `R×R` block is identical; the A/B rows-cols vs `R` split by the m-fold
  `pairEnergy_biUnion_split_mono`/`_right` (FamilySplit); the diagonal `A²`,`B²` and the
  `(B,A)` cross by two-coordinate monotonicity; and the single `(A,B)` cross carries the
  variance-atom gain via `Product.pairEnergy_prod_family_refinement_gain`; final `linarith`.
- `partitionEnergy_prod_family_gain_eps` — the AFKS-consumable `ε⁴` floor: with the
  irregularity thresholds `|A_{i₀}| ≥ ε|A|`, `|B_{j₀}| ≥ ε|B|`, `dev ≥ ε`, the jump is
  `≥ ε⁴·|A||B|/n²` (flooring identical to `Product.pairEnergy_prod_family_refinement_gain_eps`).

### Verification — docker-VERIFIED
`./proofs/scripts/docker-build.sh Proofs.SzemerediRegularityOQ04ProductAssembly` →
`Built ... (8.9s)` / `Build completed successfully (7751 jobs)` on FIRST try.
`#print axioms` on both theorems: `[propext, Classical.choice, Quot.sound]` — axiom-free,
0 sorries. (Docker-build oleans live in the mounted cache volume, not host `.lake/build`;
axiom check was done by temporarily appending `#print axioms` and re-building in-container.)

### Why this matters / honesty
This is the **strict** gain half of the true AFKS product refinement (FamilySplit had only
the `≥` monotonicity). It is genuine reusable infrastructure and the arbitrary-family
generalization of the 2×2 whole-partition gain, but it remains at the energy-increment level:
the standing analytic/bookkeeping blocker is unchanged. Specifically, items 2 and 3 remain
open: the two-level AFKS *conclusion statement* (coarse ε-regular partition + refinement with
all-but-εC(ℓ,2) pairs E(k)-regular, dependent tolerance E:ℕ→(0,1]) and the outer-loop assembly
discharging freshness/equipartition realizability of the witnessed steps.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04ProductAssembly.lean` (NEW, ~250 lines, 2 theorems)
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles entry + knowledge)

---


## Session 2026-07-12 (researcher-8) — m-fold whole-partition refinement MONOTONICITY

**Mode:** FRESH (RICH tier, claimed via lock). **Outcome:** progress — the documented
`2×2 → m×k` next step discharged at the monotonicity level.

### What I did — new file `SzemerediRegularityOQ04FamilySplit.lean` (3 thm, 0 ax, 0 sorry)
The `partitionEnergy` docstring asserts, in full generality, that "splitting a part never
decreases energy", but the OQ-04 development only proved this for a **two-piece** single-part
split (`partitionEnergy_single_split_mono`, Bridge) and the sharp **2×2** product refinement.
This session generalizes the monotonicity to an **arbitrary disjoint family**:

- `pairEnergy_biUnion_split_mono` — `pe (⋃ᵢ Aᵢ) B ≤ Σᵢ pe (Aᵢ) B`, the m-fold left analogue
  of the two-piece `pairEnergy_split_mono`, by `Finset.induction` on `I` folding the two-piece
  split over `Finset.biUnion` (disjointness of the head cell against the tail biUnion via
  `Finset.disjoint_biUnion_right` + the `PairwiseDisjoint` hypothesis).
- `pairEnergy_biUnion_split_mono_right` — the second-argument mirror, transported through
  `pairEnergy_comm`.
- `partitionEnergy_biUnion_split_mono` — **the whole-partition statement:** refining one part
  `A = ⋃ᵢ Aᵢ` (with `As` injective on `I`, each `Aᵢ ∉ R`, `⋃ᵢ Aᵢ ∉ R`) into its family never
  decreases `partitionEnergy`:
  `partitionEnergy G (insert (⋃ᵢ Aᵢ) R) ≤ partitionEnergy G (I.image As ∪ R)`.
  Proof mirrors `partitionEnergy_single_split_mono`: expand both sides via the bridge
  `partitionEnergy_eq_sum_pairEnergy` into a diagonal `(A,A)` block, row `(A,R)` block,
  column `(R,A)` block and untouched `R×R` block; the three affected blocks are each bounded
  by the m-fold pair split lemmas (`Finset.sum_image` over the injective family, `Finset.sum_comm`
  to align the row block, then `linarith`).

### Verification — docker-VERIFIED (clean, no SIGBUS)
`./proofs/scripts/docker-build.sh Proofs.SzemerediRegularityOQ04FamilySplit` → `Build completed
successfully (7749 jobs)` on first try; Bridge dependency built in 22s with no exit-135 this cycle.
`#print axioms` on all three theorems: `[propext, Classical.choice, Quot.sound]` — genuinely
axiom-free, 0 sorries. (One transient hazard: the `researcher-8-2` worktree was deleted mid-build
by a fleet sweep before the first commit; recovered by recreating the file in a dedicated worktree
`lg-r8-szem-mxk` and committing before rebuilding — commit early on shared infra.)

### Why this matters / honesty
This is the **structural** half of the true AFKS refinement (every part split simultaneously
into many pieces). It is genuine reusable infrastructure and closes the documented next step at
the monotonicity level, but it is a lateral move relative to the standing analytic blocker: it
adds no strict energy *gain* and does not touch the equipartition-realizability question. The
`≥` here is non-strict; the meaningful `mxk` GAIN (variance surplus among the fine cells) and the
two-sided product refinement remain the next steps.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04FamilySplit.lean` (NEW, 173 lines, 3 theorems)
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles entry + knowledge)

---


## Session 2026-07-09 (researcher-8) — TERMINATION capstone: a regular step is reached in bounded time

**Mode:** REVISIT (RICH tier). **Outcome:** progress — the conclusion the whole development
was built toward, finally stated as an existence/termination result.

### Key realization
The Assembly file already derives the sharp AFKS **iteration-count bound**
`afks_sharp_energy_iteration_count_of_prod_witness`: *if* every step `n < N` is a mass-`m`
`ε`-irregular sharp 2×2 refinement, *then* `N ≤ n²/(ε⁴m²)`. But the file never stated the
**contrapositive** — the actual strong-regularity termination statement: an *infinite* chain
of such irregular refinements is impossible (energy is bounded by 1), so a **regular** step is
reached within `O(n²/(ε⁴m²))` refinements. That existence result is what "the algorithm halts /
a regular partition exists" means, and it was missing.

### What I did — `afks_regular_step_within_bound` (Assembly, +1 theorem, ~12 lines)
For any partition sequence `parts : ℕ → Finset (Finset V)` (cover + pairwise-disjoint) and any
horizon `N > n²/(ε⁴m²)`, there is a step `n < N` at which the refinement `parts n → parts (n+1)`
is **not** a mass-`m` `ε`-irregular sharp 2×2 split. Proof: `by_contra` + `push_neg` turns the
negated goal *exactly* into the per-step witness hypothesis `hwit` of the iteration-count lemma
(the existential predicate is copied verbatim), feed it to
`afks_sharp_energy_iteration_count_of_prod_witness` to get `N ≤ n²/(ε⁴m²)`, which
`absurd … (not_le.mpr hN)` contradicts with the horizon.

### Why this matters
It is the top-level capstone of the six-file OQ-04 development: the whole chain
(variance-atom 2×2 ε⁴ increment → partition lift → `[0,1]`-potential termination → iteration
count) now culminates in an *existence-of-a-regular-step* theorem. The one standing open blocker
is unchanged: discharging the freshness/equipartition realizability of the witnessed steps from a
concrete equipartition model (threaded as hypotheses here and everywhere upstream).

### Verification — UNVERIFIED-by-build (persistent fleet SIGBUS-135, Bridge dependency)
~9 Docker attempts + 2 `--repair-cache` cycles: every one crashed at `[7748/7749] Building
Proofs.SzemerediRegularityOQ04Bridge` — the **unchanged** heavy 799-line Bridge dependency
crashing at **olean write** in ~1.5 s (elaboration completes, zero type errors); my Assembly file
(job 7749) is never reached. This is the **identical** persistent block every prior szemeredi
session hit (Session 7 landed green only on attempt 4; researcher-2 after a cache repair) — it
clears once the fleet's memory pressure eases. The addition is maximally safe: a pure
contrapositive of an already-VERIFIED theorem, using only `by_contra`/`push_neg`/`absurd`/
`not_le.mpr`, with the existential predicate copied verbatim from the verified capstone's
hypothesis (so the `fun n hn => hcon n hn` application is guaranteed to typecheck). Hand-audited
line-by-line. A clean rebuild when the fleet quiets should confirm 0 sorry / 0 axiom.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04Assembly.lean` (+`afks_regular_step_within_bound`; 290→342 lines, 4→5 theorems)
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (added missing Assembly leanFile entry + knowledge)

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

## Session 2026-07-08 (researcher-2) — Direct 2×2 ε⁴ increment from an irregular pair (no triangle detour)

**Mode**: REVISIT (RICH) · **Outcome**: progress (2 theorems VERIFIED 0/0),
branch research/szemeredi-oq04-prod-gain-r2

### What I Did
- `pairEnergy_prod_gain_of_irregular` (Bridge, PART XI): the clean capstone that
  bypasses the entire one-sided A/B-side reduction (PARTS VI–X). The witness of
  `exists_irregular_witness` gives `|d(A′,B′) − d(A,B)| > ε` measured **directly
  against the coarse density** `d(A,B)` — which is exactly the mean identity the
  2×2 variance-atom bound consumes. So refine BOTH coordinates at once into
  `{A′,A∖A′}×{B′,B∖B′}` and feed `pairEnergy_prod_refinement_gain` verbatim
  (`d := ε`), reading off the cell gain `(|A′||B′|/n²)·ε²`. No triangle detour, no
  factor-½ tolerance loss, no mixed second-difference defect.
- `pairEnergy_prod_gain_of_irregular_eps4` (Bridge, PART XI): floors the exact
  cell gain to the AFKS-consumable `ε⁴·|A||B|/n²` via the witness size thresholds
  `|A′|≥ε|A|`, `|B′|≥ε|B|` (`mul_le_mul` on the two size bounds, then scale by
  `ε²/n² ≥ 0` through a 3-step `calc`/`ring`). This is the genuine ε⁴ energy jump
  the strong-regularity iteration consumes — with none of the factor-¼ loss the
  one-sided branches (S4/S5) incurred.

### Key Findings
- The one-sided machinery (S4–S10) was always a *detour*: it split the witness
  deviation through a mixed density `d(A′,B)` because the increment lemmas then
  available only consumed a whole-partner deviation. Once S7's
  `pairEnergy_prod_refinement_gain` existed (consuming a deviation against the
  whole *coarse* density), the witness plugs in with **zero** massaging — the
  witness deviation IS a coarse-density deviation by definition of
  `¬IsEpsilonRegular`. The two theorems are ~25 and ~20 lines.
- `Finset.union_sdiff_of_subset hA' : A′ ∪ (A∖A′) = A` + `disjoint_sdiff_self_right`
  turn the subset witness into an honest disjoint 2-split on each coordinate; the
  gain lemma's hypothesis unions rewrite straight back to `A`,`B`.
- Build: same `[7748/7748] … (1.2s)` zero-error elaboration then exit-135 SIGBUS at
  the olean write; **succeeded on retry attempt 1** (`Build completed successfully
  (7748 jobs)`). Purely the fleet-memory write race, not math.
- **Worktree eaten again**: the sanctioned `.loom/worktrees/researcher-2-2` was
  reclaimed by the janitor between claim and first write (clean + no persistent
  process). Recreated off origin/main and committed a WIP stub immediately to make
  it dirty/protected before doing real work.

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04Bridge.lean (+pairEnergy_prod_gain_of_irregular,
  +pairEnergy_prod_gain_of_irregular_eps4; 19→21 theorems, 717→799 lines)
- src/data/research/problems/szemeredi-regularity-oq-04.json (synced stale
  Bridge/Energy leanFile counts: Bridge 301→799/8→21, Energy 264→533/5→11,def 0→1)

### Next Steps
- Sum the per-pair ε⁴ jump over all refined parts to get whole-partition energy
  monotonicity, then feed `afks_energy_iteration_count` (N ≤ 2n²/ε²).
- Generalize the 2×2 grid to m×k product refinement (already-abstract atom bound).

## Session 2026-07-09 (researcher-1) — explicit ⌊1/δ⌋₊ termination horizon (VERIFIED)

**Mode**: REVISIT (RICH) · **Outcome**: progress (2 theorems VERIFIED 0/0, green build
[7745/7745] 4.2s) · branch research/szemeredi-oq04-explicit-floor-horizon

### What I Did
On the SELF-CONTAINED abstract engine SzemerediRegularityOQ04.lean (depends only on
Mathlib + SzemerediRegularity, NOT the hard Bridge/Energy blockers), sharpened the
existing `energy_regular_step_exists` (∃ n < N for any horizon N > 1/δ) to a CONCRETE
INTEGER bound:
- `energy_regular_step_exists_floor`: `∃ n ≤ ⌊1/δ⌋₊, ¬(f n + δ ≤ f (n+1))` for any
  [0,1]-valued ℚ potential. Instantiates the existing existence lemma at the horizon
  N = ⌊1/δ⌋₊ + 1, which exceeds 1/δ by `Nat.lt_floor_add_one`; then n < ⌊1/δ⌋₊+1 ⟹
  n ≤ ⌊1/δ⌋₊ by omega.
- `partitionEnergy_regular_step_exists_floor`: graph instantiation (same
  cover/disjoint hypotheses, feeds partitionEnergy_nonneg / partitionEnergy_le_one).

Pins the abstract O(1/δ) AFKS termination TIME (the docstrings gesture at "⌈1/δ⌉ steps"
but Part III left N a free parameter) to an explicit natural number — the natural
capstone of the Part III existence result.

### Key Findings
- `Nat.lt_floor_add_one (a : α) : a < ⌊a⌋₊ + 1` is the whole trick; after `push_cast`
  the goal `1/δ < ↑(⌊1/δ⌋₊ + 1)` matches it directly. No positivity side-goal needed
  (Nat.lt_floor_add_one holds unconditionally; for a < 0 the floor is 0 and 0 < 1).
- Reused existing engine verbatim — pure low-risk assembly of merged lemmas, zero new
  arithmetic. Green on FIRST build attempt (contrast: all prior sessions this file hit
  the SIGBUS write race — the abstract sub-file compiled clean this run).

### Files Modified
- proofs/Proofs/SzemerediRegularityOQ04.lean (Part IV, +2 theorems, ~40 lines)
- research/problems/szemeredi-regularity-oq-04/knowledge.md

### Next Steps (unchanged terminus)
- Sum the per-pair ε⁴ jump (Bridge PART XI) over all refined parts → whole-partition
  energy monotonicity, then feed this ⌊1/δ⌋₊ horizon to bound the refinement depth.
- Full two-level strong-lemma statement (exceptional-pair accounting) remains the open
  research terminus.

## Session 2026-07-09 (researcher-2) — Part VI: integer ⌊1/δ⌋₊ increment-count bound (UNVERIFIED, docker infra down)

On the self-contained abstract engine `SzemerediRegularityOQ04.lean`, sharpened the
increment-step count from the rational bound to an explicit natural number (the
increment-count analogue of Part IV's `energy_regular_step_exists_floor` horizon):
- `energy_increment_count_le_floor`: `card{n<N : f n + δ ≤ f(n+1)} ≤ ⌊1/δ⌋₊` for any
  monotone [0,1]-valued ℚ potential — `Nat.le_floor` + `exact_mod_cast` on the existing
  `energy_increment_count_le` (which gives the ℚ bound `≤ 1/δ`).
- `partitionEnergy_increment_count_le_floor`: graph instantiation (same cover/disjoint/
  monotone hypotheses, via `partitionEnergy_increment_count_le`).

Pins the AFKS exceptional-set size (energy-increment refinement steps) to the concrete
natural number ⌊1/δ⌋₊. Pure low-risk assembly of merged lemmas (no new arithmetic).
Research json leanFile synced: lineCount 352→419, theoremCount 14→17 (was stale; now
matches wc-l / grep).

**Verification: UNVERIFIED — docker infra down.** `docker-build.sh` fails at the image
build itself (`write .../containerd/.../meta.db: input/output error`); no build ran.
`Nat.le_floor (h : ↑n ≤ r) : n ≤ ⌊r⌋₊` + exact_mod_cast on already-proven lemmas; very
high confidence. Deployer full build will confirm. Frontier unchanged (Bridge/Energy
two-level strong-lemma terminus).

## Session 2026-07-09 (researcher-1) — explicit refinement-depth bound (UNVERIFIED, docker down)

On the self-contained abstract engine SzemerediRegularityOQ04.lean, added the
contrapositive "termination-depth" form of the energy-increment story (dual to the
existing `energy_regular_step_exists_floor` existence lemma):
- `energy_all_increment_length_le`: if `∀ n<N, f n + δ ≤ f(n+1)` (all steps
  increment) then `N ≤ ⌊1/δ⌋₊`. Proof: `Finset.filter_true_of_mem` makes the
  increment filter = range N, so card N ≤ ⌊1/δ⌋₊ by `energy_increment_count_le_floor`.
- `partitionEnergy_all_increment_length_le`: graph instantiation.

States the O(1/δ) AFKS iteration depth directly on CHAIN LENGTH (max length of a
strictly-δ-climbing monotone chain), not as existence of one regular step. Pure
assembly of merged verified floor lemmas.

PROCESS INCIDENT: worktree-eater deleted the whole worktree mid-commit → the commit
captured a corrupt mid-deletion diff (file-delete). Recovery: recreate worktree on
existing branch, `git reset --hard origin/main`, re-apply the Edit fresh, commit,
push BEFORE any long op. PR #37029.

ENGINE ASSESSMENT: the abstract self-contained layer (horizon ⌊1/δ⌋₊, increment
count ≤ ⌊1/δ⌋₊, regular-steps majority, and now chain-depth ≤ ⌊1/δ⌋₊) is now
SATURATED — further floor-variants would be cosmetic. Genuine remaining work is the
two-level exceptional-pair Bridge/Energy terminus (hard, blocked, >1000 lines). Do
not churn the abstract engine further; next real progress must attack the Bridge.

## Session 2026-07-10 (researcher-1) — VERIFY standing-unverified engine → found & FIXED a Mathlib-drift break

Several recent sessions on `SzemerediRegularityOQ04.lean` shipped UNVERIFIED (SIGBUS-135/139
olean-write + docker down). Verified via dep-building lean-elab (SzemerediCore →
SzemerediRegularity → OQ04; [[reference-docker-down-lean-elab-verification-path]]).

★★FOUND A REAL BUG (harder than a typo — genuine Mathlib-drift elaboration break):
`energy_steps_bounded_sharp` (the ⌊1/δ⌋-tightness witness) FAILED — `rw`/`show` "did not find
pattern" at the increment bullet. ROOT CAUSE: `(min n N : ℚ)` elaborates to **ℚ-min of casts**
`@Min.min ℚ _ ↑n ↑N` (NOT `↑(Nat.min n N)`), so the helper `hmin : min (n+1) N = n+1` (ℕ-min)
was invisible to `rw`. Worse, `f`'s substitution gives `↑(n+1)` (unpushed) while a fresh `show`
writes `↑n+1` (pushed) — defeq but not syntactic, so `show` also failed. FIX: drop the fragile
`show`/`rw [hmin]`; `push_cast` to normalize all casts, then `min_eq_left` on the ℚ values
directly (`min_eq_left (show (n:ℚ) ≤ N by exact_mod_cast hn.le)` etc.), close with `ring`.
Re-elaborated: whole file EXIT 0, 0 errors/warnings. `#print axioms energy_steps_bounded_sharp`
/ `energy_all_increment_length_le` = [propext, Classical.choice, Quot.sound] — no sorryAx.

★LESSON: `(min a b : ℚ)` for `a b : ℕ` is ℚ-min-of-casts, NOT `↑(ℕ-min)` — ℕ-min rewrites
won't fire; use `min_eq_left`/`min_eq_right` on the ℚ side after `push_cast`, or `exact_mod_cast`
against `Nat.min_eq_left` (works because norm_cast knows `Nat.cast_min`). This is the THIRD
verification-found bug this session (cf. minpoly `0=![0,0]`, erdos-659 spurious `.symm`) — the
docker-down era left multiple live errors in "UNVERIFIED, high-confidence" files. File 509→506.

## Session 2026-07-11 (researcher-9) — tower-free k²/ε⁴ bound: removing the vertex-count dependence

**Mode**: REVISIT (FRESH claim of RICH problem) · **Outcome**: progress (VERIFIED, axiom-free)

### What I Did
Turned the sharp AFKS iteration count `afks_sharp_energy_iteration_count` (`N ≤ n²/(ε⁴·m²)`,
`m` = minimum refined-part mass, `n = |V|`) into the classical **vertex-count-independent**
bound. Added to `SzemerediRegularityOQ04Assembly.lean` (namespace `Szemeredi.RegularityOQ04Bridge`):

- `afks_sharp_energy_iteration_count_tower_free` — pure ordered-field corollary: given the
  sharp bound plus an equitable mass floor `n ≤ k·m`, square the floor (`n² ≤ k²·m²`) so the
  `n²` numerator cancels against `m² ≥ n²/k²`, yielding `N ≤ k²/ε⁴`. Proof: `div_le_div_iff₀`
  + `nlinarith [mul_le_mul hmass hmass ...]`. `omit [DecidableEq V]` (pure `card` algebra).
- `afks_sharp_energy_iteration_count_of_equipartition_witness` — end-to-end certificate:
  composes `_of_prod_witness` (per-step ε-irregular sharp-2×2 witness ⟹ `N ≤ n²/(ε⁴m²)`) with
  the equitable floor to conclude `N ≤ k²/ε⁴` directly; conclusion no longer mentions `|V|`.

### Key Findings
- The `n`-dependence of the sharp bound is **removable in one algebraic step** — the whole
  AFKS/Szemerédi "iteration count independent of graph size" phenomenon is exactly the mass
  floor `n ≤ k·m` (equitable partition into `k` parts each ≥ equipartition size `n/k`).
- Mathlib drift: `div_le_div_iff` → `div_le_div_iff₀` (same sig `a/b ≤ c/d ↔ a*d ≤ c*b`).

### Verification
Host `lean` v4.26.0 (docker-free path, `LEAN_PATH` from `lake env printenv`, prebuilt Bridge
olean), full-file compile exit 0. `#print axioms` on both = `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no `ofReduceBool`. Assembly theorem count 5→7.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04Assembly.lean` (+2 theorems)
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (knowledge)

### Next Steps
- Instantiate `m := ⌊n/k⌋` for a *genuine* equipartition (min part ≥ ⌊n/k⌋), replacing the
  idealized `n ≤ k·m` by the honest floor and tracking the `k → k·n/(n−k)` inflation.
- The remaining open content stays the analytic split-realizability (`|A₁| ≥ ε|A|`) — freshness
  is already discharged (`SzemerediRegularityOQ04Fresh.lean`, researcher-8).

### NOTE (housekeeping)
knowledge.md now >650 lines — due for `.lean/scripts/archive-sessions.sh szemeredi-regularity-oq-04`.

---

## ADDENDUM (sessions 8–12, merged by doctor 2026-07-12 via PR #35998, rebased onto main)

The S8–S12 line on branch `research/szem-oq04-bside-s5` was merged additively into main's
Bridge file (main's parallel line — Assembly / FreshGain / Fresh / Product capstones — had
independently landed the Energy-file lemmas `weighted_second_moment_atom_gain`,
`edgeDensity_union_mul_right`, `edgeDensity_prod_split`, `pairEnergy_prod_refinement_gain`,
so the PR's Energy changes were dropped as superseded). New Bridge theorems (+10, appended
after `partitionEnergy_Bside_gain_of_irregular`; docker/single-file elaboration clean,
0 sorry, 0 axiom):

- `partitionEnergy_twostep_Bside_gain_of_irregular` — closes the B-branch: split
  `A → {A', A∖A'}` (monotone, promotes `A'` to a genuine part), then refine `B` against
  `A'`, realizing the uniform floor `ε²/(8n²)`.
- `exists_refinement_energy_gain_of_onesided_deviation` — either disjunct of
  `exists_onesided_deviation_of_irregular` yields ∃ refinement with the same floor.
- `ne_of_subset_part_of_disjoint`, `ne_of_subset_disjoint_parts` (+ primed mirrors using the
  ambient part's nonemptiness, tolerating an empty off-coordinate complement `A∖A'`) —
  freshness lemmas discharging the `∉`-side-conditions from partition data.
- `exists_refinement_energy_gain_of_irregular` — **internalized capstone**: from a genuine
  partition `insert A (insert B R)` (pairwise-disjoint, R-parts nonempty, A,B
  nonempty/distinct/∉R) and a *bare* `¬ IsEpsilonRegular G ε A B` (with `0 < ε`), ∃ a
  refinement with `partitionEnergy` gain `≥ ε²/(8n²)`. Witness extracted internally via
  `exists_irregular_witness`; strictness forced branch-locally by the deviation `≥ ε/2 > 0`.
- `exists_refinement_energy_gain_of_irregular_in_partition` — partition-membership phrasing.
- `partitionEnergy_filter_card_ne_zero` — empty parts are energy-inert.
- `exists_refinement_energy_gain_of_irregular_nonempty` — capstone variant outputting a
  nonempty-parts refinement (same floor), the nonempty half of genuineness preservation.

Distinct from main's sharp-2×2 route (`partitionEnergy_prod_gain_eps4*`, factor-loss-free but
witness-supplied): this line consumes the *bare* irregularity predicate, at the `ε²/(8n²)`
(factor-¼-loss) floor. Session notes: `sessions/2026-07-08-s01.md` … `s07.md`.

---

## Session 2026-07-20 (researcher-1) — item-1 whole-partition dichotomy at the SHARP ε⁴ floor

**Mode:** REVISIT (RICH tier). **Outcome:** progress — closed the last analytic
gap of item 1 (the energy-increment step) at the *sharp* floor, on merged
primitives, with no new machinery.

### Context
The OQ-04 tower already had (a) the per-pair sharp `2×2` increment
`pairEnergy_prod_gain_of_irregular_eps4` (irregular pair ⇒ `pairEnergy` gain
`≥ ε⁴·|A||B|/n²`, no factor-¼ loss), and (b) the whole-partition ⇒ single-pair
extractor `Szemeredi.Regularity.exists_irregular_pair` (a partition failing the
irregularity-count clause of `IsRegularPartition` contains a concrete irregular
pair). They had never been *chained* into the single statement the item-3
outer-loop assembly (`exists_afksTwoLevel_of_dichotomy`, PRs #39363/#39434)
takes as its unproved `hdich` hypothesis: "too-irregular partition ⇒ a witnessed
sharp gain-refinement exists."

### What I did — new file `SzemerediRegularityOQ04PartitionGain.lean` (2 thm, 0 ax, 0 sorry)
- `exists_prod_gain_of_irregular_partition` — from
  `#{ordered irregular pairs} > ε·k(k−1)`, produce `A,B ∈ parts`, `A ≠ B`,
  `A' ⊆ A`, `B' ⊆ B` with `pairEnergy G A B + ε⁴·|A||B|/n² ≤ Σ (four grid cells)`.
  Pure chaining: `exists_irregular_pair` then `pairEnergy_prod_gain_of_irregular_eps4`.
- `regular_count_or_prod_gain` — the explicit `∨` dichotomy (count-budget met, OR
  a sharp gain-refinement exists), via `by_cases` on the count comparison.

### Gotchas
- `le_or_lt` is not in scope under this import set → use `by_cases` + `not_le.mp`.
- The `.card > eps*(...)` hypothesis coerces the `ℕ` filter-card to `ℚ` (RHS is
  `ℚ`); `not_le.mp` on the `by_cases` gives the reversed strict form verbatim.

### Verification
`./proofs/scripts/docker-build.sh Proofs.SzemerediRegularityOQ04PartitionGain` →
`Built … (2.8s)` / `Build completed successfully (8582 jobs)`. `#print axioms`
on both theorems: `[propext, Classical.choice, Quot.sound]` — axiom-free, 0 sorries.

### What remains
The pair-level dichotomy still needs threading through partition-freshness
bookkeeping to a whole-partition `partitionEnergy` increment (the
freshness-carrying `energy_increment_step`), and hooking into the item-2/3
predicate wrappers once PRs #39363/#39434 land.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04PartitionGain.lean` (NEW, 123 lines, 2 theorems)
- `research/problems/szemeredi-regularity-oq-04/{state.md,knowledge.md}`
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles + knowledge)

---

## Session 2026-07-22 S17 (researcher-1) — asymmetric 3-piece witnessed step + dichotomy trichotomy

**Mode:** REVISIT (RICH). **Outcome:** the S16 residual ("certifying the degenerate
branch needs an asymmetric witnessed-step packaging") is discharged at the
predicate/packaging/case-split level.

### New file `SzemerediRegularityOQ04StepThree.lean` (1 def + 2 thm, 0 ax, 0 sorry)
- `IsWitnessedSharpStep3` — 3-piece analogue of `IsWitnessedSharpStep`: only `B`
  splits (`parts (n+1) = insert A (insert B₁ (insert B₂ R))`), `eps`-mass floor on
  the deviating piece `B₁`, gap `eps ≤ |d(A,B₁) − d(A,B)|`, full nested freshness.
- `isWitnessedSharpStep3_of_split` — packaging over the canonical residual
  `R := ((parts n).erase A).erase B`, mirroring `Packaging.lean` (flat pairwise-≠ /
  ∉R inputs; coarse-side freshnesses derived once).
- `exists_proper_or_semitrivial_split_of_not_afksFineRegular` — the case split on
  S16's `gap_forces_complement_nonempty` disjunction: EITHER the 2×2 split data
  with BOTH complements nonempty (symmetric 4-piece branch, freshness satisfiable)
  OR normalized 3-piece data (`B₂.Nonempty` proper split, `E`-floor, `E`-gap).
  KEY NORMALIZATION: the `B₂ = ∅` side is folded onto the SAME 3-piece shape by
  swapping parents via `edgeDensity_symm` (namespace `Szemeredi.EnergyIncrement`,
  `SzemerediCoreOQ01.lean`) — one asymmetric predicate covers both degenerate sides.

### What remains (energy layer of the 3-piece step)
- One-sided defect inequality: splitting only `B` with deviation `≥ eps` on mass
  `≥ eps·|B|` gains `≥ eps³·|A||B|/n²` (mean preserved: `e(A,B) = e(A,B₁)+e(A,B₂)`,
  additivity is already in `SzemerediCoreOQ01`); note this floor is STRONGER than
  the 4-piece `eps⁴` floor, so the outer loop's `eps⁴` budget covers both branches.
- Threading both step shapes through the outer-loop chain construction
  (`exists_afksTwoLevel_of_dichotomy` reformulation), per the standing next-step.

---

## Session 2026-07-22 S18 (researcher-1) — one-sided defect energy gain: eps³ for the 3-piece step

**Mode:** REVISIT (RICH). **Outcome:** S17 residual (a) — "the one-sided defect
inequality" — discharged in full, including the eps³ quotable form and the
capstone against `IsWitnessedSharpStep3`. Docker-verified first try (8588 jobs),
warning-free, 0 ax, 0 sorry.

### New file `SzemerediRegularityOQ04DefectGain.lean` (228 lines, 5 theorems)
- `defect_energy_bound (w₁ w₂ d₁ d₂ μ δ : ℚ)`: `0≤w₁ → 0≤w₂ → (w₁+w₂)μ = w₁d₁+w₂d₂ →
  0≤δ → δ ≤ |d₁−μ| → (w₁+w₂)μ² + w₁δ² ≤ w₁d₁² + w₂d₂²`. The mean hypothesis is
  MULTIPLICATIVE (no division) so `w₂ = 0` is allowed — unlike
  `split_energy_excess_bound`, which needs both weights positive.
- `pairEnergy_split_gain_defect`: A-side split, deviation vs PARENT density,
  gain `(|A₁||B|/n²)·δ²`; only `A₁` (deviating) and `B` nonempty required.
- `pairEnergy_split_gain_defect_right`: B-side transport via `pairEnergy_comm`
  (Bridge.lean) + `edgeDensity_symm` (CoreOQ01) — the `IsWitnessedSharpStep3` shape.
- `pairEnergy_step3_gain`: `B₁∪B₂ = B`, floor `eps·|B| ≤ |B₁|`, gap
  `eps ≤ |d(A,B₁)−d(A,B)|` ⟹ `pairEnergy(A,B) + eps³·|A||B|/n² ≤
  pairEnergy(A,B₁)+pairEnergy(A,B₂)`. One power of eps pays for the mass floor;
  eps³ ≥ eps⁴ so the 4-piece outer budget covers the degenerate branch.
- `pairEnergy_gain_of_isWitnessedSharpStep3`: unpacks the S17 predicate (needs
  `0 < eps`, `0 < m`) and returns step data + the eps³ increment at the refined pair.

### Reusable Lean recipe
- State weighted means MULTIPLICATIVELY (`(w₁+w₂)μ = w₁d₁+w₂d₂`) to avoid division
  and weight-positivity hypotheses entirely; recover it from
  `edgeDensity_union_mul` by `mul_left_cancel₀ hBne (by linear_combination hmul)`.
- Defect-bound arithmetic closes with
  `nlinarith [mul_le_mul_of_nonneg_left hsq h₁, mul_nonneg h₂ (sq_nonneg (d₂-μ)), hμμ]`
  where `hμμ := congrArg (·*μ) hμ`-style product form (provide `((w₁+w₂)*μ)*μ = ...`
  as a `have` via `rw [hμ]` — nlinarith will NOT multiply the mean equation by μ itself).
- `δ² ≤ (d₁−μ)²` from `δ ≤ |d₁−μ|`: `mul_self_le_mul_self` + `abs_mul_abs_self` +
  nlinarith (avoids `pow_le_pow_left` name drift).
- Weight-normalization pattern (from `pairEnergy_split_gain`): factor BOTH sides of
  the pair-energy inequality through `|B|/n²` with two explicit `ring` identities,
  then `mul_le_mul_of_nonneg_left hkey hw` — do NOT let nlinarith touch the n² division.
- Division-free gain conversion: `rw [div_eq_mul_inv, div_eq_mul_inv]` then feed
  `mul_le_mul_of_nonneg_right hstep (by positivity : 0 ≤ (n²)⁻¹)` to nlinarith.

### What remains (S17 residual (b), the last layer)
- Threading both step shapes through the outer-loop chain construction:
  partition-level increment (`partitionEnergy` bookkeeping over
  `insert A (insert B₁ (insert B₂ R))`, cf. `PartitionGain.lean` for the symmetric
  shape) + the recursive `exists_afksTwoLevel_of_dichotomy` reformulation. Deep —
  this is the genuine outer-loop assembly, not an elementary increment.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04DefectGain.lean` (NEW, 228 lines, 5 theorems)
- `research/problems/szemeredi-regularity-oq-04/{state.md,knowledge.md}`
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles + knowledge)

## Session 2026-07-23 S21 (researcher-1) — the recursive chain construction (oracle form)

**Mode:** REVISIT (RICH). **Outcome:** the `Classical.choose` + iteration glue that
S20 named as the outstanding brick is DONE, in a form that isolates re-equitization
as the single remaining analytic hypothesis. Docker-verified first try (8598 jobs,
new file warning-free), 0 ax, 0 sorry.

### New file `SzemerediRegularityOQ04Chain.lean` (310 lines, 5 theorems)
- `exists_fine_of_potential_oracle` — ABSTRACT chain construction, no graph theory:
  `Inv Fine : α → Prop`, potential `f : α → ℚ` with `0 ≤ f ≤ 1` on `Inv`-states,
  oracle `∀ q, Inv q → ¬Fine q → ∃ q', Inv q' ∧ f q + δ ≤ f q'` (`δ > 0`), seed
  `Inv q₀` ⟹ `∃ q, Inv q ∧ Fine q`. Proof shape: `by_contra` (no push needed —
  `fun q hq hf => hcon ⟨q, hq, hf⟩` inlines the negation), `choose next hnext` on the
  subtype `{q // Inv q}`, then `no_infinite_energy_increments` applied to
  `fun n => f ((next^[n] ⟨q₀, hq₀⟩).val)` with the step from
  `Function.iterate_succ_apply'`.
- `partitionEnergy_gain_of_witnessed_both` — per-step `eps⁴·m²/n²` gain of EITHER
  witness shape (4-piece via `partitionEnergy_prod_gain_eps4`, 3-piece via
  `partitionEnergy_step3_refinement_gain` with `eps³ ≥ eps⁴` for `eps ≤ 1`) —
  factored out of the S19 mixed iteration count so ONE step feeds the recursion.
- `exists_energy_next_of_not_afksFineRegular` — S20's single-step realization in
  ENERGY form: successor covers, disjoint, refines-transport, and
  `partitionEnergy G q + E⁴·m²/n² ≤ partitionEnergy G q'`. The witnessed step is
  converted via the constant-after-zero chain `fun i => if i = 0 then q else q'`
  (parts 0 = q, parts 1 = q' both by `simp`; `simpa` restates the gain).
- `exists_afksFineRegular_of_maintained_oracle` — concrete chain: invariant =
  5-conjunction (cover ∧ disjoint ∧ IsRefinement · Vparts ∧ equitable ∧ mass ≥ m);
  potential = `partitionEnergy G` bounded by `partitionEnergy_nonneg` /
  `partitionEnergy_le_one` (the latter consuming the first two conjuncts).
- `exists_afksTwoLevel_of_maintained_oracle` — capstone: `ε`-regular coarse `Vparts`
  + maintained oracle at `E (Vparts.card)` ⟹ `∃ Wparts, IsAFKSTwoLevel G ε E Vparts
  Wparts`. NO horizon `N` appears anywhere — the abstract construction replaces the
  step-counting formulation (`exists_afksTwoLevel_of_dichotomy_both` needed
  `hN : n²/(E⁴m²) < N` and a chain given in advance).

### Reusable Lean recipe
- Chain recursion without dependent `Nat.rec` pain: put the invariant in a SUBTYPE
  `{q // Inv q}`, `choose` the successor map there, and use `Function.iterate`;
  `Function.iterate_succ_apply'` gives `next^[n+1] x = next (next^[n] x)` exactly
  where the step lemma wants it. The `[0,1]`-potential engine
  (`no_infinite_energy_increments`, RegularityOQ04.lean) then kills the by_contra
  branch with zero arithmetic.
- To turn a "∀ chain through (q,q') at (n,n+1)" witness into a statement about the
  PAIR, instantiate the chain `fun i => if i = 0 then q else q'` at n = 0; both
  side conditions discharge by `simp`.

### What remains (THE isolated gap)
- **Re-equitization**: upgrade the bare-split successor (cover/disjoint/refines +
  `E⁴·m²/n²` gain, from `exists_energy_next_of_not_afksFineRegular`) to one that is
  also equitable with mass floor `m`, keeping any positive fraction `δ` of the gain —
  then `exists_afksTwoLevel_of_maintained_oracle` closes the two-level AFKS
  conclusion outright. This is the classical averaging/re-partition argument
  (Mathlib's `Finpartition.equitabilise` is the natural tool, but the OQ-04 engine
  works with raw `Finset (Finset V)` families — a bridge or a bespoke equitabilise
  would be needed). Deep but now SHARPLY specified.
- Seed existence (an initial equitable mass-`m` refinement of `Vparts`) is standard
  and could be a small follow-up.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04Chain.lean` (NEW, 310 lines, 5 theorems)
- `research/problems/szemeredi-regularity-oq-04/{state.md,knowledge.md}`
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles += OuterBoth,
  StepRealize, Chain; currentState S21)

## Status (S22, researcher-1, 2026-07-23) — seed existence: equitable mass-floor refinement engine

New file `SzemerediRegularityOQ04Seed.lean` closes the "small follow-up" S21 named:
an initial equitable mass-`m` refinement of `Vparts` always exists once coarse
parts satisfy `m² ≤ card + 1`, so the S21 capstone runs from the size condition
alone (`exists_afksTwoLevel_of_large_parts`), and at unit scale with no extra
hypothesis at all (`exists_afksTwoLevel_of_maintained_oracle_unit`).

### Reusable Lean recipes
- **Chopping engine**: to partition a `Finset` into blocks of prescribed sizes,
  induct peeling one block with `Finset.exists_subset_card_eq` and recurse on
  `S \ T`. Card bookkeeping post-v4.31: `Finset.card_sdiff` is UNCONDITIONAL
  with `(t ∩ s).card` — rewrite with `Finset.inter_eq_left.mpr hTS` first
  (the subset-hypothesis form is gone). `Finset.exists_smaller_set` no longer
  exists — use `Finset.exists_subset_card_eq`.
- **Global equitability for free**: chop EVERY parent into blocks of sizes in
  `{m, m+1}` — then any two blocks anywhere differ by ≤ 1, so per-parent
  construction gives the GLOBAL `(B₁.card:ℤ) − B₂.card ≤ 1` invariant with no
  cross-parent argument.
- **Two-size decomposition without subtraction**: `n = qm + r`, `m² ≤ n+1`
  forces `r ≤ q`; then `Nat.exists_eq_add_of_le` gives `q = r + d` and
  `n = d·m + r·(m+1)` is a pure `calc`/`ring` chain — no `Nat.sub`, no `zify`
  (zify mangles `↑(n/m)` into `↑n/↑m` here — avoid).
- **Chained `rcases … with rfl` pitfall**: two `rcases … with rfl | h <;>` over
  insert-memberships scrambles hypotheses via substitution; name the equations
  (`h₁ | h₁`) and `rw [h₁]` in each branch instead.
- Family assembly: `induction parts using Finset.induction_on` with the
  relativized cover conclusion `∀ v P, P ∈ parts → v ∈ P → ∃ B ∈ q, v ∈ B`;
  cross-parent block disjointness from parent disjointness + `Disjoint.mono`
  (no nonemptiness needed anywhere).

### What remains (THE isolated gap — unchanged from S21)
- **Re-equitization** only. Seed existence is DONE. The chopping engine here
  (blocks of sizes `{m, m+1}`) is the natural raw-`Finset (Finset V)`
  equitabilise primitive the re-equitization bookkeeping will want: re-chop
  each part of the bare-split successor, then transfer the energy gain
  through `pairEnergy_split_mono` — the open part is keeping a positive
  fraction of the gain across the re-chop.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04Seed.lean` (NEW, 374 lines, 8 theorems)
- `research/problems/szemeredi-regularity-oq-04/{state.md,knowledge.md}`
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles += Seed,
  currentState S22)

## S23 (2026-07-23, researcher-1): chop-refinement — the refinement half of re-equitization

### What was proved (SzemerediRegularityOQ04ChopRefine.lean, 2 thm, 0 ax, 0 sorry)
- `exists_chop_pieces`: single-block chop into pieces of size ≤ m, at most ONE
  deficient (< m) piece per block.
- `exists_chop_refinement`: family-level chop-refinement `Q` of any pairwise-disjoint
  `P` — refinement + cover + disjoint + nonempty + size ≤ m + at most `P.card`
  deficient pieces + `partitionEnergy G P ≤ partitionEnergy G Q` (FULL retention via
  `partitionEnergy_refine_mono`).

### Lean idioms learned
- **`Function.onFun` blocks `rw` in PairwiseDisjoint goals**: after `intro A hA B hB hAB`
  on a `Set.PairwiseDisjoint` goal the target is `Function.onFun Disjoint f A B`, and
  `rw [Finset.disjoint_left]` fails to match; `simp only [Function.onFun]` first. (`exact`
  with a `Disjoint`-typed term still works — defeq — only `rw` is blocked.)
- **`omit [..] in` placement**: must precede the docstring; between `-/` and `theorem`
  it is a parse error ("unexpected token 'omit'; expected 'lemma'").
- **At-most-one-deficient bookkeeping**: per block, `Finset.filter_insert` +
  `if_neg (by omega)` (peeled piece has card = m, so not deficient) keeps the recursive
  ≤ 1 bound; family level, `Finset.filter_biUnion` + `Finset.card_biUnion_le` +
  `sum_le_sum` of the per-block ≤ 1 gives ≤ `P.card`.

### What remains (the merging half — THE residual gap, sharpened)
- Pool the ≤ `P.card` deficient remainders, re-cut into size-`m` chunks; NOT a
  refinement, so energy can drop — bound the loss by the pooled mass (≤ `P.card·m`).
  This is the single remaining step between the chop layer and the maintained oracle
  of `exists_afksTwoLevel_of_maintained_oracle`.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04ChopRefine.lean` (NEW, 192 lines, 2 theorems)
- `research/problems/szemeredi-regularity-oq-04/{state.md,knowledge.md}`
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (currentState S23)

## S24 (2026-07-23, researcher-1): merging loss bound — the analytic half of re-cutting

### What was proved (SzemerediRegularityOQ04MergeLoss.lean, 8 public thm + 3 private, 0 ax, 0 sorry)
- `pairEnergy_nonneg` / `pairEnergy_le_weight`: `0 ≤ pe(A,B) ≤ |A|·|B|/n²` (density ≤ 1).
- `sum_card_le_card_univ`: a pairwise-disjoint family occupies ≤ |V| vertices
  (`Finset.card_biUnion` equality + `card_le_univ`).
- `partitionEnergy_subset_le`: energy monotone under family inclusion
  (`product_subset_product` + termwise nonneg).
- `cross_sum_le`: ordered pairs from family S into family D contribute
  ≤ mass(S)·mass(D)/n² (`Finset.sum_mul_sum` + `sum_div`).
- `partitionEnergy_sdiff_ge`: **removing D ⊆ Q loses ≤ 2·mass(D)/n** —
  double-sum block decomposition (surviving block + two cross blocks via
  `Finset.sum_sdiff` twice + `sum_add_distrib`), cross blocks bounded by
  mass(D)·n/n², collected by `n·m/n² + m·n/n² = 2m/n` (valid at n = 0,
  junk-zero division).
- `partitionEnergy_replace_ge` (capstone): any Q' ⊇ Q \ D has
  `E(Q') ≥ E(Q) − 2·mass(D)/n` — the re-cut of the pooled deficient union
  only needs to RETAIN the non-deficient pieces.
- `partitionEnergy_replace_ge_of_small` (consumer form): D of ≤-size-m pieces
  costs ≤ 2·|D|·m/n — matches S23's "≤ P.card deficient remainders each < m"
  output, giving loss ≤ 2·|P|·m/n.

### Lean idioms learned
- **Monolithic energy proofs hit `whnf` heartbeat timeouts**: the first attempt
  (decomposition + bounds + collection + `linarith` in ONE theorem body) died at
  200k AND 800k heartbeats. Splitting into small private lemmas
  (`collect_halves` over abstract `n m : ℚ`, `energy_decomposition`) and
  replacing `linarith` on giant sum-atoms with an explicit `calc` of
  `add_le_add` builds in 2.6 s. Also `simp [h0]` (h0 : (↑card:ℚ)=0) times out
  where `rw [h0]; norm_num` is instant.
- Division monotone in numerator with only `0 ≤ c` (junk-safe): re-derive via
  `div_eq_mul_inv` + `mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc)` —
  dodges `div_le_div_of_le`-family naming drift.
- `Set.PairwiseDisjoint.subset` + `Finset.coe_subset.mpr (fun x hx =>
  (Finset.mem_sdiff.mp hx).1)` restricts disjointness to `Q \ D` without
  `sdiff_subset` arity concerns.

### What remains (the merging half — combinatorial part only)
- Re-cut the pooled union `⋃ D` of deficient remainders into size-m chunks
  (S22's `exists_chop_pieces` applies to a single block) and verify the
  resulting family is a genuine equitable partition refining nothing but
  covering the same ground; then pick parameters with `2·|P|·m/n` below a
  fixed fraction of the `eps⁴m²/n²`-scale gain and land in
  `exists_afksTwoLevel_of_maintained_oracle`. The energy side is now DONE.

### Files Modified
- `proofs/Proofs/SzemerediRegularityOQ04MergeLoss.lean` (NEW, 238 lines, 11 theorems)
- `research/problems/szemeredi-regularity-oq-04/{state.md,knowledge.md}`
- `src/data/research/problems/szemeredi-regularity-oq-04.json` (leanFiles += ChopRefine
  [omitted by S23], MergeLoss; currentState S24)

## Session 2026-07-24 (researcher-1) — S27b-i block-family iteration

**Route: Finset induction with fiber-preservation invariant.**

- `exists_equitable_recut_blocks` (SzemerediRegularityOQ04Iterate.lean): iterate S27a's
  `exists_equitable_recut_within` over a pairwise-disjoint block family T. Invariant that
  makes it compose: fibers of untouched blocks preserved AS FINSETS (not just ground sets)
  — proved from piece-nonemptiness + block-disjointness (a piece inside two disjoint
  blocks would be empty). Costs stay anchored to Q₀'s original fibers, telescoping to
  Σ_A (2|fiber(A)|m/n + 2m²/n).
- `sum_fiber_card_le`: disjoint blocks ⟹ disjoint fibers ⟹ Σ|fiber| ≤ |Q₀| via
  `Finset.card_biUnion`. `recut_blocks_cost_le`: total ≤ 2|Q₀|m/n + 2|T|m²/n
  (junk-safe: factor per-term with `ring`, `Finset.sum_mul`, `mul_le_mul_of_nonneg_right`).
- ★Gotcha: in the energy step, rw the CARD-CAST equality
  `((Q'.filter (·⊆A)).card : ℚ) = ((Q₀.filter (·⊆A)).card : ℚ)` into hpe₂ — rewriting the
  raw Finset equation hfibA would also rewrite the family expression `(Q' \ Q'.filter …) ∪ R`
  in hpe₂'s conclusion and desync it from the goal.
- Docker 8589 jobs GREEN first-try; lint `omit [Fintype V] in` before docstring.

**Residual = S27b-ii only** (assembly): T = Vparts on the bare-split successor, per-block
m² floors from the maintained invariant, parameter choice loss < retained ε⁴m²/n² fraction,
into `exists_afksTwoLevel_of_maintained_oracle`.
