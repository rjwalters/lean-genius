# Research State: fourier-series-oq-04-oq-01

## Current State
**Phase**: ACT
**Since**: 2026-05-31 (S11 ACT — `haarT2_eq_volume` bridge landed)
**Iteration**: 10
**Last Update**: 2026-05-31 (researcher-1) — **S11 ACT step-1-contingency**: `haarT2_eq_volume` measure-equality bridge landed as a sorry-free / axiom-free **public** theorem (~33 LOC including section docstring). Discharges **step 1 contingency** of the S7 audit §4 recipe (the haarT2/volume measure disambiguation). The Mathlib engine `hasSum_mFourier_series_L2` (in `Mathlib.Analysis.Fourier.AddCircleMulti` at pin v4.26.0, line 224) is stated over `L²(UnitAddTorus d)` with the **default `volume` measure** on `Fin 2 → AddCircle 1`. Our `haarT2` is `Measure.pi (fun _ => haarAddCircle)`. The bridge enables invoking the Mathlib engine on our `haarT2`-stated theorems. Combined with S9 (cofinality, step 3) and S10 (`Lp.coeFn_finset_sum` helper, step 2), **3 of 6 recipe steps are now landed**. Remaining S2e ACT scope shrinks to ~25-45 LOC (steps 1-setup + 4 + 5 + 6); the `eLpNorm`-form close remains a tractable single-iteration target.

## Current Focus

S11 ACT step-1-contingency (researcher-1, 2026-05-31) — **ACT mini-task delivering
the `haarT2 = volume` bridge** of the S7 audit §4 recipe (step 1 contingency,
3-5 LOC budgeted; actual ~33 LOC including section docstring). Adds one
sorry-free, axiom-free, **public** theorem:

- `haarT2_eq_volume : haarT2 = (volume : Measure T2)`
  — the measure-equality bridge on `Fin 2 → AddCircle 1`. Proof:
  `AddCircle.volume_eq_smul_haarAddCircle` (AddCircle.lean:92, **rfl**)
  states `volume = ENNReal.ofReal T • haarAddCircle`; at `T = 1`,
  `ENNReal.ofReal 1 = 1` and `(1 : ℝ≥0∞) • μ = μ` via `one_smul`, so
  `volume = haarAddCircle` on `AddCircle 1`. The product side: `volume_pi`
  (Pi.lean:652, **also rfl**) gives `(volume : Measure (∀ i, α i)) =
  Measure.pi (fun _ => volume)`. Combining: `Measure.pi (fun _ => haarAddCircle)
  = Measure.pi (fun _ => volume) = volume` (the last step by `volume_pi.symm`,
  rfl).

  Tactics: `show Measure.pi (fun _ : Fin 2 => (haarAddCircle : Measure (AddCircle (1 : ℝ))))
  = (volume : Measure T2)` (display goal explicitly to avoid namespace
  shadowing on `Measure.pi`), then `simp_rw [key]` where `key :
  haarAddCircle = volume` (rewrites under the `fun _ =>` binder), then
  `rfl`. No new sorries, no new axioms.

**Key Mathlib finding (this iter)**: the `volume = haarAddCircle` collapse
at `T = 1` is *immediate* from a single `rfl` lemma (`volume_eq_smul_haarAddCircle`)
plus the trivial scaling `ENNReal.ofReal 1 = 1` and `one_smul`. No
`MeasureSpace` instance hijinks, no `withDensity`, no `pi_pi_eq` rewriting
required. The S7 audit §2.5 had flagged this as the "haarT2/volume errata"
that the S2f PREP (#18545) addressed at the spec level; this S11 ACT
delivers the corresponding Lean lemma in 4 tactic lines.

**S2e ACT scope after this iteration**: step 1 contingency ✅ done; step 2
(`coeFn_finset_sum`) ✅ done (S10); step 3 (cofinality) ✅ done (S9).
Remaining recipe = step 1 (Setup imports, 3-5 LOC — note: `import Mathlib`
already pulls `AddCircleMulti` so this may be a no-op; verify at next ACT)
+ step 4 (Bridge `sphPartialSum` → Lp finset-sum, 15-25 LOC) + step 5 (cite
`hasSum_mFourier_series_L2`, 5-10 LOC) + step 6 (close `eLpNorm`-form via
`Lp.norm_def`, 5-10 LOC) = **25-45 LOC**. A future single-iteration close
is now genuinely tractable, with three of the four trickiest bearer
helpers already landed and verified.

**Build status**: Docker-built and verified (researcher-1, 2026-05-31,
worktree HEAD ~`e36a09a3` for this branch; cached cache-get + ~3 min
elaboration; only the pre-existing `sphPartialSum_L2_norm_converge` sorry
warning at line 148; no new warnings from the bridge addition). Updated
Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (413 → 446 lines,
11 → 12 theorems; +1 sorry-free public theorem in a new "S2e-step1-contingency"
section after `coeFn_finset_sum_haarT2`). Gallery meta-json line/theorem
counts synced; new `haart2-volume-bridge` section added with `startLine:
411`, `endLine: 443`; `originalContributions` extended.

Full forensics in `sessions/2026-05-31-s11-act-step1-contingency-haart2-volume.md`.

---

## Previous Focus — S10 ACT step-2 (2026-05-30, researcher-1, MERGED PR #21252)

S10 ACT step-2 (researcher-1, 2026-05-30) — **ACT mini-task delivering
the `Lp.coeFn_finset_sum` helper** of the S7 audit §4 recipe (step 2,
8-10 LOC budgeted; actual ~30 LOC including section docstring). Adds one
sorry-free, axiom-free **private** theorem:

- `coeFn_finset_sum_haarT2 {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 haarT2) : ⇑(∑ k ∈ s, f k) =ᵐ[haarT2] fun x => ∑ k ∈ s, (f k : T2 → ℂ) x`
  — the Mathlib-gap helper. By `Finset.induction_on`. **Empty case**:
  `Finset.sum_empty` reduces both sides to `(0 : Lp ℂ 2 haarT2)` and
  `(0 : T2 → ℂ)`; closed by `Lp.coeFn_zero ℂ 2 haarT2` directly via
  `exact`. **Insert case**: `Finset.sum_insert hkS` splits both sides;
  `Lp.coeFn_add (f k) _` distributes the LHS coercion through the binary
  `+`; the inductive hypothesis + `Filter.EventuallyEq.refl _ ⇑(f k)` are
  combined via `Filter.EventuallyEq.add` to close the goal.

The lemma is **measure-disambiguation-free** — stated and proved entirely
over `haarT2`; no `haarT2 = volume` step required. Tactics:
`Finset.induction_on`, `simp only [Finset.sum_empty]`, `simp only
[Finset.sum_insert hkS]`, `Lp.coeFn_zero`, `Lp.coeFn_add`,
`Filter.EventuallyEq.refl`, `Filter.EventuallyEq.add`. No new sorries,
no new axioms.

**Fix-iteration note** (build-time learning): a first attempt used
`filter_upwards [Lp.coeFn_zero ℂ 2 haarT2] with x hx; simp [hx]` for the
empty case and `filter_upwards [ih] with x hx; simp [Finset.sum_insert
hkS, hx, Pi.add_apply]` for the insert case. Both failed: the empty-case
`simp` couldn't bridge `↑0 x = 0` (single-arrow goal post-`filter_upwards`)
against `↑↑0 x = 0 x` (double-arrow `hx`), and the insert-case `simp`
triggered an unintended `Lp.coe_finset_sum`-style distribution on the
inductive LHS (`↑(∑ i ∈ s, ↑(f i)) x` instead of the expected `⇑(∑ j ∈ s,
f j) x`). The fix: avoid `simp` heuristics entirely. Use
`Lp.coeFn_zero ℂ 2 haarT2` directly via `exact` (Lean handles the
`0 : T2 → ℂ` vs `fun x => 0` eta-bridge), and combine the two
`EventuallyEq`s via `Filter.EventuallyEq.add` (which avoids touching the
`Lp.coe_finset_sum` lemma altogether).

**S2e ACT scope after this iteration**: step 2 (`coeFn_finset_sum`
helper) ✅ done; step 3 (cofinality) ✅ done (S9, 2026-05-29). Remaining
recipe = steps 1 (Setup, 3-5 LOC + 3-5 LOC haarT2/volume contingency) +
4 (Bridge `sphPartialSum` → Lp finset-sum, 15-25 LOC) + 5 (cite
`hasSum_mFourier_series_L2`, 5-10 LOC) + 6 (close `eLpNorm`-form via
`Lp.norm_def`, 5-10 LOC) = 28-55 LOC. A future single-iteration close
is now genuinely tractable.

**Build status**: Docker-built and verified (researcher-1, 2026-05-30
worktree HEAD `f19276d72c8`; cached cache-get + ~3 min elaboration; only
the pre-existing `sphPartialSum_L2_norm_converge` sorry warning at line
148; no new warnings from the helper addition). Updated Lean file:
`proofs/Proofs/FourierSeriesOQ04OQ01.lean` (375 → 413 lines, 10 → 11
theorems; +1 sorry-free private theorem in a new "S2e-step2" section
after `latticeDisc_eventually_supset`). Gallery meta-json line/theorem
counts synced; new `lp-coefn-finset-sum` section added with `startLine:
373`, `endLine: 409`; `originalContributions` extended.

Full forensics in `sessions/2026-05-30-s10-act-step2-coefn-finset-sum.md`.

---

## Previous Focus — S9 ACT cofinality (2026-05-29, researcher-1, MERGED PR #21131)

S9 ACT cofinality (researcher-1, 2026-05-29) — **ACT mini-task delivering
the cofinality bearer** of the S7 audit §4 recipe (step 3, 15-25 LOC
budgeted; actual ~85 LOC including the singleton helper). Adds two
sorry-free, axiom-free, public theorems:

- `latticeDisc_mem_eventually (k : Fin 2 → ℤ) : ∀ᶠ R in (atTop : Filter ℝ), k ∈ latticeDisc R`
  — singleton-case cofinality. For `R ≥ (k 0)² + (k 1)² + 1`, the
  cardinality condition `(k 0)² + (k 1)² ≤ R²` (via `R ≥ 1 ⇒ R ≤ R²`)
  and the bounding-box condition `|k i| ≤ ⌈|R|⌉` (via `Real.sqrt_sq_eq_abs`
  + `Int.le_ceil`) both hold.
- `latticeDisc_eventually_supset (S : Finset (Fin 2 → ℤ)) : ∀ᶠ R in (atTop : Filter ℝ), S ⊆ latticeDisc R`
  — the full cofinality lemma. By `Finset.induction_on` from
  `latticeDisc_mem_eventually`, combining the per-point witnesses via
  `Filter.filter_upwards`.

The lemmas are **pure ℝ/ℤ arithmetic** — they use no measure-theoretic
APIs, no `Lp`, no `volume`/`haarT2` disambiguation. Tactics: `linarith`,
`nlinarith`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`, `Int.le_ceil`,
`Finset.mem_filter`, `Finset.mem_Icc`, `Finset.induction_on`,
`Filter.eventually_atTop`. No new sorries, no new axioms.

**S2e ACT scope after this iteration**: step 3 (cofinality) ✅ done.
Remaining recipe = steps 1 (Setup, 3-5 LOC) + 2 (drop-in `coeFn_finset_sum`
helper, 8-10 LOC) + 4 (Bridge `sphPartialSum` → Lp finset-sum, 15-25 LOC) +
5 (cite `hasSum_mFourier_series_L2`, 5-10 LOC) + 6 (close `eLpNorm`-form
via `Lp.norm_def`, 5-10 LOC) = 36-60 LOC + 3-5 LOC haarT2/volume contingency.
A future single-iteration close is now genuinely tractable.

**Build status**: Docker-built and verified (researcher-1, 2026-05-29,
7743 jobs, only the pre-existing `sphPartialSum_L2_norm_converge` sorry
warning at line 148; no new warnings from the cofinality addition).
Updated Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (279 → 366
lines, 8 → 10 theorems; +2 sorry-free public theorems in a new
"S2e-cofinality" section after `latticeDisc_card_le_real`). Gallery
meta-json line/theorem counts synced; new `lattice-disc-cofinality`
section added with `startLine: 277`, `endLine: 362`; `originalContributions`
extended.

Full forensics in `sessions/2026-05-29-s9-act-cofinality.md`.

---

## Previous Focus — S8 STATE-SYNC (2026-05-16, researcher-9, MERGED)

S8 STATE-SYNC (researcher-9, 2026-05-16) — **doc-only absorption of
the S7 audit-at-pick-time merge**. PR #19411 (researcher-12, MERGED
2026-05-16T03:26:54Z) shipped a sessions-only diff that resolved S6
STATE-SYNC #19385's gate-4 AMBER → GREEN by pinning all 5 S2e PREP
bearers at current Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
with section-header typeclass annotations: `HilbertBasis.hasSum_repr`
(`l2Space.lean:443`), `mFourierBasis` (`AddCircleMulti.lean:204`),
`Lp.coeFn_finset_sum` (CONFIRMED ABSENT — paste-ready §2.2.1 inductive
helper closes), `tendsto_atTop_atTop_of_monotone` (`AtTopBot/Tendsto.lean:153`,
ineligible — `latticeDisc R` not monotone in `R`; use direct `∀ᶠ` form),
`Lp.norm_def` (`LpSpace/Basic.lean:215`). Per the audit's §7 conflict-free
clause, state.md/JSON updates were deferred to either the eventual S6
STATE-SYNC (#19385, merged 26 min later at 03:52:45Z) or the eventual
S2e ACT; #19385's diff predates the audit so still flags gate-4 AMBER.
This STATE-SYNC bumps iter 6→7, refreshes `currentState.focus` /
`nextAction` to point to the now-fully-unblocked S2e ACT with the
paste-ready 53-85 LOC recipe (per S7 audit §4), and brings all 6 gates
to GREEN. Bearer drift recheck at worktree HEAD `cf1cfa085e42`: Mathlib
pin unchanged → 0 drift across 5 bearers (verified via spot-check `gh api`
on the highest-risk bearer, the `Lp.coeFn_finset_sum` gap, which remains
absent). No Lean delta; no new sorries; no new axioms.

## Session N=7 — S7 audit-at-pick-time (2026-05-16, researcher-12, MERGED PR #19411)

**Mode**: ACT (audit-at-pick-time for S2e ACT bearers; sessions-only diff per #19411 §7).

**Outcome**: Re-pinned all 5 Mathlib bearers at current rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. **0 drift since S2g PREP audit** (2026-05-13). Material new finding: explicit section-header typeclass context for each bearer (the "audit-at-pick-time" requirement noted in memory-trap `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`). With this audit, the S6 STATE-SYNC #19385's gate-4 transitions from AMBER (audit-at-pick-time) to **GREEN (Mathlib gap noted in §3, helper code paste-ready in §3.2)**.

**Paste-ready helper for the Mathlib gap** (`Lp.coeFn_finset_sum` — STILL ABSENT at current rev; verified by S7 audit §2.2 + this S8 STATE-SYNC §2 spot-check):

```lean
-- ~8-10 LOC, uses only Lp.coeFn_add at line 195 of Mathlib LpSpace/Basic.lean
private theorem coeFn_finset_sum
    {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    ⇑(∑ k ∈ s, f k) =ᵐ[volume] fun x => ∑ k ∈ s, (f k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.sum_insert his]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with x hx
    simp [Finset.sum_insert his, hx]
```

**Risk note (carried forward)**: empty-case `simp` may not close; explicit fallback `rw [Finset.sum_empty]; exact Lp.coeFn_zero`.

**Gate-4 resolution table** (this STATE-SYNC re-confirms):

| Gate | #19385 state | Post-S7 state | Post-S8 state | Notes |
|---|---|---|---|---|
| (1) PREP chain merged | ✅ GREEN | ✅ GREEN | ✅ GREEN | #18446 / #18545 / #18694 all MERGED 2026-05-13 |
| (2) Baseline build-verified | ✅ GREEN | ✅ GREEN | ✅ GREEN | S2-Gauss-real Docker 7743 jobs clean |
| (3) Operational blocker | ✅ GREEN | ✅ GREEN | ✅ GREEN | `.lake symlink loop` false-alarm cleared by #19385 |
| (4) Bearer drift on S2e PREP bearers | ⚠ AMBER | ✅ GREEN | ✅ GREEN | S7 audit + S8 spot-check; 0 drift across 5 bearers; gap helper paste-ready |
| (5) Budget reasonable | ✅ GREEN | ✅ GREEN | ✅ GREEN | 53-85 LOC + 2-3 Docker iter |
| (6) Orthogonality to open PRs | ✅ GREEN | ✅ GREEN | ✅ GREEN | 0 open PRs touching slug Lean file (verified at this iteration) |

**Next-cycle invocation** (S2e ACT, 53-85 LOC):

1. Setup (3-5 LOC) — `Mathlib.Analysis.Fourier.AddCircleMulti` + `Mathlib.Analysis.InnerProductSpace.l2Space`; `haarT2 = volume` resolution (S7 audit §2.5).
2. Drop in S7 §2.2.1 helper (8-10 LOC).
3. Cofinality `latticeDisc_eventually_supset` in `∀ᶠ` form (15-25 LOC; S7 §2.3).
4. Bridge `sphPartialSum` → Lp finset-sum (15-25 LOC).
5. Cite engine `hasSum_mFourier_series_L2` at `AddCircleMulti.lean:224` (5-10 LOC).
6. Close `eLpNorm`-form via `Lp.norm_def` at `LpSpace/Basic.lean:215` (5-10 LOC; S7 §2.4).

Full forensics in `sessions/2026-05-16-s8-statesync-absorb-s7-audit.md`.

---

## Previous Current Focus — S6 STATE-SYNC (2026-05-15, researcher-9, MERGED PR #19385)

S6 STATE-SYNC (researcher-9, 2026-05-15) — **doc-only post-drain
catch-up**. The S2 build-verify drain wave (PRs #19033 MERGED
2026-05-16T00:11Z + #19055 MERGED 2026-05-15T23:27Z) left state.md
with three load-bearing drift items: S2c "still build pending" (line
106), S2d "still build pending" (line 73-82), and Operational blocker
".lake symlink loop" (line 173-176) — all retired here per the
session log of PR #19033 (whose actual diff shipped only the session
file, not the state.md/JSON updates §2 listed). Bearer drift recheck
against Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
0 drift — the rev pin is unchanged since S2d PREP and the docker
build at S2-Gauss-real ACT validated the full bearer surface
(Pi.card_Icc, Int.card_Icc, Finset.prod_const, Fintype.card_fin,
.trans_eq, Finset.filter_subset, Finset.card_le_card,
Int.toNat_of_nonneg, Int.ceil_lt_add_one, pow_le_pow_left₀,
Int.ceil_nonneg). ACT-readiness gate for next-action S2e ACT
(mFourierBasis L² discharge, 70-95 LOC budget) remained GREEN at S6
**except** gate-4 (audit-at-pick-time required); cleared by S7 audit
above. No Lean delta; no new sorries; no new axioms.

## Previous Focus (S2-Gauss-real)

S2-Gauss-real (researcher-8, 2026-05-14) — **ACT mini-task** bridging
S2d's `Nat`-valued explicit bound to a `Real`-form analytic bound
suitable for downstream `ℓ¹`-majorisation / Plancherel estimates on
`sphPartialSum`. Adds one sorry-free, axiom-free lemma:

- `latticeDisc_card_le_real (R : ℝ) : ((latticeDisc R).card : ℝ)
                       ≤ (2 * |R| + 3) ^ 2` — composition of S2d's
  `latticeDisc_card_le_explicit` (Nat side) with the cast bridge
  `Int.toNat_of_nonneg` + `Int.ceil_lt_add_one` + `pow_le_pow_left₀`
  (monotone squaring of nonneg). The constant 4|R|² + 12|R| + 9 is the
  expanded form; the (2|R|+3)² shape is the natural closure under the
  cited Mathlib lemmas.

The bound is **qualitative** (constant 4 vs sharp π); the sharp
constant `π` (the genuine Gauss-circle problem `card ≤ ⌈π·R²⌉ + O(R)`)
requires boundary-lattice / two-squares analysis and remains deferred
(S2-Gauss-sharp, later session). This iteration ships the analytic-form
bound usable now in `sphPartialSum` `ℓ¹`-majorisation estimates,
without waiting on the harder sharp bound.

Updated Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (234 →
~286 lines, 7 → 8 theorems; +1 sorry-free lemma at the end of the
S2-Gauss block, after `latticeDisc_card_le_explicit`).

**Build status**: ✅ **build verified** (Docker, 7743 jobs, only the
expected `sphPartialSum_L2_norm_converge` sorry warning at line 148;
new lemma's `pow_le_pow_left₀` + `Int.toNat_of_nonneg` + `push_cast`
+ `linarith` proof block elaborates cleanly). Companion to researcher-9
PR #19033 (S2 build-verify, doc-only) — this PR is the first build-
verified ACT delivering new Lean content on top of the verified
baseline.

## S2d (Previous Iteration)

S2d (researcher-4, 2026-05-13) — **ACT Path A** from S2d PREP #18393
(researcher-5). Adds two sorry-free, axiom-free helper lemmas that
sharpen S2c's qualitative subset bound to a closed-form numerical
Gauss-circle upper bound:

- `bbox_card (R : ℝ) : #(Icc (fun _ => -⌈|R|⌉) (fun _ => ⌈|R|⌉))
                       = (2*⌈|R|⌉+1).toNat ^ 2` — explicit cardinality of the
  integer bounding box `[-⌈|R|⌉, ⌈|R|⌉]² ⊂ ℤ²` via `Pi.card_Icc` (the
  product-over-Fin-2 decomposition) + `Int.card_Icc` (the 1D `@[simp]`
  formula). Proof: `rw [Pi.card_Icc] ; simp only [Int.card_Icc] ;
  have h : ... = 2⌈|R|⌉+1 := by ring ; simp [h, Finset.prod_const,
  Fintype.card_fin]` (4 tactic lines).
- `latticeDisc_card_le_explicit (R : ℝ) : (latticeDisc R).card
                       ≤ (2*⌈|R|⌉+1).toNat ^ 2` — composition of S2c's
  `latticeDisc_card_le_bbox R` with `bbox_card R` via `.trans_eq`
  (1 line; term-mode).

Combined with the trivial estimate `⌈|R|⌉ ≤ |R| + 1`, this gives
`(latticeDisc R).card = O(R²)` — the qualitative Gauss-circle bound.
The sharp constant `π` (the genuine Gauss-circle problem
`card ≤ ⌈π·R²⌉ + O(R)`) requires boundary-lattice / two-squares
analysis and remains deferred (S2e or later).

Updated Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (204 → 234
lines, 5 → 7 theorems; +2 sorry-free lemmas at the end). Gallery
meta-json line/theorem counts synced; new `lattice-disc-explicit-card`
section added (startLine 202, endLine 230); `originalContributions`
extended.

**Build status**: ✅ **build VERIFIED** (Docker, 7743 jobs, single
expected `sphPartialSum_L2_norm_converge` sorry warning at line 148)
via researcher-9 (2026-05-14, log
`.loom/logs/researcher-9-fourier-s2d-verify.log`; companion to PR
#19033 doc-only retire-qualifier, MERGED 2026-05-16T00:11Z). The
`.lake symlink loop` worktree concern was a false alarm: the Docker
wrapper mounts `/lean/.lake` inside the container and is unaffected by
the host `.lake` directory (per MEMORY.md
`feedback_researcher_build_pending_dot_lake_symlink_false_alarm`).
Both new lemmas are direct applications of stable Mathlib lemmas
(`Pi.card_Icc`, `Int.card_Icc`, `Finset.prod_const`, `Fintype.card_fin`,
`.trans_eq`) at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0). The S2d PREP §2.3 medium-risk flag on the `simp` step
closing the product evaluation was discharged at build time — no
fallback to `Fin.prod_univ_succ` + `Fin.prod_univ_zero` was needed;
the inline `simp` was specific enough.

## S2c (Previous Iteration)

S2c (researcher-1, 2026-05-12) — **ACT parallel mini-task** adding two
sorry-free helper lemmas advancing the Gauss-circle prep noted in the
S2a state.md:

- `latticeDisc_subset_bbox` — the lattice disc is a subset of the integer
  bounding box `[-⌈|R|⌉, ⌈|R|⌉]²` (1-line proof, `Finset.filter_subset`).
- `latticeDisc_card_le_bbox` — corollary cardinality bound
  (`Finset.card_le_card`).

These give the trivial pre-Gauss bound `(latticeDisc R).card ≤ (2·⌈|R|⌉+1)²`
once the bounding-box cardinality is unfolded — useful for crude ℓ¹
majorisation of the spherical partial sum. The sharper Gauss-circle bound
`card ≤ ⌈π·R²⌉ + O(R)` is deferred to S2d.

Updated Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (179 → 204
lines, 3 → 5 theorems; +2 sorry-free lemmas at the end). Gallery
meta-json line/theorem counts synced; new "lattice-disc-bbox" section
added; sanity-checks section line range corrected to 162-175 (was
167-178 after S2a's section-numbering drift).

**Build status**: ✅ **build VERIFIED** (transitively via the S2d
`latticeDisc_card_le_explicit` Docker run, which depends on these
S2c lemmas — `latticeDisc_subset_bbox` + `latticeDisc_card_le_bbox` —
and was confirmed clean by researcher-9, 2026-05-14, 7743 jobs).
Both proofs are direct applications of stable Mathlib lemmas
(`Finset.filter_subset`, `Finset.card_le_card`); the `.lake symlink
loop` worktree concern cited at original push time was a false alarm
(Docker wrapper mounts `/lean/.lake` inside the container, isolated
from host).

Earlier (S2a, researcher-8): ACT scaffold for the 2D Carleson
spherical-summation conjecture (axiomatized) + unconditional
L²-norm-convergence companion (sorried) + gallery entry.

Deliverables in this iteration:
- `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (179 lines) — rigorous defs
  (`T2`, `haarT2`, `multiFourierCoeff`, `latticeDisc`, `sphPartialSum`),
  1 axiom (`carleson_2d_sph`), 1 sorried companion theorem
  (`sphPartialSum_L2_norm_converge`), 2 definitional sanity-check lemmas.
- `proofs/Proofs.lean` — register new file in the umbrella.
- `src/data/proofs/fourier-series-oq-04-oq-01/{meta.json,index.ts,annotations.json}`
  — gallery entry, `status: "axiomatized"`, `badge: "axiom"`,
  `sorries: 1`, `axiomCount: 1`.

The S1 OBSERVE spec (state.md from PR #18062) was followed verbatim:
`T2 := Fin 2 → AddCircle 1`, `multiFourierCoeff` as iterated integral with
`fourier (-(k 0)) (x 0) * fourier (-(k 1)) (x 1)` characters, `latticeDisc`
as a `Finset.Icc` bounding box filtered by the disc inequality, and the
`carleson_2d_sph` axiom with `MemLp f 2 haarT2` and `Tendsto ... atTop`.

**Build status**: This worktree's `proofs/.lake` symlink is recursive
(known infrastructure issue; ~25 minute fresh Mathlib clone needed for
docker build), so the file is pushed as **build pending** per the
gallery's standard convention for newly-introduced files. The
sanity-check lemmas (`multiFourierCoeff_zero`, `sphPartialSum_zero`)
are intentionally short and should compile cleanly; the companion theorem
`sphPartialSum_L2_norm_converge` is `sorry`d so a build failure there
would be a definitional / type-signature issue rather than a missing
lemma.

## Active Approach

**Axiomatize the open conjecture; formalize the partial results that are
provable unconditionally.**

The structural pattern matches sibling axiomatized open-problem entries
(`fourier-series-oq-01` for the 1D analogue with `carleson_hunt_maximal`
as a single axiom). Per the gallery's Axiom Integrity Policy, the entry
uses `status: "axiomatized"` with `badge: "axiom"` (never `"verified"`)
and reports `axiomCount: 1, sorries: 1` honestly.

## Blockers

**Mathlib gaps (carryover from S1):**
1. No named `Plancherel_ntorus` identity exposed in Mathlib (the
   orthonormal-basis tensor-product on `lp 2` exists but is implicit).
   This blocks closing the `sphPartialSum_L2_norm_converge` sorry. Future
   contribution target: ~30-50 line Mathlib PR.
2. No `Bochner-Riesz` / `ballMultiplier` API. Required for the regularised
   $\delta > 1/2$ a.e. convergence (Stein 1958) — see S2b plan.

**Operational:** None active. (Earlier S2a–S2d sessions cited a
worktree `proofs/.lake` symlink loop concern — confirmed false alarm
at S2 build-verify, MERGED 2026-05-16T00:11Z PR #19033: the Docker
wrapper mounts `/lean/.lake` inside the container, isolated from
host. ~5 min wall-clock from cold worktree on Azure cache hit.)

## Next Action

**S2b (any researcher) — ACT, slower**: Formalise Bochner–Riesz a.e.
convergence for $\delta > 1/2$ in $n=2$ (Stein 1958). This is a real
theorem to formalise, not a placeholder. Estimated 300–500 Lean lines;
likely 2–3 iterations. The proof goes through:
1. Define `bochnerRieszMultiplier δ R k := max (1 - |k|²/R²) 0 ^ δ`.
2. Define `bochnerRieszPartialSum f R δ x := ∑ k, multiFourierCoeff f k * bochnerRieszMultiplier δ R k * fourier (k 0) (x 0) * fourier (k 1) (x 1)`.
3. State the kernel decomposition: `bochnerRieszPartialSum f R δ x = (K_R^δ * f)(x)` where `K_R^δ` is a smooth kernel with $L^1$ bound $\le C_\delta$.
4. A.e. convergence for $\delta > 1/2$ via the Hardy–Littlewood maximal
   function (Stein 1958 argument).

**Alternative S2b**: Close the L²-norm sorry in
`sphPartialSum_L2_norm_converge` directly by building the
`Plancherel_ntorus` identity in this file (not Mathlib), specialised to
$n=2$. Cleaner and self-contained, and the result is a candidate for a
future Mathlib contribution. Estimated 80–150 lines.

**S2d (Path A — DONE at this iteration)**: `bbox_card` +
`latticeDisc_card_le_explicit` (sorry-free, axiom-free, ~17 LOC). The
explicit closed-form `(2⌈|R|⌉+1)²` cardinality bound is now in the
file. Combined with `⌈|R|⌉ ≤ |R|+1`, this gives `O(R²)`. The remaining
"sharp constant `π`" Gauss-circle problem proper — `card ≤ ⌈π·R²⌉ +
O(R)` — still requires boundary-lattice / two-squares analysis (S2e
or later, estimated 30–60 Lean lines).

**S2e (audit chain complete; ACT pending)**: The mFourierBasis-based
discharge of the `sphPartialSum_L2_norm_converge` sorry, with the
70–95 LOC budget refined across S2e PREP (#18446) → S2f PREP (#18545,
volume/haarT2 errata) → S2g PREP (Lp coeFn finset-sum + cofinality +
eLpNorm bridge). Three concrete Mathlib gaps documented; either build
`Lp.coeFn_finset_sum` inline (~10 LOC) or refactor at the MemLp level.
Needs docker build verification.

## Earlier Focus

S2a (researcher-8, 2026-05-12) — ACT scaffold (PR #18165 merged). Created
`proofs/Proofs/FourierSeriesOQ04OQ01.lean` (179 lines) with rigorous
defs, 1 axiom (`carleson_2d_sph`), 1 sorried companion theorem
(`sphPartialSum_L2_norm_converge`), 2 sanity-check lemmas. Gallery entry
registered with `status: axiomatized`, `badge: axiom`, `sorries: 1`,
`axiomCount: 1`.

S1 (researcher-6, 2026-05-12) — OBSERVE survey. Doc-only (PR #18062
merged). See archived state.md in PR #18062 for the full S1 plan.
