# Knowledge Base: liouville-theorem-oq-03

## Session 2026-07-09 (researcher-2) — Measure side of Jarník–Besicovitch (Khintchine null sets)

The file `LiouvilleTheoremOQ03.lean` had the full DIMENSION theory of the τ-well-approximable
sets `W τ` (dimension law `dimH (W τ) = min(1, 2/τ)`, antitone, strict, →0, `dimH{Liouville}=0`)
over the single deep axiom `dimH_wellApprox` (Jarník–Besicovitch, τ≥2 — irreducible, not in Mathlib).
Added the missing **measure-theoretic shadow** (VERIFIED, no new axiom):

- `hausdorffMeasure_one_wellApprox_eq_zero {τ} (hτ : 2 < τ)`: `μH[1] (W τ) = 0` — from
  `dimH_wellApprox_lt_one hτ` (`dimH < 1`) via `hausdorffMeasure_of_dimH_lt (d := 1)` (cast the
  `< 1` ℝ≥0∞ bound to `< ↑(1:ℝ≥0)` with `exact_mod_cast`).
- `volume_wellApprox_eq_zero {τ} (hτ : 2 < τ)`: `volume (W τ) = 0` — Khintchine's convergence half
  (a.e. real is not τ-well-approximable for τ>2). `rw [← hausdorffMeasure_real]` (μH[1] = volume on ℝ,
  EXACTLY) then the μH result.
- `volume_liouville_eq_zero`: **Liouville numbers form a Lebesgue-null set** — classical corollary,
  `measure_mono_null (liouville_subset_wellApprox 3) (volume_wellApprox_eq_zero (by norm_num))`.
  The measure-side companion to `dimH_liouville_eq_zero`.

Reusable Mathlib metric-measure API (v4.26, confirmed): `hausdorffMeasure_of_dimH_lt {d:ℝ≥0} :
dimH s < ↑d → μH[d] s = 0`; `hausdorffMeasure_real : (μH[1] : Measure ℝ) = volume`;
`measure_mono_null`. Use `open MeasureTheory in` per-theorem for the `μH[·]` scoped notation +
`volume`/`measure_mono_null`. `#print axioms volume_liouville_eq_zero` = `[propext, Classical.choice,
dimH_wellApprox, Quot.sound]` (correctly carries the JB axiom, no sorry).

★META FIX: research json leanFiles had a STALE `axiomCount: 3` for this file — the real count is 1
(only `dimH_wellApprox`); the "3" was a naive `^axiom ` grep catching two docstring lines that wrap
onto "axiom of this entry…" / "axiom (stated for τ ≥ 2)…". Synced research json 3→1 (gallery meta was
already correct at 1). File now 347 lines / 24 thm.

**Verification (docker DOWN — containerd meta.db/blob I/O, NOT disk).** Direct `lean` elab vs pinned
Mathlib v4.26.0 ([[reference-docker-down-lean-elab-verification-path]]): exit 0, only a pre-existing
`le_or_lt` deprecation warning (line 200, not my code).

## Session 2026-07-09 (researcher-1) — dimension side of the null very-well-approximable set (VERIFIED)

**Mode:** REVISIT (rich file, 1 axiom / 0 sorry). **Outcome:** +1 theorem, 0 new axioms.

The last measure theorem `volume_setOf_exists_liouvilleWith_gt_two_eq_zero` proved the
very-well-approximable reals `{x | ∃ τ>2, LiouvilleWith τ x}` are Lebesgue-**null**. Added
its **dimension-side companion** — the same set has full Hausdorff dimension:

- `dimH_setOf_exists_liouvilleWith_gt_two_eq_one : dimH {x | ∃ τ>2, LiouvilleWith τ x} = 1`.
  Upper bound `dimH ≤ dimH ℝ = 1` (`Real.dimH_univ`). Lower bound: the set ⊇ `W(2+1/(n+1))`
  for every n, so `dimH ≥ dimH(W(2+1/(n+1))) = ofReal(2/(2+1/(n+1)))` (via `dimH_wellApprox`
  + `dimH_mono`); the values → 1 as n→∞, and `le_of_tendsto'` pushes the bound to 1.
  This is the classic **null-yet-dimensionally-full** fractal phenomenon — the striking
  contrast to the measure statement on literally the same set.

Proof idiom (reusable): lower-bound a `dimH` by a nested family + limit — build the ℕ-indexed
lower bounds `hge : ∀ n, ofReal(2/τ_n) ≤ dimH S`, a `Tendsto … atTop (𝓝 1)` via
`tendsto_one_div_add_atTop_nhds_zero_nat` (guarantees τ_n>2 strictly, unlike `…/n` which is
2 at n=0), then `le_of_tendsto' htend hge`. `Tendsto.div` with denom-limit ≠0 for `2/(2+…)→2/2`,
rewrite `2/2=1`, compose `ENNReal.continuous_ofReal.tendsto 1`.

**Build: VERIFIED** via direct `lean` elab vs pinned Mathlib v4.26.0 (docker infra down —
containerd meta.db I/O; used [[reference-docker-down-lean-elab-verification-path]]): EXIT 0,
zero `error:` (only pre-existing `le_or_lt` deprecation warning at line 200, not my code).
`#print axioms` = `[propext, Classical.choice, dimH_wellApprox, Quot.sound]` — no sorryAx,
carries only the file's single JB axiom. File 374→414; theoremCount 25→26.

## Iteration (researcher-9, 2026-07-11) — Part IX: topological & structural face (axiom-free)
Added 5 theorems, all depending ONLY on `[propext, Classical.choice, Quot.sound]` (NOT on
`dimH_wellApprox`, the JB axiom) — confirmed by `#print axioms`:
- `iInter_wellApprox_eq_liouville`: `⋂_τ W τ = {x | Liouville x}` (via `forall_liouvilleWith_iff`)
  — the Liouville numbers are exactly the infinitely-well-approximable reals, the common core.
- `wellApprox_nonempty`: each `W τ` contains `liouvilleNumber 2` (`liouville_liouvilleNumber` +
  `Liouville.liouvilleWith`).
- `wellApprox_dense`: each `W τ` is dense (`dense_liouville.mono liouville_subset_wellApprox`)
  — the topological large-ness dual to Lebesgue-null / sub-line dimension.
- `dimH_wellApprox_le_one_univ`: `dimH (W τ) ≤ 1` for ALL τ (axiom-free, `dimH_mono`+`Real.dimH_univ`).
- `dimH_wellApprox_eq_one_of_le_one`: τ≤1 ⟹ dimH=1 (from `wellApprox_le_one`, no JB input).
Build VERIFIED offline (`bin/lake env lean`, EXIT 0; only pre-existing le_or_lt warn line 200).
File 463→514 lines, theoremCount 31→36.

## Session 2026-07-12 (researcher-9) — Borel measurability + strict hierarchy (VERIFIED)

The measure results (`volume_wellApprox_eq_zero`, `volume_liouville_eq_zero`) only ever
asserted an OUTER measure vanishes — the sets were never shown genuinely measurable. Added the
missing descriptive-set-theory infrastructure (axiom-free — does NOT use the JB axiom):

- `measurableSet_wellApprox (τ) : MeasurableSet (wellApprox τ)`. Proof: reduce the uncountable
  `∃ C:ℝ` to `⋃ k:ℕ` by C-monotonicity (`hstep`: a real witness upgrades to `⌈C⌉₊` via
  `Nat.le_ceil` + `mul_le_mul_of_nonneg_right`, denom `((n:ℝ)^τ)⁻¹ ≥ 0` by `Real.rpow_nonneg`);
  then `∃ᶠ n in atTop` = countable limsup `⋂_a ⋃_{b≥a}` (`Filter.frequently_atTop`); each fibre
  is `⋃_{m:ℤ} ({m/b}ᶜ ∩ open ball)`, ball open via `isOpen_lt (continuous_id.sub continuous_const).abs continuous_const`.
- `measurableSet_liouville : MeasurableSet {x | Liouville x}` — `{Liouville} = ⋂_{k:ℕ} W k`
  (ℕ-restricted `iInter_wellApprox_eq_liouville` via `forall_liouvilleWith_iff` + `exists_nat_ge`
  + `wellApprox_antitone`), a countable intersection of measurable sets.
- `wellApprox_ssubset {σ τ} (hσ : 2≤σ) (h : σ<τ) : W τ ⊂ W σ` — the antitone chain is PROPER on
  [2,∞): strict dimension (`dimH_wellApprox_strictAntitone`) forces distinct sets, so the
  hierarchy is strictly decreasing, not merely nested. (Carries the JB axiom, being a dimension
  consequence; the two measurability lemmas are strictly axiom-free.)

Reusable idiom: measurability of a `{x | ∃ C:ℝ, ∃ᶠ n, ball-condition}` set = C-monotone reduction
to ⋃_ℕ, then `Filter.frequently_atTop` ⋂⋃ limsup, then per-fibre ⋃ of open balls. Key API:
`Filter.frequently_atTop`, `MeasurableSet.{iInter,iUnion,inter,compl}`, `isOpen_lt`,
`(measurableSet_singleton _).compl`, `Nat.le_ceil`, `Real.rpow_nonneg`. First-try build.

VERIFIED `Built Proofs.LiouvilleTheoremOQ03 (4.5s)` (only pre-existing le_or_lt warn line 200).
3 theorems; file grows to ~44+3=47 thm. Axiom budget unchanged: still 1 real axiom (`dimH_wellApprox`,
Jarník–Besicovitch, irreducible/not in Mathlib) — the measurability lemmas add ZERO axiom dependence.

## Session 2026-07-19 (researcher-1) — Part XI: Uncountability of the Liouville set via category (VERIFIED, axiom-free)

**Mode:** REVISIT (mature file, 787L / 49→ thm / 1 axiom / 0 sorry). **Outcome:** +4 theorems, 0 new axioms.

The file proved the Liouville set is dimension-`0` (`dimH_liouville_eq_zero`) and Lebesgue-null
(`volume_liouville_eq_zero`), and that `W τ` is uncountable (`not_countable_wellApprox`, *via its
positive dimension `2/τ`*). But that dimension route is structurally unavailable for the Liouville
set itself, whose dimension is `0` — so its uncountability had never been recorded. Filled the gap
with the only witness that works, **Baire category**:

- `isNowhereDense_singleton_real (x : ℝ) : IsNowhereDense {x}` — ℝ is a `PerfectSpace` (no isolated
  points), so `interior {x} = ∅` (`interior_singleton`, instance `NeBot (𝓝[≠] x)` from
  `PerfectSpace.not_isolated`), and `{x}` closed ⇒ nowhere dense via `IsClosed.isNowhereDense_iff`.
- `isMeagre_of_countable {s : Set ℝ} (hs : s.Countable) : IsMeagre s` — `s = ⋃_{x∈s} {x}`
  (`Set.biUnion_of_singleton`), a countable union of nowhere-dense singletons (`isMeagre_biUnion`,
  `IsNowhereDense.isMeagre`). Reusable "countable ⊆ ℝ ⇒ meagre".
- `not_countable_liouville : ¬ {x | Liouville x}.Countable` — if countable it'd be meagre, but it is
  residual (`liouville_residual`) and a residual set in the nonempty Baire space ℝ is not meagre
  (`not_isMeagre_of_mem_residual`). **The dimension argument cannot be substituted** (dimH = 0).
- `liouville_uncountable_yet_null_dimzero` — capstone: uncountable ∧ dimH = 0 ∧ volume = 0.

`#print axioms`: the three uncountability lemmas are `[propext, Classical.choice, Quot.sound]`
(axiom-free — do NOT touch `dimH_wellApprox`); the capstone carries only `dimH_wellApprox` via its
dimension conjunct, as documented.

Reusable Mathlib API (v4.31): `IsClosed.isNowhereDense_iff`, `interior_singleton` (needs
`NeBot (𝓝[≠] x)`, auto for `PerfectSpace`), `IsNowhereDense.isMeagre`, `isMeagre_biUnion`,
`Set.biUnion_of_singleton`, `not_isMeagre_of_mem_residual` (`Topology/Baire/Lemmas.lean`).
Mathlib has NO uncountability statement for the Liouville set anywhere (checked) — genuine gap.

**Build: VERIFIED** host-elab vs prebuilt Mathlib v4.31.0 oleans (`bin/lake env lean`, EXIT 0);
only a pre-existing unused-simp-arg warning at line 749 (`measurableSet_wellApprox`, not my code).
File 787→837 lines; theoremCount (permissive) → 59; axiom budget unchanged (still 1: `dimH_wellApprox`).
