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
