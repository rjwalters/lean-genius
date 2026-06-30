# 2026-06-19 (s2) — researcher-12 — Fubini-assembly crux hand-proved (verification blocked)

**Mode**: REVISIT (continue prior KL-form scaffold)
**Outcome**: progress — sole `sorry` discharged in source; build verification blocked.

## State on wake
- Branch `research/shannon-channel-coding-oq01-kl-mutual-information`; PR #26169
  (the `[build-pending]` scaffold WITH the sorry) was already **MERGED to main**.
- Sole `sorry` at `ShannonChannelCodingOQ01OQ01.lean:131`, in
  `additive_kl_eq_entropy_difference` (the Fubini assembly).
- Prior Aristotle project **a6e50bb5** → `Resource not found` (gone; last session's
  connection was interrupted).

## Aristotle OUTAGE
Resubmission failed: both MCP `prove` and the uv CLI `aristotle prove-from-file`
return **HTTP 404 on `POST https://aristotle.harmonic.fun/api/v1/project?project_type=2`**.
Service-side outage, not project expiry. Delegation unavailable this session.

## What I did — hand-proved the crux
Could not delegate, so proved the Fubini assembly manually. Key idea: work at the
**product-measure level** to avoid per-`x` integrability (we only have *joint*
integrability hypotheses). Pointwise `K = N − O` (split the log); flatten each
iterated integral to a product integral via `integral_prod` (justified by the joint
hyps `hnoise_int`, `houtput_int`, and `hK_int := (hnoise_int.sub houtput_int).congr`);
split with `integral_sub`; collapse NOISE → `−h(Z)` (inner = `noise_logterm_integral`,
average against `f_X`, `hX_sum`) and OUTPUT → `−h(Y)` (`integral_integral_swap`, inner
= `output_logterm_integral` via marginalisation). Result `−h(Z) − (−h(Y)) = h(Y)−h(Z)`.

### Exact proof body now in the source (replaces the sorry)
```lean
  have hsplit : ∀ x y, additiveKLIntegrand fX fZ fY x y
      = fX x * fZ (y - x) * Real.log (fZ (y - x))
        - fX x * fZ (y - x) * Real.log (fY y) := by
    intro x y
    unfold additiveKLIntegrand
    rw [Real.log_div (ne_of_gt (hZ_pos (y - x))) (ne_of_gt (hY_pos y)), mul_sub]
  have hK_int : Integrable
      (fun p : ℝ × ℝ => additiveKLIntegrand fX fZ fY p.1 p.2) := by
    apply (hnoise_int.sub houtput_int).congr
    filter_upwards with p
    rw [hsplit p.1 p.2]
  have eN : (∫ x, ∫ y, fX x * fZ (y - x) * Real.log (fZ (y - x)))
      = ∫ p : ℝ × ℝ, fX p.1 * fZ (p.2 - p.1) * Real.log (fZ (p.2 - p.1)) :=
    (MeasureTheory.integral_prod _ hnoise_int).symm
  have eO : (∫ x, ∫ y, fX x * fZ (y - x) * Real.log (fY y))
      = ∫ p : ℝ × ℝ, fX p.1 * fZ (p.2 - p.1) * Real.log (fY p.2) :=
    (MeasureTheory.integral_prod _ houtput_int).symm
  have eK : additiveMutualInformationKL fX fZ fY
      = ∫ p : ℝ × ℝ, additiveKLIntegrand fX fZ fY p.1 p.2 := by
    rw [additiveMutualInformationKL]
    exact (MeasureTheory.integral_prod _ hK_int).symm
  have hKsplit : (∫ p : ℝ × ℝ, additiveKLIntegrand fX fZ fY p.1 p.2)
      = (∫ p : ℝ × ℝ, fX p.1 * fZ (p.2 - p.1) * Real.log (fZ (p.2 - p.1)))
        - (∫ p : ℝ × ℝ, fX p.1 * fZ (p.2 - p.1) * Real.log (fY p.2)) := by
    rw [← MeasureTheory.integral_sub hnoise_int houtput_int]
    apply integral_congr_ae
    filter_upwards with p
    exact hsplit p.1 p.2
  have noise : (∫ p : ℝ × ℝ, fX p.1 * fZ (p.2 - p.1) * Real.log (fZ (p.2 - p.1)))
      = - differentialEntropy fZ := by
    rw [← eN]
    have hinner : ∀ x, (∫ y, fX x * fZ (y - x) * Real.log (fZ (y - x)))
        = (- differentialEntropy fZ) * fX x := by
      intro x
      have hc : (∫ y, fX x * fZ (y - x) * Real.log (fZ (y - x)))
          = ∫ y, (fZ (y - x) * Real.log (fZ (y - x))) * fX x := by
        apply integral_congr_ae; filter_upwards with y; ring
      rw [hc, integral_mul_const, noise_logterm_integral]
    simp_rw [hinner]
    rw [integral_const_mul, hX_sum, mul_one]
  have output : (∫ p : ℝ × ℝ, fX p.1 * fZ (p.2 - p.1) * Real.log (fY p.2))
      = - differentialEntropy fY := by
    rw [← eO]
    have hswap : (∫ x, ∫ y, fX x * fZ (y - x) * Real.log (fY y))
        = ∫ y, ∫ x, fX x * fZ (y - x) * Real.log (fY y) :=
      MeasureTheory.integral_integral_swap houtput_int
    rw [hswap]
    have hinner : ∀ y, (∫ x, fX x * fZ (y - x) * Real.log (fY y))
        = fY y * Real.log (fY y) := fun y =>
      output_logterm_integral fX fZ fY y (hmarg y)
    simp_rw [hinner]
    rw [differentialEntropy, neg_neg]
  rw [eK, hKsplit, noise, output]
  ring
```

## Status: UNVERIFIED
Build gate CLOSED at session end: host load ~15.8 (rising), 6 docker containers,
~21 MB truly free. Did NOT docker-build (CLAUDE.md memory-crash policy) and did NOT
commit/push unverified code. Proof lives in the worktree only.

## Suspected first-build failure points (if red)
1. `integral_prod` / `integral_integral_swap`: `volume` vs `volume.prod volume`
   defeq on `ℝ × ℝ` — if elaboration balks, `rw [← MeasureTheory.volume_eq_prod]`
   the joint hyps or wrap with `(MeasureTheory.volume_eq_prod ℝ ℝ ▸ h…)`.
2. `integral_const_mul` lemma name (the left-constant pull in `noise`). Sibling
   confirms `integral_mul_const` exists; if `integral_const_mul` is missing, reorder
   `hinner` to `fX x * (…)` and use `integral_mul_const` + `hX_sum` + `one_mul`.
3. `simp_rw [hinner]` rewriting under the `∫ x,`/`∫ y,` binder — if it fails, use
   `integral_congr_ae` + `filter_upwards`.

## Next session
1. `aristotle ... ` 404? if cleared, can resubmit `/tmp/ShannonKLCrux.lean` as backup.
2. When gate opens (load<6): `./proofs/scripts/docker-build.sh Proofs.ShannonChannelCodingOQ01OQ01`.
3. Green ⇒ new branch off `origin/main`, commit the file, flip meta
   `status formalized→verified`, drop `[build-pending]`, open completion PR, graduate.
