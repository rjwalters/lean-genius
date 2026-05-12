# S6 PREP — Discharging `cauchy_diag_norm_bound_at_radius`

**Date**: 2026-05-12
**Researcher**: researcher-8
**Phase**: PREP (scoping for S6 — does not modify the Lean file)
**Conditional on**: PR #18197 (S5 ACT) merging. S5 isolates the single
residual `sorry` to `cauchy_diag_norm_bound_at_radius` and proves the
limit-extraction step `cauchy_diag_norm_bound` in full.

This document does **not** propose Lean changes. It surveys the Mathlib
hooks needed by a future S6 ACT iteration so that the implementer can
pick the right tactic chain on the first try and avoid the v4.26.0
lemma-name drift that the file's various docstrings have accumulated.

## 1. The S6 target (post-S5 file state)

After PR #18197 lands, the single open `sorry` is on:

```lean
theorem cauchy_diag_norm_bound_at_radius
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (_hR : 0 < R) (_hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (_hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (_hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (k : ℕ) (w : ℂ) (r' : ℝ) (_hr' : 0 < r') (_hr'R : r' < R) :
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k
```

i.e. the **finite-radius Cauchy diagonal-coefficient estimate**: for
each strict intermediate radius `r' ∈ (0, R)`, the multilinear
coefficient `p k`, evaluated on the diagonal vector `(w, …, w)`, is
bounded above by `M · (‖w‖ / r')^k`.

The limit step `r' → R⁻` (boundary-form bound) is already proven in
S5 (`cauchy_diag_norm_bound`), so S6 has no limit plumbing to do.

## 2. Candidate Mathlib lemma names — drift survey

This file's various docstrings (Iter 1 / S2 / §3a / S5) name **at
least seven distinct Mathlib lemma identifiers** for the finite-radius
Cauchy chain. They do not all agree, and some may not be the exact
v4.26.0 spelling. S6 starts here:

| # | Lemma identifier cited                                                | Cited in              | Role                                                       | Status                                  |
|---|-----------------------------------------------------------------------|-----------------------|------------------------------------------------------------|-----------------------------------------|
| 1 | `HasFPowerSeriesOnBall.uniform_geometric_approx'`                     | S1 docstring, line 70 | partial-sum residual, geometric                            | ✅ used at line 595 (S2, proven)        |
| 2 | `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`        | S1 docstring, line 71 | per-coefficient bound from radius                          | unverified (no other in-tree use)       |
| 3 | `HasFPowerSeriesOnBall.factorial_smul_apply_iteratedFDeriv`           | S1 docstring, l. 120  | bridge `p k` ↔ `iteratedFDeriv k f a`                      | unverified (likely renamed in v4.26.0)  |
| 4 | `Complex.norm_cauchyPowerSeries_le`                                   | §3a docstring, l. 562 | per-coefficient bound on closed sphere                     | unverified (no other in-tree use)       |
| 5 | `DifferentiableOn.hasFPowerSeriesOnBall`                              | §3a docstring, l. 563 | hypothesis upgrade `holomorphic` ⇒ `HasFPowerSeriesOnBall` | unverified (no other in-tree use)       |
| 6 | `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`          | S5 PR #18197 docstring| Cauchy integral bound on `iteratedDeriv k f a`             | unverified (no other in-tree use)       |
| 7 | `HasFPowerSeriesOnBall.factorial_smul`                                | S5 PR #18197 docstring| likely abbreviation of #3 above                            | unverified (likely same as #3)          |
| 8 | `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`                      | S5 PR #18197 docstring| 1D collapse `iteratedFDeriv = w^k · iteratedDeriv`         | unverified                              |
| ★ | **`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`**    | sibling, not this file| bridge `p k` ↔ `iteratedFDeriv k f a` via `Perm`-sum       | ✅ battle-tested in `TaylorTheoremOQ02.lean:93`, v4.26.0 |

**Finding**: only #1 has been actually invoked in this file's proven
content. Identifier ★ (not previously cited in this file's
docstrings) is the **battle-tested in-repo** analog at v4.26.0 of
identifier #3/#7 — see `TaylorTheoremOQ02.lean:88–104` for a working
proof that uses ★ to relate `p n (fun _ ↦ 1)` to
`iteratedDeriv n f x₀ / n!`. S6 should plan to use ★ as the bridge,
**not** #3 or #7 as cited in the S5 PR docstring.

## 3. Recommended proof outline for S6

Using the battle-tested bridge ★ and the standard Cauchy integral
formula, the proof of `cauchy_diag_norm_bound_at_radius` decomposes
into three substeps:

### Step (a) — Sub-disk inclusion: `f` is bounded by `M` on `sphere a r'`

The hypothesis `_hbound` gives `‖f z‖ ≤ M` for `z ∈ Metric.ball a R`.
For `r' < R`, the closed sphere `Metric.sphere a r'` is contained in
the open ball `Metric.ball a R` (since `dist z a = r' < R`). Hence

```lean
have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := by
  intro z hz
  have : z ∈ Metric.ball a R := by
    rw [Metric.mem_ball, ← Metric.mem_sphere.mp hz]
    exact _hr'R
  exact _hbound z this
```

Tactic cost: ~6 lines.

### Step (b) — Cauchy integral bound on `iteratedDeriv k f a`

This is the **only step that genuinely depends on Mathlib's complex
Cauchy infrastructure**. Two Mathlib candidates from the survey:

- **Option (b.i)**: `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
  (cited in S5 PR docstring #18197). If it exists at v4.26.0 under
  that exact name, it produces

  ```
  ‖iteratedDeriv k f a‖ ≤ k! · M / (r')^k
  ```

  directly from `h_sphere_bound`. Estimated cost if it exists: ~3 lines.

- **Option (b.ii)**: `Complex.norm_cauchyPowerSeries_le` (cited in §3a
  docstring). If it exists, it likely produces a related bound on
  `p k` directly rather than on `iteratedDeriv k f a`, which (if true)
  would skip step (c) entirely.

**S6 first action**: at the start of the session, `#check
@Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` and
`#check @Complex.norm_cauchyPowerSeries_le` in the file. The
first that succeeds is the one to use. If neither does, fall back to
manually constructing the bound from `cauchyIntegral` + the integral
ML-inequality (heavier; ~30 lines).

### Step (c) — Bridge `p k` ↔ `iteratedFDeriv k f a` (1D collapse)

Using ★ as in `TaylorTheoremOQ02.lean:88–104`, for any constant vector
`(w, w, …, w) : Fin k → ℂ`:

```lean
have key := _hf.iteratedFDeriv_eq_sum_of_completeSpace
              (v := fun _ : Fin k => w)
-- key : iteratedFDeriv ℂ k f a (fun _ ↦ w)
--         = ∑ σ : Perm(Fin k), p k (fun i ↦ (fun _ ↦ w) (σ i))
simp only [Function.const_apply] at key
rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    nsmul_eq_mul] at key
-- key : iteratedFDeriv ℂ k f a (fun _ ↦ w) = ↑(k !) * p k (fun _ ↦ w)
```

Now use **`iteratedDeriv_eq_iteratedFDeriv`** (already used in
`TaylorTheoremOQ02.lean:101`) and the 1D multilinear-evaluation
identity `(iteratedFDeriv k f a) (fun _ ↦ w) = w^k * iteratedDeriv k f a`
(which is `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` per the S5
docstring, but may have a different name at v4.26.0 — verify with
`#check`).

Equate magnitudes:

```
‖p k (fun _ ↦ w)‖ = ‖iteratedFDeriv k f a (fun _ ↦ w)‖ / k!
                   = ‖w‖^k · ‖iteratedDeriv k f a‖ / k!
                   ≤ ‖w‖^k · (k! · M / (r')^k) / k!     -- step (b)
                   = M · (‖w‖ / r')^k
```

Estimated cost: ~30 lines (the multilinear/norm bookkeeping is what
makes this the longest part).

### Total budget

- Step (a): 6 lines
- Step (b): 3–30 lines (best case 3 with ready-made Cauchy lemma)
- Step (c): 30 lines
- Total: **40–70 lines** if Mathlib's Cauchy infrastructure cooperates.

This matches the S5 PR's "Estimated 60–100 lines" estimate, with the
lower bound reflecting the existence of a ready-made Cauchy lemma.

## 4. Risks and pre-flight verifications

Before writing tactic blocks, the S6 implementer should run these
`#check` probes in the file:

```lean
#check @Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
#check @Complex.norm_cauchyPowerSeries_le
#check @HasFPowerSeriesOnBall.factorial_smul_apply_iteratedFDeriv
#check @iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
#check @FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius
```

For each that fails ("unknown constant"), use Mathlib's `loogle`,
`exact?`, or grep the v4.26.0 source for the renamed analog. The
most likely-to-have-drifted are #3 and #7 (the `factorial_smul`
variants); the most likely-to-exist-as-named are #6 (a very specific
Cauchy lemma name) and #1 (already confirmed in-tree).

**Pinned Mathlib v4.26.0 commit**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(see `proofs/lake-manifest.json`).

## 5. Coordination with in-flight PRs

| PR     | State | Touches                                                     |
|--------|-------|-------------------------------------------------------------|
| #18197 | OPEN  | S5 ACT — proves `cauchy_diag_norm_bound` via limit-extract  |
| #17904 | OPEN  | older S2 ACT (predates S3 merge, conflicting per S4 note)   |

This S6 PREP is **strictly orthogonal** to both:

- Touches only the new file `research/problems/.../sessions/2026-05-12-s6-prep-cauchy-finite-radius.md`.
- Does not touch `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`,
  `knowledge.md`, `state.md`, the per-slug JSON, or any `meta.json`.
- Builds on the *anticipated* post-S5 file state (one residual sorry
  on `cauchy_diag_norm_bound_at_radius`). If S5 does not merge as-is
  the recommendations in §3 still apply with `cauchy_diag_norm_bound`
  in place of `cauchy_diag_norm_bound_at_radius` — the underlying
  Mathlib chain is identical.

## 6. Why this is a prep iteration, not a SCAFFOLD

A SCAFFOLD would commit a partial `sorry`-bearing replacement of the
target theorem to the Lean file. S6 cannot do that without S5 first
merging (which would then require a rebase). Instead this prep
iteration:

- consolidates the scattered Mathlib lemma-name candidates into one
  decision table (§2);
- identifies one cross-file battle-tested analog ★ that the file's own
  docstrings do not mention;
- gives a step-by-step proof plan (§3) keyed to the existing v4.26.0
  state of the codebase;
- enumerates the pre-flight `#check` probes (§4) that the S6 ACT
  session should run first.

## 7. Next concrete S6 ACT moves

1. Wait for PR #18197 (S5 ACT) to merge.
2. Rebase against `origin/main`.
3. Run the §4 `#check` probes; classify each cited Mathlib name as
   ✅ exists / ❌ drifted / ⚠️ renamed (and find the rename).
4. Pick the best Cauchy-bound route from §3 step (b) based on what
   exists.
5. Implement steps (a)–(c) on the lines of `TaylorTheoremOQ02.lean`'s
   `fps_coeff_eq_taylor_coeff`.
6. Verify with `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01`.

If steps 3–4 reveal that the Cauchy lemma chain has drifted
substantially in v4.26.0, the alternative bound via
`HasFPowerSeriesOnBall.uniform_geometric_approx'` (identifier #1,
already used in this file's S2 proof) can be used to *upper-bound the
diagonal coefficient* by extracting a single-term subsum from the
geometric residual estimate — at the cost of a worse constant.

---

**Word count**: ~1500. Pure prep / no Lean source touched.
