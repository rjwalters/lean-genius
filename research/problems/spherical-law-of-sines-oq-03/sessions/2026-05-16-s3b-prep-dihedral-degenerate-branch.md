# S3b PREP — `dihedralAngle` definitional-branch case analysis for `spherical_cotangent_rule_polynomial`

**Date**: 2026-05-16
**Researcher**: researcher-12
**Type**: Doc-only PREP (no Lean edits).
**Scope**: Resolve the open question flagged by S3 PREP §4.4 and §6's
"Before opening S3b ACT" gate — *does the polynomial form of the cotangent
rule reduce to `0 = 0 + 0` in the degenerate branches of `dihedralAngle`,
and if so via what case taxonomy?*

**Answer**: yes, but the discharge requires a **three-case split** on
`Real.sin (arcLen X Y) = 0` for each of the three sides `(a, b, c)`, with
**two of the three cases yielding the degeneration directly** and the
**non-degenerate case (`sin a, sin b, sin c` all nonzero)** discharged via
`sin_sq_dihedralAngle` + `spherical_law_of_cosines_local` applied twice.
This PREP lays out the case taxonomy and provides a paste-ready Lean
skeleton with a 4-way `by_cases` split.

## §1 The boxed equation (verbatim, parent line numbering)

```lean
theorem spherical_cotangent_rule_polynomial
    (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.sin (dihedralAngle A B C) * Real.cos (arcLen B C)
        * Real.sin (arcLen A C)
      = Real.sin (arcLen B C) * Real.sin (dihedralAngle A B C)
          * Real.cos (arcLen A C) * Real.cos (dihedralAngle C A B)
        + Real.sin (arcLen B C) * Real.cos (dihedralAngle A B C)
          * Real.sin (dihedralAngle C A B)
```

In informal notation: let
`α := dihedralAngle A B C`,
`γ := dihedralAngle C A B`,
`a := arcLen B C`,
`b := arcLen A C`,
`c := arcLen A B`. Then the equation reads

> **(†)** `sin α · cos a · sin b = sin a · sin α · cos b · cos γ + sin a · cos α · sin γ`.

This is one polynomial form of the classical *four-parts formula* /
cotangent rule (after dividing by `sin a · sin α`, it becomes
`cot a · sin b - cos b · cos γ = sin γ · cot α`, i.e., one of Napier's
six analogies).

## §2 Definitional unfolding of `dihedralAngle`

Parent file `SphericalLawOfSines.lean` line 158:

```lean
noncomputable def dihedralAngle (A B C : Fin 3 → ℝ) : ℝ :=
  let pB := projPerp B A
  let pC := projPerp C A
  if Real.sqrt (normSq pB) = 0 ∨ Real.sqrt (normSq pC) = 0 then 0
  else Real.arccos (dot pB pC / (Real.sqrt (normSq pB) * Real.sqrt (normSq pC)))
```

Two definitional facts (no proofs needed at PREP time, both routine):

* **D1**: `Real.sqrt (normSq pB) = 0 ↔ normSq pB = 0` (because `normSq pB ≥ 0`
  and `Real.sqrt_eq_zero (normSq_nonneg pB)`).
* **D2**: For unit `B, A`: `normSq (projPerp B A) = sin²(arcLen B A) = sin²(c)`
  (parent's `normSq_projPerp_unit B A hB hA` + `arcLen_comm` + `Real.sin_sq_eq_zero_iff`).

So the degenerate branch for `α = dihedralAngle A B C` fires iff
**`sin c = 0` ∨ `sin b = 0`**. And similarly for `γ = dihedralAngle C A B`:
fires iff `sin b = 0 ∨ sin a = 0` (since `projPerp A C` has normSq = sin²(b)
by `arcLen_comm`, and `projPerp B C` has normSq = sin²(a)).

| Vertex | Degenerate when |
|--------|-----------------|
| α (at A) | `sin c = 0 ∨ sin b = 0` |
| γ (at C) | `sin b = 0 ∨ sin a = 0` |

## §3 Case taxonomy on `sin a, sin b, sin c` zero-ness

Eight sign patterns, but only four distinct discharges:

| # | sin a | sin b | sin c | α deg? | γ deg? | Discharge |
|---|-------|-------|-------|--------|--------|-----------|
| 1 | =0    | =0    | =0    | ✓ | ✓ | `sin b = 0` makes LHS factor 0; `sin α = sin γ = 0` makes RHS 0. |
| 2 | =0    | =0    | ≠0    | ✓ | ✓ | Same as #1: `sin b = 0` ⟹ LHS = 0, `sin α = sin γ = 0` ⟹ RHS = 0. |
| 3 | =0    | ≠0    | =0    | ✓ | ✓ | `sin a = 0` ⟹ RHS = 0; `sin α = 0` (α-deg via sin c = 0) and need `sin α · cos a · sin b = 0` — yes, `sin α = 0` works. |
| 4 | =0    | ≠0    | ≠0    | ✗ | ✓ | `sin a = 0` ⟹ RHS = 0. LHS: need `sin α · cos a · sin b = 0`. Use `sin a = 0 ⟹ a ∈ {0, π}` ⟹ `B = ±C`; in either subcase prove `sin α = 0` via `dihedralAngle A B C = dihedralAngle A B B = 0` (B=C, both projPerps equal) or `dihedralAngle A (-B) B = π` (the cosines come out to `−1`). **More complex subcase.** |
| 5 | ≠0    | =0    | =0    | ✓ | ✓ | `sin b = 0` ⟹ LHS = 0. RHS: `sin α = sin γ = 0` ⟹ 0. |
| 6 | ≠0    | =0    | ≠0    | ✓ | ✓ | Same as #5. |
| 7 | ≠0    | ≠0    | =0    | ✓ | ✗ | `sin c = 0` ⟹ α-deg, so `sin α = 0, cos α = 1`. LHS = 0 (factor `sin α`). RHS = `sin a · 0 · ... · cos γ + sin a · 1 · sin γ = sin a · sin γ`. Need `sin γ = 0`. Subcase: `sin c = 0` ⟹ `A = ±B`; in `A = B`, `γ = dihedralAngle C A A = 0` (if-branch fires since `projPerp A C` would appear twice... actually `dihedralAngle C A B` with `A = B`: `projPerp A C` and `projPerp B C = projPerp A C`, neither necessarily 0). Hmm — see §4 below. **More complex subcase.** |
| 8 | ≠0    | ≠0    | ≠0    | ✗ | ✗ | Non-degenerate case. Use `sin_sq_dihedralAngle` + `spherical_law_of_cosines_local` (twice, for sides `b` and `c`) + `lagrange_identity` + algebraic manipulation. **The main work.** |

### Simplification: collapse to three macro-cases

Most rows reduce trivially via `sin b = 0 ⟹ LHS = 0` or `sin α = 0 ⟹ LHS = 0`.
Group as:

* **Macro-case A** (rows 1, 2, 5, 6): `sin b = 0`. LHS = 0 directly
  (factor `Real.sin (arcLen A C)`). RHS: `sin α = sin γ = 0` (both
  degenerate via `sin b = 0`). Equation `0 = 0 + 0`. Discharge in `~4 LOC`.
* **Macro-case B** (rows 3, 4): `sin a = 0 ∧ sin b ≠ 0`. RHS = 0 (factor
  `Real.sin (arcLen B C)` in both terms). LHS: need `sin α · cos a · sin b = 0`.
  Either:
  * (sub-row 3) `sin c = 0` triggers α-deg ⟹ `sin α = 0` ⟹ LHS = 0. `~3 LOC`.
  * (sub-row 4) `sin c ≠ 0`, so `sin a = 0` triggers γ-deg only.
    Need `sin α = 0` via `B = ±C` subcase analysis. **Defer to S3c**
    or use a one-line algebraic identity:
    `Real.sin (arcLen B C) = 0 ⟹ projPerp B C = 0 ∨ projPerp B C = ...`
    is *not* immediate. **Recommendation**: introduce a parent-level helper
    `dihedralAngle_eq_zero_of_sin_arcLen_eq_zero_right (hA : IsUnit3 A)
    (hB : IsUnit3 B) (hC : IsUnit3 C) (h : Real.sin (arcLen B C) = 0) :
    Real.sin (dihedralAngle A B C) = 0`, prove it in the parent (~10-15 LOC)
    and consume it here in 1 LOC. **This is the recommended S3b ACT path.**
* **Macro-case C** (row 7): `sin a, sin b ≠ 0 ∧ sin c = 0`. α-deg via `sin c = 0`
  ⟹ `sin α = 0` ⟹ LHS = 0. RHS = `sin a · sin γ`. Need `sin γ = 0` via
  `A = ±B` subcase. Same shape as sub-row 4. **Same parent-level helper**
  `dihedralAngle_eq_zero_of_sin_arcLen_eq_zero_middle` (or similar).
* **Macro-case D** (row 8): non-degenerate. Main algebraic discharge.

## §4 Why we recommend two parent-level helpers (not in-file case analysis)

Sub-rows 4 and 7 both require unfolding `Real.sin (arcLen X Y) = 0 ⟹
arcLen X Y ∈ {0, π} ⟹ X = ±Y` and then chasing through the `dihedralAngle`
if-branch in a non-obvious way. Doing this inline in
`spherical_cotangent_rule_polynomial` would inflate the proof by 30+ LOC of
case analysis that has nothing to do with the cotangent rule per se.

**Cleaner path**: extract two helper lemmas in the parent
`SphericalLawOfSines.lean` (just below `dihedralAngle_comm_last`, before
`sin_sq_dihedralAngle`):

```lean
/-- If `sin (arcLen B C) = 0` (so `B = ±C`) and `A` is unit, then
    `sin (dihedralAngle A B C) = 0`. -/
theorem sin_dihedralAngle_eq_zero_of_sin_arcLen_third_eq_zero
    (A B C : Fin 3 → ℝ) (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (h : Real.sin (arcLen B C) = 0) :
    Real.sin (dihedralAngle A B C) = 0 := by
  -- Strategy: `Real.sin (arcLen B C) = 0` + parent's `normSq_projPerp_unit`
  -- ⟹ `Real.sin (arcLen B C) ^ 2 = 0` ⟹ `normSq (projPerp C B) = 0` ⟹
  -- ⟹ ⟨B, C⟩² = 1 (via `lagrange_identity` or `normSq_projPerp`).
  -- Then either C = B or C = -B (since both unit). In each subcase,
  -- `projPerp C A = ±projPerp B A`, so `dot (projPerp B A) (projPerp C A) =
  -- ±normSq (projPerp B A) = ±(sqrt normSq pB)²`, hence the arccos argument is
  -- `±1`, hence `arccos = 0 or π`, hence `sin = 0`.
  sorry
```

```lean
/-- If `sin (arcLen A B) = 0` (so `A = ±B`) and `A`, `B`, `C` unit, then
    `sin (dihedralAngle C A B) = 0`. -/
theorem sin_dihedralAngle_eq_zero_of_sin_arcLen_first_two_eq_zero
    (A B C : Fin 3 → ℝ) (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (h : Real.sin (arcLen A B) = 0) :
    Real.sin (dihedralAngle C A B) = 0 := by
  -- Symmetric to the previous helper, but with roles of A and B swapped.
  sorry
```

Both helpers are ~10–15 LOC each and *are* a substantive contribution to
the parent's API. They unblock the S3b ACT in ~25-LOC of clean case analysis
plus the non-degenerate macro-case D.

**Trade-off**: this approach modifies the parent file
`SphericalLawOfSines.lean` (a `verified` gallery proof). The parent's
verification status is unaffected because we add **theorems**, not axioms or
sorries (the helpers themselves must compile cleanly). The parent's
`theoremCount` increments by 2 in meta.json (auditor will catch the drift if
we forget).

**Alternative path** (avoid modifying parent): inline the case analysis into
`SphericalLawOfSinesOQ03.lean` via two `private` helper lemmas with the same
proofs. ~+25 LOC over the parent-modifying path, but keeps the parent file
locked. **Recommended for S3b ACT iteration 1**; if the inline form is too
unwieldy, promote to parent in a later iteration.

## §5 Non-degenerate case (macro-case D, row 8): the algebraic core

When `sin a, sin b, sin c` are all nonzero, both `α` and `γ` are
non-degenerate, so:

```lean
have hpB_pos : normSq (projPerp B A) ≠ 0 := …   -- from sin c ≠ 0
have hpC_pos : normSq (projPerp C A) ≠ 0 := …   -- from sin b ≠ 0
have hpA_pos : normSq (projPerp A C) ≠ 0 := …   -- from sin b ≠ 0 (arcLen comm)
have hpBC_pos : normSq (projPerp B C) ≠ 0 := … -- from sin a ≠ 0
```

Then `sin_sq_dihedralAngle A B C hA hpB_pos hpC_pos` gives
`sin² α = det² / (||pB||² · ||pC||²) = det² / (sin² c · sin² b)`.
And `sin_sq_dihedralAngle C A B hC hpA_pos hpBC_pos` gives
`sin² γ = det² / (||pA_at_C||² · ||pB_at_C||²) = det² / (sin² b · sin² a)`.

Where `det = tripleProduct A B C` (up to swap-sign, see parent's
`tripleProduct_sq_swap`).

The cotangent rule, **squared** (i.e., square both sides of (†) and absorb
sign on the `sin γ` term), becomes a polynomial identity in
`dot A B, dot A C, dot B C, det²`, which is precisely the surface where
`spherical_law_of_cosines_local` operates. The non-degenerate discharge
ought to be:

```lean
-- macro-case D skeleton (non-degenerate)
-- 1. Square both sides:
have h_sq : (LHS - RHS) * (LHS + RHS) = 0 := by
  -- Expand LHS² and RHS², substitute sin² α, sin² γ, sin² _ via
  -- sin_sq_dihedralAngle and sin_sq_arcLen.
  -- The resulting polynomial identity in dot products + det should
  -- close via `linear_combination` over `unit_sum A hA`, `unit_sum B hB`,
  -- `unit_sum C hC`, and the parent's `lagrange_identity` thrice.
  sorry
-- 2. Argue LHS + RHS ≠ 0 (so LHS = RHS follows).
have h_pos : LHS + RHS ≠ 0 := by
  -- Use sin α > 0 and sin γ > 0 in the non-degenerate branch.
  -- Both arccos values are in (0, π), so sin is strictly positive.
  sorry
linarith [h_sq, h_pos]
```

**Warning**: the `(LHS - RHS) * (LHS + RHS) = 0` step is the algebraically
hard step. It is the analog of squaring the law of sines, and it requires
careful sign tracking. Estimated **20–40 LOC** for this step alone, possibly
needing `nlinarith` or `polyrith` after substitution.

**Alternative for macro-case D**: avoid squaring entirely by using
`Real.sin_arccos` and `Real.cos_arccos` on the `dihedralAngle` arccos
arguments, then push everything through `linear_combination` directly on
the un-squared identity. This *might* succeed with the right
`linear_combination` weights but introduces square-root terms; likely
needs `field_simp` + `ring_nf` + manual sign-management. Estimated
**30–50 LOC** if this path works.

## §6 Bearer drift recheck (Mathlib `v4.26.0` / SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Re-pinned via `gh api .../contents/<path>?ref=<sha>` on 2026-05-16:

| Bearer file | File SHA at pin | Used by |
|-------------|-----------------|---------|
| `Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean` | `67fe98d576b76fc0379a6cfe9d9ee00c126663f3` | `Real.sin_arccos`, `Real.cos_arccos` |
| `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` | `93fc1d70f829448208fd4930ac2fcd38ea94b877` | `Real.sin_eq_zero_iff_of_lt_of_lt`, sign lemmas |

Both verified present at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
**0 drift** since S3 PREP (15 bearers, 11 parent + 4 OQ-03 file) and S3a
ACT (same SHA confirmed in S3a's session note).

## §7 Paste-ready Lean skeleton for S3b ACT

```lean
theorem spherical_cotangent_rule_polynomial
    (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.sin (dihedralAngle A B C) * Real.cos (arcLen B C)
        * Real.sin (arcLen A C)
      = Real.sin (arcLen B C) * Real.sin (dihedralAngle A B C)
          * Real.cos (arcLen A C) * Real.cos (dihedralAngle C A B)
        + Real.sin (arcLen B C) * Real.cos (dihedralAngle A B C)
          * Real.sin (dihedralAngle C A B) := by
  -- Set up abbreviations
  set α := dihedralAngle A B C with hα_def
  set γ := dihedralAngle C A B with hγ_def
  set a := arcLen B C with ha_def
  set b := arcLen A C with hb_def
  set c := arcLen A B with hc_def
  -- Three-way case split on sin a, sin b, sin c
  by_cases hsin_b : Real.sin b = 0
  · -- Macro-case A: sin b = 0 ⟹ LHS = 0; sin α = sin γ = 0 (both deg via sin b = 0)
    have hα_zero : Real.sin α = 0 := by
      -- α-deg trigger: normSq (projPerp C A) = sin²(arcLen A C) = sin² b = 0
      -- ⟹ Real.sqrt (normSq (projPerp C A)) = 0
      -- ⟹ dihedralAngle A B C = 0 (if-branch) ⟹ sin = 0.
      sorry  -- ~6 LOC
    have hγ_zero : Real.sin γ = 0 := by
      -- γ-deg trigger: normSq (projPerp A C) = sin²(arcLen C A) = sin² b = 0
      sorry  -- ~6 LOC, symmetric to hα_zero
    rw [hα_zero, hγ_zero, hsin_b]
    ring
  · by_cases hsin_a : Real.sin a = 0
    · -- Macro-case B: sin a = 0 ∧ sin b ≠ 0 ⟹ RHS = 0
      -- LHS: need sin α · cos a · sin b = 0.
      -- Sub-row 3 (sin c = 0): direct α-deg via sin c.
      -- Sub-row 4 (sin c ≠ 0): need parent helper or inline case on B = ±C.
      have hα_zero : Real.sin α = 0 := by
        -- Use the helper `sin_dihedralAngle_eq_zero_of_sin_arcLen_third_eq_zero`
        -- (introduce in parent first, or inline as `private` here).
        sorry  -- ~10 LOC inline, or 1 LOC after parent helper
      rw [hα_zero, hsin_a]
      ring
    · by_cases hsin_c : Real.sin c = 0
      · -- Macro-case C: sin a, sin b ≠ 0 ∧ sin c = 0
        -- ⟹ α-deg via sin c = 0 ⟹ sin α = 0, cos α = 1.
        -- LHS = 0 (sin α factor). RHS = sin a · sin γ.
        -- Need sin γ = 0 via second helper or inline case on A = ±B.
        have hα_zero : Real.sin α = 0 := by sorry -- ~6 LOC
        have hα_cos_one : Real.cos α = 1 := by sorry -- ~3 LOC after hα_zero
        have hγ_zero : Real.sin γ = 0 := by
          -- helper: sin_dihedralAngle_eq_zero_of_sin_arcLen_first_two_eq_zero
          sorry  -- ~10 LOC inline, or 1 LOC after parent helper
        rw [hα_zero, hα_cos_one, hγ_zero]
        ring
      · -- Macro-case D: non-degenerate.
        -- sin a, sin b, sin c all nonzero ⟹ α, γ both non-degenerate.
        -- This is the algebraic core. See §5 for the strategy.
        sorry  -- ~20-40 LOC (the hard part)
```

## §8 LOC + risk estimate

| Macro-case | LOC | Risk | Notes |
|------------|-----|------|-------|
| A (`sin b = 0`) | ~14 LOC | low | Two direct `dihedralAngle` if-branch unfoldings + `ring`. |
| B (`sin a = 0, sin b ≠ 0`) | ~12 LOC + helper | moderate | Helper is `~10 LOC` inline or 1 LOC w/ parent extraction. |
| C (`sin c = 0, sin a sin b ≠ 0`) | ~18 LOC + helper | moderate | Symmetric to B. |
| D (non-degenerate) | ~25-45 LOC | very high | The algebraic core; needs `linear_combination` or `polyrith`. |
| **Total** | **~70-100 LOC** | **high** | Without parent helpers; ~50-70 LOC with them. |

## §9 S3b ACT readiness gate

Before opening S3b ACT:

- [x] Macro-case taxonomy verified (§3 above).
- [x] Bearer drift recheck — 0 drift at SHA `2df2f0150c`.
- [x] Paste-ready skeleton for all four macro-cases (§7).
- [ ] **Decision needed**: parent-helper path vs inline-helper path for
      macro-cases B and C. **Recommended**: inline-helper for S3b ACT iter 1
      (keeps parent file locked); promote to parent in S3c if cleanup is
      warranted.
- [ ] **Build smoke-test before push**: `docker-build.sh Proofs.SphericalLawOfSinesOQ03`
      on base SHA, confirm baseline 3061 jobs / 1 strategic sorry remains.
- [ ] **Sibling PR sweep**: `gh pr list --search "spherical-law-of-sines-oq-03 in:title" --state open` — confirm 0 open PRs.

## §10 What this PREP does NOT do

* Does **not** modify `proofs/Proofs/SphericalLawOfSinesOQ03.lean` or the
  parent `SphericalLawOfSines.lean`.
* Does **not** introduce parent helpers (deferred to S3b ACT iteration 1's
  inline form; promotion to parent is S3c).
* Does **not** attempt the non-degenerate macro-case D algebra — that is
  S3b ACT's main work.
* Does **not** advance the iteration counter (PREP is iteration-neutral).

## §11 Conflict-free guarantees

Files touched:

1. `research/problems/spherical-law-of-sines-oq-03/sessions/2026-05-16-s3b-prep-dihedral-degenerate-branch.md` (this file, NEW).
2. `research/problems/spherical-law-of-sines-oq-03/state.md` (UPDATE: phase line + next-action refresh + attempt count bump).
3. `src/data/research/problems/spherical-law-of-sines-oq-03.json` (UPDATE: lastUpdated + nextSteps).

**No Lean source modified**. No new sorries. The skeleton in §7 is paste-ready
for S3b ACT but is not itself committed as Lean.

## §12 References

* PR #19340 (S3 PREP), PR #19388 (S3a ACT) — predecessors on this slug.
* Parent file `proofs/Proofs/SphericalLawOfSines.lean` lines 158–215
  (`dihedralAngle` def + `sin_sq_dihedralAngle`).
* `feedback_researcher_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open.md`
  — guidance on PREP-then-ACT cadence when the predecessor PREP names the
  follow-on explicitly (S3 PREP §4.4 named this S3b PREP).
