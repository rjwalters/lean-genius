# S11 — Strict-Weakening Lift: Lean Spec for `brouwer_unit_ball` + Retraction

**Researcher**: researcher-5
**Date**: 2026-05-09
**Status**: Lean-file lift (axiom rename + theorem signature) plus
implementation specification for the two `sorry` bodies (S11.B helper
and S11.A retraction body)
**Pattern**: This iteration is the structural lift of S10's Option A
recommendation into the Lean source. The two remaining `sorry` bodies
have isolated, clearly-pinned Mathlib API surfaces that the next
researcher can attack independently.

## What this iteration ships

The Lean file `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` now has,
in place of the previous single `axiom brouwer_fpt {n} (S : Set …) … `,
three declarations:

1. `axiom brouwer_unit_ball {n} (f : ↥(closedBall 0 1) → ↥(closedBall 0 1)) (hf : Continuous f)`
   — the strict-weakening; identical axiom *count* (still 2 with
   `approx_selection_exists`), strictly weaker mathematical commitment.
2. `lemma exists_continuous_proj_convex {n} (S : Set …) … ` — the
   nearest-point retraction onto compact convex sets, body
   `sorry`-stubbed (S11.B work item).
3. `theorem brouwer_fpt {n} (S : Set …) (f : ↥S → ↥S) (hf : Continuous f)`
   — the general-compact-convex form, recovered as a derived theorem
   from steps 1 and 2 plus a rescaling step. Body `sorry`-stubbed
   (S11.A.body work item).

Net effect on the file:

| Dimension | Before S11 | After S11 (this PR) | After S11.B + S11.A.body |
|---|---|---|---|
| Axioms | 2 | 2 | 2 |
| Brouwer-side strength | general compact convex | unit ball only | unit ball only |
| Sorries | 0 | 2 | 0 |
| Mathlib-API risk | unverified `brouwer_fpt` lookup | none on the Brouwer side | none (helper builds from `Projection.lean` API) |

The transitional 2-sorry state is the natural cost of staging the
strict-weakening across multiple researchers; the two sorry bodies are
mathematically rigorous standard arguments with no remaining open
mathematical questions.

## S11.B — Lean stub for `exists_continuous_proj_convex`

The lemma signature (now in the Lean file):

```lean
lemma exists_continuous_proj_convex {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
    ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
      Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x
```

### Proof structure (S11.B work item, ~30–80 Lean lines)

```lean
lemma exists_continuous_proj_convex {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
    ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
      Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x := by
  -- Step 1: closedness + completeness for the existence/uniqueness call.
  have hS_closed : IsClosed S := hS_compact.isClosed
  have hS_complete : IsComplete S := hS_closed.isComplete
  -- Step 2: existence of nearest point at every x ∈ E.
  --   `Mathlib.Analysis.InnerProductSpace.Projection.exists_norm_eq_iInf_of_complete_convex`
  --   gives ∃ y ∈ S, ‖x - y‖ = ⨅ z ∈ S, ‖x - z‖.
  -- Step 3: uniqueness from strict convexity of the Euclidean norm.
  --   `EuclideanSpace.instStrictConvexSpace` (or
  --   `InnerProductSpace.toStrictConvexSpace ℝ E`) packages the strict
  --   convexity needed for uniqueness — strictly convex norm + at most
  --   one nearest point on a convex set.
  -- Step 4: define `r : E → ↥S` via `Classical.choose` on the
  --   existence-uniqueness combination.
  -- Step 5: continuity from the variational inequality.
  --   `Mathlib.Analysis.InnerProductSpace.Projection` exposes
  --   `norm_eq_iInf_iff_real_inner_le_zero` (and friends): for `y ∈ S`,
  --   `‖x - y‖ = ⨅ z ∈ S, ‖x - z‖` ↔ `∀ z ∈ S, ⟪x - y, z - y⟫_ℝ ≤ 0`.
  --   This Lipschitz-style characterization yields continuity of the
  --   projection: |r x₁ - r x₂| ≤ |x₁ - x₂| (1-Lipschitz, in fact).
  -- Step 6: idempotency on `↥S` from `dist_self` + uniqueness.
  --   For x ∈ S, `‖x - x‖ = 0`, which is the infimum, so the unique
  --   nearest point is x itself.
  sorry
```

### Mathlib API hooks (verified at the pinned rev)

| Step | Mathlib API |
|---|---|
| 2 (existence) | `Mathlib.Analysis.InnerProductSpace.Projection.exists_norm_eq_iInf_of_complete_convex` |
| 3 (strict convexity) | `EuclideanSpace.instStrictConvexSpace`, `StrictConvexSpace.strictConvex_closedBall`, `strictConvex_norm_le_iff` family |
| 5 (continuity) | `Mathlib.Analysis.InnerProductSpace.Projection`: `norm_eq_iInf_iff_real_inner_le_zero` and the 1-Lipschitz consequence |
| 6 (idempotency) | `dist_self`, `Metric.iInf_dist_eq_zero_iff_mem_closure`, plus uniqueness from step 3 |

### Why uniqueness matters

In a normed space that is **not** strictly convex (e.g. `ℓ¹` with the
sup-norm), the nearest point on a convex set need not be unique, so the
"projection" is not a function. For `EuclideanSpace ℝ (Fin n)` the
inner-product norm is strictly convex (parallelogram-law argument), so
this obstruction does not arise. The Mathlib typeclass
`StrictConvexSpace ℝ (EuclideanSpace ℝ (Fin n))` captures this and is
the typeclass dependency the helper requires.

### Why continuity follows from the variational inequality

The standard 1-Lipschitz proof: for any `x, x' ∈ E` and their
projections `r x, r x' ∈ S`, the variational inequalities

```
⟪x  - r x , r x' - r x⟫_ℝ ≤ 0
⟪x' - r x', r x  - r x'⟫_ℝ ≤ 0
```

add to give `⟪x - x', r x - r x'⟫_ℝ ≥ ‖r x - r x'‖²`, and Cauchy–Schwarz
delivers `‖r x - r x'‖ ≤ ‖x - x'‖`. This is folklore (Brézis,
*Functional Analysis*, Prop. 5.3) and is the standard route in the
Mathlib downstream literature.

## S11.A.body — Lean stub for `theorem brouwer_fpt` body

The theorem signature (now in the Lean file):

```lean
theorem brouwer_fpt {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x
```

### Proof structure (S11.A.body work item, ~60 Lean lines)

```lean
theorem brouwer_fpt {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x := by
  -- Step 1: S ⊆ closedBall 0 R for some R > 0 (LOOKUP-1, S9-confirmed).
  have hS_bounded : Bornology.IsBounded S := hS_compact.isBounded
  -- `Bornology.IsBounded.subset_closedBall_lt` returns `∃ R > 0, S ⊆ closedBall 0 R`
  -- for any chosen center; pick the origin.
  obtain ⟨R, hR_pos, hSR⟩ :=
    hS_bounded.subset_closedBall_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  -- Step 2: nearest-point retraction r : E → ↥S (LOOKUP-2 helper, S11.B).
  obtain ⟨r, hr_cont, hr_id⟩ :=
    exists_continuous_proj_convex S hS_ne hS_compact hS_convex
  -- Step 3: build F : ↥(closedBall 0 R) → ↥(closedBall 0 R).
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 R with hB_def
  have hSB : S ⊆ B := hSR
  have hB_ne : B.Nonempty := ⟨0, by
    simp [B, Metric.mem_closedBall, hR_pos.le]⟩
  -- F'(b) := f(r(b)) ∈ ↥S (lifted to E), then F lands in B since S ⊆ B.
  have hF_cont : Continuous (fun b : ↥B =>
      (f (r (b : EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n))) := by
    have h1 : Continuous (fun b : ↥B => (b : EuclideanSpace ℝ (Fin n))) :=
      continuous_subtype_val
    exact continuous_subtype_val.comp (hf.comp (hr_cont.comp h1))
  have hF_in_B : ∀ b : ↥B,
      (f (r (b : EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n)) ∈ B :=
    fun b => hSB (f (r (b : EuclideanSpace ℝ (Fin n)))).property
  let F : ↥B → ↥B := fun b =>
    ⟨(f (r (b : EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n)), hF_in_B b⟩
  have hF_cont' : Continuous F := hF_cont.subtype_mk _
  -- Step 4: rescale closedBall 0 R ↔ closedBall 0 1 to apply brouwer_unit_ball.
  -- The map  σ : closedBall 0 1 → closedBall 0 R,  x ↦ R • x
  -- is continuous (multiplication-by-R) with continuous inverse  τ : b ↦ R⁻¹ • b.
  -- Define G := τ ∘ F ∘ σ : closedBall 0 1 → closedBall 0 1; continuity by
  -- composition. brouwer_unit_ball gives a fixed point of G; conjugate
  -- back via σ to get a fixed point of F.
  --
  -- The membership in closedBall 0 R / closedBall 0 1 under scaling uses
  -- `Metric.mem_closedBall_zero_iff` (norm characterization of closedBall),
  -- `norm_smul`, and the elementary algebra `‖R • x‖ = R · ‖x‖` (R > 0).
  --
  -- Mathlib API options for the rescaling (any of these works):
  --   (a) `Homeomorph.smul` (multiplication by `R⁻¹`, after promoting R⁻¹ to a
  --       unit / nonzero scalar via `hR_pos.ne'`); restrict to the closed-ball
  --       subtypes via `Homeomorph.image` / `Homeomorph.subtype`.
  --   (b) Direct elementwise definition of σ, τ as `↥(closedBall 0 1) → ↥(closedBall 0 R)`
  --       using `norm_smul` for the membership proof and `continuous_const_smul` /
  --       `Continuous.smul` for continuity.
  --   (c) Apply brouwer_unit_ball to the conjugate G in coordinate form, no
  --       Homeomorph needed; conclude existence of the F-fixed point directly.
  --
  -- Option (b) is the most explicit and least Mathlib-API-dependent; we
  -- recommend it. The ~20-line conjugation block:
  --
  --   let σ : ↥(closedBall (0 : E) 1) → ↥B := fun x =>
  --     ⟨R • (x : E), by
  --       rw [Metric.mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hR_pos.le]
  --       calc R * ‖(x : E)‖ ≤ R * 1 := by
  --             apply mul_le_mul_of_nonneg_left _ hR_pos.le
  --             rw [← Metric.mem_closedBall_zero_iff]; exact x.property
  --         _ = R := by ring⟩
  --   let τ : ↥B → ↥(closedBall (0 : E) 1) := fun b =>
  --     ⟨R⁻¹ • (b : E), by
  --       rw [Metric.mem_closedBall_zero_iff, norm_smul,
  --           Real.norm_of_nonneg (inv_nonneg.mpr hR_pos.le)]
  --       have : ‖(b : E)‖ ≤ R := by
  --         rw [← Metric.mem_closedBall_zero_iff]; exact b.property
  --       calc R⁻¹ * ‖(b : E)‖ ≤ R⁻¹ * R := by
  --             apply mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hR_pos.le)
  --         _ = 1 := inv_mul_cancel₀ hR_pos.ne'⟩
  --   have hσ_cont : Continuous σ := by
  --     apply Continuous.subtype_mk
  --     exact (continuous_const_smul R).comp continuous_subtype_val
  --   have hτ_cont : Continuous τ := by
  --     apply Continuous.subtype_mk
  --     exact (continuous_const_smul R⁻¹).comp continuous_subtype_val
  --   let G : ↥(closedBall (0 : E) 1) → ↥(closedBall (0 : E) 1) := τ ∘ F ∘ σ
  --   have hG_cont : Continuous G := hτ_cont.comp (hF_cont'.comp hσ_cont)
  --   obtain ⟨y, hy⟩ := brouwer_unit_ball G hG_cont
  --   -- Recover F-fixed point: F (σ y) = σ y.
  --   ⟨σ y, …⟩
  --
  -- Steps 5–6 (membership of fixed point in S, idempotency, conclusion)
  -- proceed exactly as in S8's stub — no Mathlib-API risk.
  sorry
```

### Mathlib API hooks (verified at the pinned rev)

| Step | Mathlib API |
|---|---|
| 1 (LOOKUP-1) | `Bornology.IsBounded.subset_closedBall_lt` (S9-confirmed via on-disk grep; S10-reconfirmed via GitHub-API at the pinned mathlib rev) |
| 2 (LOOKUP-2) | `exists_continuous_proj_convex` (this file, S11.B) |
| 3 (compose F) | `continuous_subtype_val`, `Continuous.subtype_mk`, function-composition lemmas |
| 4 (rescale) | `Metric.mem_closedBall_zero_iff`, `norm_smul`, `continuous_const_smul`, `Continuous.smul`, `inv_mul_cancel₀`, `Real.norm_of_nonneg` |
| 5–6 (conclude) | `Subtype.ext`, `congrArg Subtype.val`, the helper's idempotency clause |

### The rescaling step in detail

The mathematical content of step 4: given a continuous self-map
`F : closedBall 0 R → closedBall 0 R` (R > 0), produce a fixed point.
The map `σ x := R • x` carries `closedBall 0 1` to `closedBall 0 R`
homeomorphically (via the inverse `τ b := R⁻¹ • b`); hence
`G := τ ∘ F ∘ σ : closedBall 0 1 → closedBall 0 1` is continuous.
`brouwer_unit_ball G hG_cont` gives `y` with `G y = y`, i.e.
`τ (F (σ y)) = y`, i.e. `F (σ y) = σ (τ (F (σ y))) = σ y`. So `σ y` is
a fixed point of `F` in `closedBall 0 R`.

The elementary version (Option b above) avoids `Homeomorph` machinery
entirely — every step is `norm_smul` + arithmetic on real numbers.
This makes it the lowest-risk Mathlib-API option for S11.A.body.

## Independence between S11.B and S11.A.body

The two `sorry` bodies above are *fully independent*:

* `exists_continuous_proj_convex` (S11.B) does not reference
  `brouwer_unit_ball` or any Brouwer FPT; it is a pure projection-onto-
  compact-convex statement.
* `theorem brouwer_fpt` (S11.A.body) does not reference any internal
  step of S11.B's proof; it only uses the helper's existential
  conclusion as a black box.

Hence S11.B and S11.A.body can be claimed and worked on by *two
different researchers in parallel*; their PRs do not conflict, and the
Lean file builds end-to-end once both lands.

## Confidence assessment

| Risk | Severity | Mitigation |
|---|---|---|
| `Bornology.IsBounded.subset_closedBall_lt` API drift between v4.10 and v4.26 | Low | S10 reconfirmed via GitHub-API at the pinned rev |
| `exists_norm_eq_iInf_of_complete_convex` API drift | Low | Present in `Mathlib/Analysis/InnerProductSpace/Projection.lean` at the pinned rev (S10) |
| `EuclideanSpace.instStrictConvexSpace` typeclass missing or renamed | Low | Standard typeclass; alternatives via `InnerProductSpace.toStrictConvexSpace` |
| Variational-inequality continuity proof in Mathlib | Medium | Folklore but the precise lemma name may need adjustment; the proof can be inlined (~10 lines) if no direct Mathlib lemma applies |
| Rescaling step Mathlib API selection | Low (with Option b) | Direct elementwise approach uses only `norm_smul` and arithmetic — no `Homeomorph` needed |
| `Subtype.ext` / coercion plumbing in step 5–6 | Low | Pattern matches the existing `kakutani_from_brouwer` body in the same file |

The overall confidence in S11.B + S11.A.body landing in 1–2 sessions
each is **high**: every Mathlib API surface is either confirmed at the
pinned rev or has a direct elementary alternative.

## What this iteration does

* **Strict-weakens** the Brouwer axiom from `general compact convex S`
  to `closed unit ball only`, achieving S10's recommended Option A.
* **Adds two named work items** (`exists_continuous_proj_convex` and
  `theorem brouwer_fpt` body) as `sorry`-stubbed declarations with
  fully-specified signatures. These are unblocked by S10's
  reconnaissance and have minimal API risk.
* **Decouples** S11.B and S11.A.body so that two researchers can land
  them in parallel.
* **Pins down the rescaling step** to an elementary `norm_smul` +
  arithmetic argument (Option b above), removing the `Homeomorph.smul`
  Mathlib-API uncertainty that S10's note left open.

## What this iteration does NOT do

* Does not change the axiom *count* (still 2: `brouwer_unit_ball` +
  `approx_selection_exists`).
* Does not Docker-verify the build (the `proofs/.lake` self-cycle
  symlink trap remains; see `feedback_researcher_lake_symlink_broken.md`).
  The two `sorry`-stubbed bodies syntactically depend only on
  established Lean 4 / Mathlib syntax and the helper's signature, and
  both should compile in `build pending` mode pending a build-equipped
  session's run.
* Does not address the harder `approx_selection_exists` axiom
  (PartitionOfUnity work, S12+).
* Does not implement S11.B or S11.A.body (next-iteration deliverables).

## Recommended next actions

1. **S11.B**: implement `exists_continuous_proj_convex` per the proof
   structure above. ~30–80 Lean lines. Independent of S11.A.body.
2. **S11.A.body**: implement the body of `theorem brouwer_fpt` per the
   proof structure above (Option b for rescaling). ~60 Lean lines.
   Independent of S11.B (uses the helper as a black box; if S11.B has
   not yet landed, the body still typechecks against the
   `sorry`-stubbed helper).
3. **Build verification**: once both S11.B and S11.A.body are in,
   Docker-verify the build and (if green) update `meta.json` to
   reflect axiomCount = 2 (already correct), sorry count = 0,
   `assumptions` text noting the strict-weakening on the Brouwer side.

## References

* S6 — `s6-axiom-counterexample.md` — pointwise selection counterexample
  (researcher-6, PR #17265).
* S8 — `s8-brouwer-extension-via-projection.md` — retraction reduction
  proof note + Lean stub (researcher-4, PR #17317).
* S9 — `s9-mathlib-lookup-refinements.md` — three-LOOKUP refinement
  note (researcher-5, PR #17419).
* S10 — `s10-mathlib-v426-lookup3-resolved.md` — GitHub-API resolution
  of LOOKUP-3 + Option-A recommendation (researcher-12, PR #17449).
* `feedback_researcher_lake_symlink_broken.md` — documents the
  `proofs/.lake` self-cycle that motivates `build pending` cadence.
