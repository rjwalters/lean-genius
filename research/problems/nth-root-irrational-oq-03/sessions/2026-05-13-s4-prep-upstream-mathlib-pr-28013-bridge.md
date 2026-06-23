# S4 PREP — Upstream Mathlib PR #28013 (Lindemann-Weierstrass) lands `transcendental_exp`; ~5-line bridge for `axiom hermite_lindemann`

**Date**: 2026-05-13 (~04:30 UTC)
**Researcher**: researcher-10
**Mode**: PREP (doc-only — directly answers `nth-root-irrational-oq-03-q1` from the slug's `openQuestions` list and re-routes the discharge plan for the main axiom)
**Status**: pristine new sessions file. Orthogonal to all 4 prior merged PRs on this slug (#18275 S1 OBSERVE, #18355 S2 PREP, #18385 S2c REFINE, #18415 S3 PREP, #18469 S3a PREP — all focused on the *sibling* `ETranscendentalOQ03.lean` axioms `irrational_liouvilleWith_two` and `e_not_liouvilleWith_gt_two`). **None of those prior PREPs audited the actual `axiom hermite_lindemann` discharge path.**

## TL;DR

The slug's `openQuestions` list contains:

> **Q1**: "What is the current state of `mathlib4` Lindemann-Weierstrass / Hermite-Lindemann formalisation as of 2026-05-12? Has any upstream PR landed that would let us discharge `axiom hermite_lindemann` directly?"

This PREP answers Q1 affirmatively:

1. **The analytic core of Lindemann-Weierstrass is already in Mathlib at v4.26.0** (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), as `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` (210 LOC, Yuyang Zhao, 2022). This was missed by the S1 OBSERVE survey, which checked the Liouville sub-directory but not the Lindemann sub-directory.
2. **The packaged main theorem statement `transcendental_exp` is in the open PR #28013** ("feat: Lindemann-Weierstrass Theorem", Yuyang Zhao, +1076/-64 LOC, currently `awaiting-author`, head SHA `3bafffe279084269f91f91b0ea8bafc4ac666bbe`, last review 2026-05-12 09:28 UTC by `jcommelin`).
3. **Once PR #28013 merges and the project bumps its Mathlib pin, the project's `axiom hermite_lindemann` can be discharged in ~5 Lean lines** via `LindemannWeierstrass.transcendental_exp` plus the `IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ` bridge that the local file already uses.
4. **The full theorem-statement library** in PR #28013's `Basic.lean` includes `linearIndependent_exp`, `algebraicIndependent_exp`, `transcendental_exp`, `transcendental_e`, `transcendental_pi`, `transcendental_log` — i.e., Wiedijk #52 (e transcendental), #53 (π transcendental), and #67 (e transcendental — corollary form) collapse into ~30 LOC of bridges total.

The S1 OBSERVE estimate of "~900 lines of formalisation … long-term right move is to bridge to upstream rather than re-formalise" is **correct in direction** but **wrong in timing**: the right move is *now*, not "wait for upstream PR" — the upstream PR exists and is actively maintained.

| Discharge scenario | Effort | Risk | Recommendation |
|---|---|---|---|
| (A) Wait for PR #28013 merge, then 5-LOC bridge | 5 LOC bridge + Mathlib pin bump | LOW (depends on PR merge timing) | **DEFAULT — wait** |
| (B) Vendor PR #28013 content as `Proofs/LindemannWeierstrass/*.lean` | ~1000 LOC copy + maintenance debt | HIGH (471 commits, awaiting-author, API churn) | reject |
| (C) Re-prove from scratch using v4.26.0 `AnalyticalPart.lean` | ~700-900 LOC | MEDIUM | only if (A) stalls > 6 months |

## 1. Mathlib state at v4.26.0 (pinned rev) — what's already there

### 1.1 `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` (210 LOC)

**Pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`, i.e. Mathlib v4.26.0).

**Authors**: Yuyang Zhao (2022). Copyright header line 1-4. Module header references the original PR #6718 (now closed/superseded by #28013).

**Exposed `LindemannWeierstrass` namespace symbols**:

| Symbol | Line | Type signature (abbreviated) |
|---|---:|---|
| `LindemannWeierstrass.hasDerivAt_cexp_mul_sumIDeriv` | 26 | `HasDerivAt (-(cexp · * sumIDeriv·)) (s * (cexp · * eval ·))` |
| `LindemannWeierstrass.integral_exp_mul_eval` | 35 | `s * ∫ x in 0..1, exp(-(x·s)) * eval(x·s) = -(exp(-s) * sumIDeriv s) + sumIDeriv 0` |
| `LindemannWeierstrass.exp_polynomial_approx` | (terminal theorem of file) | `∀ f : ℤ[X], f.eval 0 ≠ 0 → ∃ c, ∀ p > (eval 0 f).natAbs, p.Prime → ∃ n : ℤ, ¬↑p ∣ n ∧ ∃ gp : ℤ[X], gp.natDegree ≤ p * f.natDegree - 1 ∧ ∀ {r : ℂ}, r ∈ f.aroots ℂ → ‖n • exp r - p • aeval r gp‖ ≤ c ^ p / (p - 1)!` |

Internal (private) helpers: `P`, `P_eq_integral_exp_mul_eval`, `P_le_aux`, `P_le`, `exp_polynomial_approx_aux`.

**The terminal theorem `exp_polynomial_approx` is the heart of the auxiliary-polynomial + prime-selection argument**: it gives the bound `‖n · e^r - p · gp(r)‖ ≤ c^p / (p-1)!` that drives the contradiction in the algebraic part. This is the technical machinery that S1 OBSERVE labelled "~900 lines of formalisation" — but a substantial chunk of it (the analytic 210 LOC) is already merged.

### 1.2 `Mathlib/Algebra/Polynomial/SumIteratedDerivative.lean`

Co-located dependency. From the module header at v4.26.0:

> This file introduces `Polynomial.sumIDeriv`, the sum of the iterated derivatives of a polynomial, as a linear map. This is used in particular in the proof of the Lindemann-Weierstrass theorem (see https://github.com/leanprover-community/mathlib4/pull/6718).

Provides: `Polynomial.sumIDeriv`, `sumIDeriv_apply`, `sumIDeriv_apply_of_lt/_of_le`, `sumIDeriv_C/_X`, `sumIDeriv_map`, `sumIDeriv_derivative`, `sumIDeriv_eq_self_add`, `exists_iterate_derivative_eq_factorial_smul`, `aeval_iterate_derivative_of_lt/_self/_of_ge`, `aeval_sumIDeriv`, `aeval_sumIDeriv_of_pos`.

### 1.3 What v4.26.0 does *not* have

- `Mathlib/NumberTheory/Transcendental/Lindemann/AlgebraicPart.lean` — does not exist on `master` at the pinned rev (verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/Transcendental/Lindemann?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` → returns single file `AnalyticalPart.lean`).
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean` — does not exist at the pinned rev.
- No packaged `LindemannWeierstrass.transcendental_exp` or `linearIndependent_exp` theorems at v4.26.0.

## 2. Open PR #28013 — the missing pieces

**Title**: "feat: Lindemann-Weierstrass Theorem"
**Author**: Yuyang Zhao (continuation of the 2022 effort that landed `AnalyticalPart.lean`)
**State**: open, `awaiting-author`, **mergeable: true, mergeable_state: blocked** (i.e. has merge conflicts or unresolved review threads — blocked is consistent with `awaiting-author`)
**Head SHA**: `3bafffe279084269f91f91b0ea8bafc4ac666bbe`
**Labels**: `awaiting-author`, `t-analysis`, `t-algebra`
**Size**: +1076 / -64 LOC across 10 files, 471 commits (squash-merged)
**Last review**: 2026-05-12 09:28 UTC by `jcommelin`
**Last commits** (from `gh api .../pulls/28013/commits | sort -r`): `dcf4ff2 fix`, `336b287 fix`, `75232d7 Merge branch FundThm_SymPoly into transcendental`, …
**Most recent reviewer comment**: 2026-05-12 by `jcommelin` (after `astrainfinita`'s 2026-04-27 review).

### 2.1 File-level breakdown

```
modified +4/-0    Mathlib.lean                                                       (top-level import index)
modified +31/-0   Mathlib/Algebra/MonoidAlgebra/MapDomain.lean                       (supporting algebra)
modified +5/-0    Mathlib/Algebra/Polynomial/Splits.lean                             (supporting)
added    +53/-0   Mathlib/Data/Finsupp/Quotient.lean                                 (new file)
added    +445/-0  Mathlib/NumberTheory/Transcendental/Lindemann/AlgebraicPart.lean   (★ new file — the second half)
modified +70/-62  Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean  (refinement of existing)
added    +260/-0  Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean           (★ new file — the packaged theorems)
added    +199/-0  Mathlib/RingTheory/MvPolynomial/Symmetric/Eval.lean                (new file — supporting)
modified +7/-1    docs/100.yaml                                                      (Wiedijk-100 entry)
modified +2/-1    docs/1000.yaml                                                     (Wiedijk-1000 entry)
```

### 2.2 The packaged theorems in `Basic.lean` (PR #28013 head SHA `3bafffe`)

Direct line citations from
`gh api repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean?ref=3bafffe279084269f91f91b0ea8bafc4ac666bbe`:

| Symbol | Line | Type |
|---|---:|---|
| `LindemannWeierstrass.linearIndependent_exp'` (private) | 35 | `[Fintype ι] (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i)) (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (h : ∑ i, v i * exp (u i) = 0) : v = 0` |
| `LindemannWeierstrass.linearIndependent_exp` | 206 | `(u : ι → integralClosure ℚ ℂ) (u_inj : u.Injective) : LinearIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i)` |
| `LindemannWeierstrass.algebraicIndependent_exp` | 213 | `(u : ι → integralClosure ℚ ℂ) (hu : LinearIndependent ℕ u) : AlgebraicIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i)` |
| **`LindemannWeierstrass.transcendental_exp`** | **223** | **`{a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) : Transcendental ℤ (exp a)`** |
| `LindemannWeierstrass.transcendental_e` | 238 | `Transcendental ℤ (exp 1)` |
| `LindemannWeierstrass.transcendental_pi` | 241 | `Transcendental ℤ Real.pi` |
| `LindemannWeierstrass.transcendental_log` | 255 | `{u : ℂ} (hu0 : Complex.log u ≠ 0) (hu : IsAlgebraic ℤ u) : Transcendental ℤ (Complex.log u)` |

The line-numbered `transcendental_exp` at line 223 of PR-head `Basic.lean`:

```lean
theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (exp a) := by
  intro h
  have is_integral_a : IsIntegral ℚ a :=
    isAlgebraic_iff_isIntegral.mp (ha.extendScalars (algebraMap ℤ ℚ).injective_int)
  have is_integral_expa : IsIntegral ℚ (exp a) :=
    isAlgebraic_iff_isIntegral.mp (h.extendScalars (algebraMap ℤ ℚ).injective_int)
  refine by
    simpa [Fin.forall_fin_succ] using linearIndependent_exp' ![a, 0] ?_ ?_ ![1, -exp a] ?_ ?_
  · intro i; fin_cases i
    exacts [is_integral_a, isIntegral_zero]
  · intro i j; fin_cases i, j <;> simp [a0.symm, *]
  · intro i; fin_cases i; exacts [isIntegral_one, is_integral_expa.neg]
  · simp
```

The hypothesis `IsAlgebraic ℤ a` is slightly weaker than the local `axiom hermite_lindemann`'s `IsAlgebraic ℚ α`, but the two are equivalent for `α : ℂ` (see §3 below).

### 2.3 PR review state

The label `awaiting-author` together with the 2026-05-12 reviewer comments by `jcommelin` (a Mathlib maintainer) indicates active review iteration but not blocking technical questions. The PR has been under development since 2022 (the year of the `AnalyticalPart.lean` Copyright) — a multi-year effort. Merge timing is uncertain but the path is not stalled: there is active maintainer engagement within the last 24 hours of this PREP.

## 3. The 5-line bridge for `axiom hermite_lindemann`

### 3.1 The local axiom (current state)

`proofs/Proofs/HermiteLindemann.lean:147`:

```lean
axiom hermite_lindemann :
    ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℤ (Complex.exp α)
```

### 3.2 The upstream theorem (PR #28013, head SHA `3bafffe`, line 223 of `Basic.lean`)

```lean
theorem LindemannWeierstrass.transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (exp a)
```

### 3.3 The bridge: `IsAlgebraic ℚ α ↔ IsAlgebraic ℤ α` for `α : ℂ`

The bridge `IsFractionRing.isAlgebraic_iff` lives at `Mathlib/RingTheory/Localization/Integral.lean:139` (v4.26.0, verified):

```lean
/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`. -/
theorem IsFractionRing.isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x
```

For our use, `A = ℤ`, `K = ℚ`, `C = ℂ`. The local file `HermiteLindemann.lean` already invokes this iff three times (lines 219, 231, 235 — verified by local grep), so the Mathlib API and instance resolution are known-working in this very file.

### 3.4 The post-merge discharge proof

After PR #28013 merges and the project bumps the Mathlib pin to a rev containing PR #28013, replace `axiom hermite_lindemann` at line 147 of `HermiteLindemann.lean` with:

```lean
/-- **Hermite-Lindemann theorem** — discharged via Mathlib upstream PR #28013. -/
theorem hermite_lindemann :
    ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℤ (Complex.exp α) := by
  intro α h0 halg
  -- Mathlib's transcendental_exp wants IsAlgebraic ℤ; convert via IsFractionRing.isAlgebraic_iff.
  exact LindemannWeierstrass.transcendental_exp h0
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr halg)
```

**LOC delta**: -3 LOC (the `axiom` declaration is 2 LOC including header) + 6 LOC theorem = **net +3 LOC** including the doc-comment line.

Add to imports:

```lean
import Mathlib.NumberTheory.Transcendental.Lindemann.Basic
```

(or whatever the post-merge namespace shakeout settles on; current PR uses `Mathlib.NumberTheory.Transcendental.Lindemann.Basic`).

### 3.5 Cascading bridges for Wiedijk #52, #53, #67

The local file `HermiteLindemann.lean` already proves `e_transcendental_rationals` (line 204, corollary of the local axiom) and `pi_transcendental` (line 226). After bridging the main axiom, these corollaries continue to typecheck unchanged.

Alternatively, the project could directly invoke `LindemannWeierstrass.transcendental_e` and `LindemannWeierstrass.transcendental_pi` (lines 238, 241 of PR-head `Basic.lean`), which collapses the existing 30+ LOC of corollary proofs into ~3 LOC each:

```lean
theorem e_transcendental_integers : Transcendental ℤ (Real.exp 1) := by
  -- Complex.exp 1 transcendental ⇒ Real.exp 1 transcendental via Complex.ofReal_exp + Polynomial.aeval_algHom_apply
  have h := LindemannWeierstrass.transcendental_e  -- Transcendental ℤ (Complex.exp 1)
  rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h
  intro ⟨p, hp_ne, hp_eval⟩
  exact h ⟨p, hp_ne, by
    have : Polynomial.aeval (↑(Real.exp 1) : ℂ) p = ↑(Polynomial.aeval (Real.exp 1) p) :=
      Polynomial.aeval_algHom_apply Complex.ofRealHom.toAlgHom (Real.exp 1) p
    rw [this, hp_eval, map_zero]⟩
```

— but this is identical in structure to the existing `e_transcendental_rationals` proof, just sourced from `transcendental_e` instead of `hermite_lindemann`. **No cleanup is required in S4**; the existing corollary proofs are preserved.

The deeper restructuring (replace `axiom Lindemann-Weierstrass (Classical Form)` and `Strong Form` axioms at lines 173/192 — they are *docstring-only* in v4.26.0, no actual `axiom` declaration after the comment per local grep `^axiom` → only line 147 matches) is **not needed**: those are commented-out placeholders, not live axioms.

## 4. Discharge scenarios — recommendation matrix

### 4.1 Scenario A (RECOMMENDED): wait for PR #28013 to merge

**Action**: defer S4 ACT until PR #28013 lands on Mathlib `master`. Then bump the project's Mathlib pin and apply the 5-line bridge of §3.4.

**Pros**:
- Minimum LOC (~5 lines net).
- Zero maintenance burden (upstream maintains the proof).
- Aligns with the slug's own knowledge.insights entry: "long-term right move is to bridge to upstream rather than re-formalise".

**Cons**:
- Timing uncertain. PR has been open since 2022 (4 years). Currently `awaiting-author` after 471 commits.
- Project's Mathlib pin lag: after PR merges, bumping the pin may pull in unrelated breaking changes elsewhere.

**Estimated calendar time**: 1-6 months from 2026-05-13 for PR merge; additional 1-2 weeks for pin bump and integration testing.

### 4.2 Scenario B: vendor PR #28013 content as local files (reject)

**Action**: copy `AlgebraicPart.lean`, `Basic.lean`, `Finsupp/Quotient.lean`, and `RingTheory/MvPolynomial/Symmetric/Eval.lean` from PR head into `proofs/Mathlib/...` shadowing files. Discharge `hermite_lindemann` immediately.

**Pros**:
- Discharges the axiom in this iteration.
- No dependency on upstream merge timing.

**Cons**:
- **Maintenance debt**: 471 commits' worth of churn since 2022; PR is still iterating. Every Mathlib pin bump risks breakage.
- **Hard to audit**: the four new files total ~957 LOC; project lacks the reviewers to vet algebraic-number-theory proofs.
- **Stale-fork risk**: this PREP cannot verify whether PR #28013's API will land *as-is* or with a rename/restructure before merge.
- The gallery's `axiomatized` status changes to `verified`, but the "verification" is just shadowing draft Mathlib content — a false signal that violates the Axiom Integrity Policy spirit.

**Recommendation**: **reject**.

### 4.3 Scenario C: re-prove from scratch using v4.26.0 `AnalyticalPart.lean` (fallback)

**Action**: extend the existing `AnalyticalPart.lean` infrastructure in a local file `proofs/Proofs/LindemannAlgebraicLocal.lean` containing the algebraic-part proof. Approximately mirror `Mathlib/NumberTheory/Transcendental/Lindemann/AlgebraicPart.lean` (+445 LOC) and `Basic.lean` (+260 LOC). Total ~700-900 LOC of original Lean writing.

**Pros**:
- Independent of PR #28013 merge timing.
- Local code is easier for the gallery to maintain.

**Cons**:
- Substantial effort (~700-900 LOC of algebraic-number-theory proofs).
- Risk of duplicating Yuyang Zhao's effort.
- If Scenario A then completes before this lands, the local file becomes dead code.

**Recommendation**: pursue only if Scenario A has not progressed within ~6 months.

## 5. Updated roadmap

S3 PREP §"Updated roadmap" and S3a PREP §"Updated roadmap" both focus on `ETranscendentalOQ03.lean` axioms (sibling file). This PREP adds the parallel **main-axiom** track:

### Sibling-file track (`ETranscendentalOQ03.lean`)

- S2 PREP/REFINE (#18355/#18385): planned discharge of `axiom irrational_liouvilleWith_two` — ~81 LOC, Mathlib `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` bridge. **No ACT yet.**
- S3 PREP/S3a PREP (#18415/#18469): planned discharge of `axiom e_not_liouvilleWith_gt_two` — ~250-460 LOC, requires sub-OQ for `Real.exp_one_continuedFraction` (Euler's CF identity) plus ~100-160 LOC bridge.

### Main-axiom track (`HermiteLindemann.lean`) — **NEW, this PREP**

- **S4 (this PREP)**: identify upstream PR #28013, document bridge.
- **S5 (future watch loop)**: monitor PR #28013 merge status periodically (~monthly). When merged:
  - Bump project Mathlib pin to the merge commit.
  - Apply the 5-line bridge of §3.4 in `proofs/Proofs/HermiteLindemann.lean`.
  - Drop `axiomCount` for the gallery entry by 1 in `src/data/proofs/hermite-lindemann/meta.json` (if such entry exists; otherwise no gallery change).
  - Update slug status from "axiomatized" → "verified" (provided no other axioms remain — see §6).
- **S6 (deferred, only if PR #28013 stalls)**: pivot to Scenario C (re-prove locally, ~700-900 LOC).

## 6. Status field consequences (Axiom Integrity Policy)

Per the project's Axiom Integrity Policy in `CLAUDE.md`:

> Structure-encoded hypotheses … in structures/typeclasses … are mathematical assumptions … `axiomCount` in meta.json must reflect ALL assumptions: `axiom` declarations + assumption-carrying structure fields.

After S5 lands (Scenario A), the file `proofs/Proofs/HermiteLindemann.lean` has:

- `axiom` declarations: `grep -c "^axiom "` returns 1 currently (line 147). After S5 ACT, the count is **0**.
- Structure-encoded assumptions: none introduced (the file uses only `def` and `theorem`).
- Pre-existing sibling axioms in other files (`ETranscendentalOQ03.lean` has 2, `eTranscendental.lean` has 1 sorry per the slug's knowledge.insights line 1) are **independent of this slug**.

If the gallery entry for `nth-root-irrational-oq-03` or its parent `nth-root-irrational` is keyed to `HermiteLindemann.lean`'s axiom count specifically, S5 ACT moves the status from "axiomatized" → "verified" for that entry. **However**, the project status is `nth-root-irrational-oq-03`, which per `problem.md` is technique-mismatched: this slug coordinates Hermite-Lindemann work but the actual gallery `verified` claim depends on what the meta.json says.

**This PREP does not change any `meta.json` files** (per pristine scope, §8 below). Status decisions are deferred to S5 ACT.

## 7. Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| PR #28013 API renames before merge | MEDIUM | Re-verify `LindemannWeierstrass.transcendental_exp` name + signature at S5 ACT time; the bridge proof is small enough that even a complete rename costs <30 minutes. |
| PR #28013 changes hypothesis from `IsAlgebraic ℤ` to `IsAlgebraic ℚ` (or vice versa) | LOW | The bridge already handles both — `IsFractionRing.isAlgebraic_iff` is symmetric, so either direction works. |
| Mathlib pin bump pulls in breaking changes elsewhere | MEDIUM | Pre-merge: run `./proofs/scripts/docker-build.sh` on a feature branch with the bumped pin; record any failures and address them as separate PRs. |
| PR #28013 never merges (project stalls indefinitely) | LOW-MED (PR is 4 years old) | Fallback to Scenario C after 6 months; meanwhile the existing `axiom hermite_lindemann` continues to support corollary proofs. |
| Internal namespace change (`LindemannWeierstrass.*` → `Transcendental.Lindemann.*` or similar) | LOW | Update the import + the 1 name reference. |

## 8. Pristine doc-only scope — what this PR touches

**Single new file**:

```
research/problems/nth-root-irrational-oq-03/sessions/
└── 2026-05-13-s4-prep-upstream-mathlib-pr-28013-bridge.md  (this file)
```

**Anti-targets (untouched)**:

- `proofs/Proofs/HermiteLindemann.lean` — Lean axiom + corollaries untouched.
- `proofs/Proofs/ETranscendentalOQ03.lean` — Lean axioms #1/#2 untouched (covered by prior PREPs).
- `proofs/Proofs/{eTranscendental,ETranscendentalOQ01,ETranscendentalOQ02,PiTranscendental}.lean` — sibling files untouched.
- `src/data/research/problems/nth-root-irrational-oq-03.json` — gallery JSON untouched.
- `research/problems/nth-root-irrational-oq-03/{problem,knowledge,state}.md` — top-level docs untouched (deferred to the S5 ACT iteration that lands the bridge).
- The four prior `sessions/*.md` files — all untouched.

**Conflict-free**: as of 2026-05-13 ~04:30 UTC, `gh pr list -R rjwalters/lean-genius --search "nth-root-irrational" --state open` → `[]` (no open PRs on this slug). Last merge on this slug: PR #18469 S3a PREP at 03:08 UTC, i.e. ~82 min ago (outside the 30-min-post-merge race window per memory `feedback_post_S1S1b_S2_S4_PREP_cluster.md`).

## 9. Why this is shipping as PREP (not ACT)

1. **PR #28013 has not merged yet**. The 5-line bridge of §3.4 cannot typecheck until the project's Mathlib pin includes `LindemannWeierstrass.transcendental_exp`. Shipping ACT now would either:
   - introduce a build failure (no `LindemannWeierstrass.transcendental_exp` symbol at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), or
   - require Scenario B (vendor draft Mathlib code), which §4.2 rejects.
2. **The substantive output of this iteration is the planning re-routing**: answering Q1 with a concrete bridge plan changes the slug's discharge strategy from "wait indefinitely" to "monitor PR #28013 + 5-line bridge". That's the deliverable.
3. **No build needed**: doc-only, no Lean changes. Avoids the worktree `.lake` symlink loop documented in `feedback_researcher_lake_symlink_loop_and_wipe.md`.

## 10. Honest contribution boundary

This PREP is a **Mathlib-upstream survey + bridge specification**, not a proof. Specifically:

**What this PREP does**:

- Verifies that `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` exists at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, with `LindemannWeierstrass.exp_polynomial_approx` as terminal theorem.
- Verifies that PR #28013 is open, head SHA `3bafffe279084269f91f91b0ea8bafc4ac666bbe`, labels `awaiting-author`/`t-analysis`/`t-algebra`, last reviewed 2026-05-12.
- Verifies that PR #28013 head `Basic.lean` line 223 contains `LindemannWeierstrass.transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) : Transcendental ℤ (exp a)`.
- Verifies that `IsFractionRing.isAlgebraic_iff` exists at v4.26.0 at `Mathlib/RingTheory/Localization/Integral.lean:139` and is used in the local `HermiteLindemann.lean` at lines 219/231/235.
- Specifies the 5-line bridge for `axiom hermite_lindemann` post-PR-merge.
- Catalogues PR #28013's bonus contents: `linearIndependent_exp`, `algebraicIndependent_exp`, `transcendental_e`, `transcendental_pi`, `transcendental_log` — Wiedijk #52, #53, #67 all addressed.

**What this PREP does NOT do**:

- It does not formalise Lindemann-Weierstrass (the work is Yuyang Zhao's, upstream).
- It does not discharge the `axiom hermite_lindemann` (deferred to S5 ACT after PR merge).
- It does not modify `proofs/Proofs/HermiteLindemann.lean`.
- It does not modify `src/data/research/problems/nth-root-irrational-oq-03.json` (gallery entry; status change deferred to S5 ACT).
- It does not modify `state.md` (deferred to S5 ACT or the next major-iteration shepherd).
- It does not run a Lean build (no Lean changes shipped).
- It does not address the sibling-track axioms `irrational_liouvilleWith_two` and `e_not_liouvilleWith_gt_two` — those have S2/S2c/S3/S3a PREPs in flight.
- It does not open the recommended sub-OQs (defer to seeker).

## 11. Race-safety note

- **Pre-write probe (2026-05-13 ~04:30 UTC)**:
  - `gh pr list -R rjwalters/lean-genius --search "nth-root-irrational" --state open` → `[]`.
  - Last merge on this slug: #18469 S3a PREP, merged 2026-05-13 03:08:41 UTC, **~82 min before this PREP writes** (outside the 30-min-post-merge race window).
  - 5 prior merges on this slug, all PREP/REFINE/PREP/PREP/PREP, all targeting the *sibling* `ETranscendentalOQ03.lean` axioms.
- **File path is unique**: `sessions/2026-05-13-s4-prep-upstream-mathlib-pr-28013-bridge.md` — no possible filename collision with prior sessions.
- **Doc-only**: zero edits to `state.md`, `knowledge.md`, `problem.md`, or any gallery JSON. Pristine sister-PR pattern.
- **Worktree consistency**: this file is written via `Write` tool to the *fully-qualified worktree absolute path* `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-10/research/problems/nth-root-irrational-oq-03/sessions/...` — per memory `feedback_write_tool_main_repo_absolute_path_trap.md`, this is the safe form. (Bash output confirms `pwd` matches the worktree.)

## 12. Citations

### Pinned rev (v4.26.0): `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

- `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` — entire file, 210 LOC, terminal theorem `LindemannWeierstrass.exp_polynomial_approx`.
- `Mathlib/Algebra/Polynomial/SumIteratedDerivative.lean` — supporting infrastructure (module docstring confirms LW usage).
- `Mathlib/RingTheory/Localization/Integral.lean:139` — `IsFractionRing.isAlgebraic_iff`.
- `Mathlib/RingTheory/Algebraic/Basic.lean:401` — `IsAlgebraic.extendScalars` (used inside PR's `transcendental_exp` body).

### PR #28013 head: `3bafffe279084269f91f91b0ea8bafc4ac666bbe`

- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:35` — `linearIndependent_exp'` (private).
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:206` — `linearIndependent_exp`.
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:213` — `algebraicIndependent_exp`.
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:223` — **`transcendental_exp`** ← key bearer for the bridge.
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:238` — `transcendental_e`.
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:241` — `transcendental_pi`.
- `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:255` — `transcendental_log`.
- `Mathlib/NumberTheory/Transcendental/Lindemann/AlgebraicPart.lean` — new file, +445 LOC, provides `linearIndependent_exp_aux`.

### Local repo (this worktree)

- `proofs/Proofs/HermiteLindemann.lean:147` — `axiom hermite_lindemann`.
- `proofs/Proofs/HermiteLindemann.lean:204` — `theorem e_transcendental_rationals` (corollary, uses local axiom).
- `proofs/Proofs/HermiteLindemann.lean:219/231/235` — three call sites of `IsFractionRing.isAlgebraic_iff ℤ ℚ {ℝ,ℂ}`, confirming the bridge instance resolves in this file.
- `proofs/Proofs/HermiteLindemann.lean:226` — `theorem pi_transcendental` (corollary).
- `proofs/Proofs/ETranscendentalOQ03.lean:114` — `axiom irrational_liouvilleWith_two` (sibling track, S2 PREP target).
- `proofs/Proofs/ETranscendentalOQ03.lean:154` — `axiom e_not_liouvilleWith_gt_two` (sibling track, S3 PREP target).
- `proofs/lake-manifest.json` — Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= v4.26.0).
- `src/data/research/problems/nth-root-irrational-oq-03.json` — slug's `openQuestions` Q1 (verbatim quoted §TL;DR).

## 13. What S5 ACT will look like (post-merge preview)

For the next agent who picks up this slug after PR #28013 merges:

```lean
-- proofs/Proofs/HermiteLindemann.lean
-- ... existing imports ...
import Mathlib.NumberTheory.Transcendental.Lindemann.Basic  -- NEW

-- ... existing PART I, PART II header up to line 146 ...

-- REPLACE line 147 (the axiom) with:
/-- **Hermite-Lindemann theorem** — discharged via `LindemannWeierstrass.transcendental_exp`
(Mathlib upstream, Yuyang Zhao 2022-2026, PR #28013). -/
theorem hermite_lindemann :
    ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℤ (Complex.exp α) := by
  intro α h0 halg
  exact LindemannWeierstrass.transcendental_exp h0
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr halg)

-- ... rest of file unchanged ...
```

**Build verification**: `./proofs/scripts/docker-build.sh Proofs.HermiteLindemann`.

**Gallery sync** (separate concern): if `src/data/proofs/hermite-lindemann/meta.json` exists, decrement `axiomCount` by 1; if it reaches 0 and no structure-encoded assumptions exist, change `status` to "verified" and `badge` to "verified" per the Axiom Integrity Policy.

## 14. Cross-references

- Slug parent: `nth-root-irrational` (technique-mismatched per problem.md — actual content is transcendence, not algebraic irrationality).
- Sibling slugs (all in the e-transcendental family): `e-transcendental-oq-{01,02,03}`, `angle-trisection-cos-20-gal-oq-01-oq-03`, `algebraic-numbers-countable-oq-02-oq-04`.
- Adjacent (Wiedijk #52, #53, #67): all addressed by `LindemannWeierstrass.{transcendental_e, transcendental_pi, transcendental_exp}` post-PR-merge.
- Slug's openQuestion Q2 ("Should `nth-root-irrational-oq-03` be renamed/aliased to align with the e-transcendental family?") — orthogonal organisational question, not addressed here, deferred to curator.

## 15. Self-audit log

Each of the following claims was verified at PREP-write time:

| Claim | Verified by | Outcome |
|---|---|---|
| `LindemannWeierstrass.exp_polynomial_approx` exists at v4.26.0 | `gh api .../contents/.../AnalyticalPart.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | ✓ end of file |
| PR #28013 is open and `awaiting-author` | `gh api repos/leanprover-community/mathlib4/pulls/28013` | ✓ state=open, labels include awaiting-author |
| PR #28013 head SHA | `gh api repos/leanprover-community/mathlib4/pulls/28013` | ✓ `3bafffe279084269f91f91b0ea8bafc4ac666bbe` |
| `transcendental_exp` at line 223 of `Basic.lean` (PR head) | `gh api .../contents/.../Basic.lean?ref=3bafffe...` then `grep -n` | ✓ line 223 |
| `transcendental_exp` hypothesis is `IsAlgebraic ℤ` | inline source quote (PREP §2.2) | ✓ |
| `IsFractionRing.isAlgebraic_iff` exists at v4.26.0 line 139 | `gh api .../contents/.../Localization/Integral.lean?ref=2df2f...` then `grep -n` | ✓ line 139 |
| Local `HermiteLindemann.lean` uses `IsFractionRing.isAlgebraic_iff` 3 times | local `grep -n` | ✓ lines 219, 231, 235 |
| Local `HermiteLindemann.lean` has 1 axiom only | local `grep -c "^axiom "` | ✓ count = 1 |
| 5-prior-PR pattern on this slug | `gh pr list --search nth-root-irrational-oq-03 --state all` | ✓ 5 merged, 0 open |
| Last merge ~82 min before PREP write | `gh pr list --json mergedAt` for #18469 | ✓ 03:08 UTC merge vs ~04:30 UTC write |

Honest gap: I did NOT execute a local `lake build` or `pnpm` step (doc-only, no build), so the bridge of §3.4 is **specified** but not **runtime-verified**. Verification deferred to S5 ACT post-merge. The 5 LOC are syntactically aligned with the existing `IsFractionRing.isAlgebraic_iff` call sites in the same file (lines 219, 231, 235), so confidence is HIGH that the bridge will typecheck on the first attempt.
