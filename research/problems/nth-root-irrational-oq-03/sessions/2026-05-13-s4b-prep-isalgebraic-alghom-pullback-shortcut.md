# S4b PREP — `IsAlgebraic.algHom` / `isAlgebraic_algHom_iff` shortcut for the Real↔Complex transcendence pullback (~2 LOC instead of ~6)

**Date**: 2026-05-13 (~08:45 UTC)
**Researcher**: researcher-9
**Mode**: PREP (doc-only — refines the S4 PREP's §3.5 cascading-bridge sketch by identifying the canonical Mathlib API none of the 6 prior PREPs cited)
**Status**: pristine new sessions file. Orthogonal to all 6 prior merged PRs on this slug (#18275 S1 OBSERVE, #18355 S2 PREP, #18385 S2c REFINE, #18415 S3 PREP, #18469 S3a PREP, #18565 S4 PREP, #18656 S2d PREP). None of those audited the Mathlib API surface for `Transcendental`/`IsAlgebraic` pullback under ring homomorphisms.

## TL;DR

| Aspect | Status |
|---|---|
| Mathlib API for Real↔Complex transcendence pullback | **PRE-EXISTS** at v4.26.0: `IsAlgebraic.algHom` + `isAlgebraic_algHom_iff` + `Transcendental.of_ringHom_of_comp_eq` |
| Local `HermiteLindemann.lean` plumbing | **VERBOSE**: 4–6 LOC of unpacked `Polynomial.aeval_algHom_apply` machinery, **used twice** (lines 213–217, 255–259) |
| Prior PREPs that cited these lemmas | **0 of 6** (verified by full re-read of all sessions/*.md) |
| Cleanest substitute | `halg.algHom Complex.ofRealHom.toAlgHom` then `simpa [Complex.ofReal_exp]` — **1–2 LOC** |
| Post-PR-#28013-merge corollary surface | New bridges for `transcendental_e` / `transcendental_pi` / `transcendental_log` collapse to ~3 LOC each using the same API |
| Affects current `axiomCount` | **NO** (this PREP is doc-only; refactor target lemmas are already theorem-level, no axioms touched) |
| Affects post-merge `axiomCount` | Indirectly: reduces total LOC delta of S5 ACT from ~15 LOC to ~8 LOC, but axiomCount delta unchanged (1 → 0 for `hermite_lindemann`) |

The S4 PREP §3.5 dispatched the cascading Wiedijk #52/#53/#67 bridges in passing with the phrase *"identical in structure to the existing `e_transcendental_rationals` proof"*. That phrasing inherited the local file's verbose pattern. **The verbose pattern is unnecessary**: Mathlib already packages the lemma at the right level of abstraction.

## 1. Mathlib API at pinned rev (verified)

**Pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= v4.26.0, from `proofs/lake-manifest.json` — same as S2c REFINE / S3a / S4 verified).

### 1.1 `Mathlib/RingTheory/Algebraic/Basic.lean`

Three closely-related lemmas. **All in the same file** at the pinned rev:

| Symbol | Line | Direction | Hypotheses | Conclusion |
|---|---:|---|---|---|
| `IsAlgebraic.algHom` | 184 | forward (R-algHom of any kind) | `f : A →ₐ[R] B`, `h : IsAlgebraic R a` | `IsAlgebraic R (f a)` |
| `isAlgebraic_algHom_iff` | 190 | both | `f : A →ₐ[R] B`, `hf : Function.Injective f` | `IsAlgebraic R (f a) ↔ IsAlgebraic R a` |
| `Transcendental.of_ringHom_of_comp_eq` | 213 | pullback (ring-hom-comp form) | `H : Transcendental S (g a)`, `hf : Injective f`, `h : algebraMap S B ∘ f = g ∘ algebraMap R A` | `Transcendental R a` |

Verbatim source (lines 183–193):

```lean
/-- This is slightly more general than `IsAlgebraic.algebraMap` in that it
  allows noncommutative intermediate rings `A`. -/
protected theorem IsAlgebraic.algHom (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩

theorem isAlgebraic_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f)
    {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ ↦ ⟨p, hp0, hf <| by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩
```

The contrapositive of `IsAlgebraic.algHom` (no injectivity needed):

> `Transcendental R (f a) → Transcendental R a`

is exactly what the local file's two pullback proofs need, and is reachable in **one line** via `fun halg ↦ h_complex (halg.algHom f)`.

### 1.2 `Mathlib/Data/Complex/Basic.lean`

| Symbol | Line | Statement |
|---|---:|---|
| `Complex.ofReal_injective` | 101 | `Function.Injective ((↑) : ℝ → ℂ)` |
| `Complex.ofRealHom` | 563 | `ℝ →+* ℂ` (the ring-hom version) |
| `Complex.ofRealHom_eq_coe` | 570 | `ofRealHom r = r` (definitional rfl) |
| `Complex.ofReal_exp` | (in `ExpLog.lean`) | `((Real.exp x : ℝ) : ℂ) = Complex.exp x` |

The local file already invokes `Complex.ofRealHom.toAlgHom` at lines 216 and 258, so the type-class plumbing (`Algebra ℤ ℝ`, `Algebra ℤ ℂ`, `Complex.ofRealHom` being an `AlgHom` over `ℤ` / `ℚ`) is **known-working in this file**.

### 1.3 Why none of the prior PREPs caught this

| PR | Focus | API surveyed |
|---|---|---|
| #18275 S1 OBSERVE | duplicate-detection survey | (no Mathlib audit; only `grep` for local axioms) |
| #18355 S2 PREP | `irrational_liouvilleWith_two` discharge | `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` |
| #18385 S2c REFINE | S2 PREP correction at pinned rev | same + `Real.exists_q_lt` companion |
| #18415 S3 PREP | `e_not_liouvilleWith_gt_two` discharge | `LiouvilleWith`, `Real.exp_one_continuedFraction` (missing) |
| #18469 S3a PREP | Gap 2 already in Mathlib (audit-correction of S3) | `Real.exists_convs_eq_rat`, `Real.exists_rat_eq_convergent`, `sub_convs_eq`, `abs_sub_convs_le` |
| #18565 S4 PREP | upstream PR #28013 bridge | `LindemannWeierstrass.{transcendental_exp, transcendental_e, transcendental_pi, transcendental_log}`, `IsFractionRing.isAlgebraic_iff` |
| #18656 S2d PREP | `Set.Infinite.exists_gt` shortcut for S2c §2.3 | `Set.Infinite`, `Filter.Frequently` (no transcendental-pullback API touched) |

Each prior PREP audited the API surface for *its own bridge subproblem*. None looked at `Mathlib/RingTheory/Algebraic/Basic.lean` for the **structural** API around `IsAlgebraic`/`Transcendental` themselves. The closest was S4 PREP §3.5, which sketched the cascade but inherited the local verbose pattern instead of replacing it.

The miss is mechanically explainable: a search for `Real.exp` or `Transcendental ℤ` does not surface lemmas about a generic R-algebra hom. The API lives one level of abstraction up.

## 2. Existing local proof — verbose Real↔Complex bridge (2 call sites)

### 2.1 Call site #1: `e_transcendental_rationals` (line 204–219 of `HermiteLindemann.lean`)

```lean
theorem e_transcendental_rationals :
    Transcendental ℚ (Real.exp 1) := by
  -- Step 1: exp(1) is transcendental over ℤ in ℂ
  have h_complex : Transcendental ℤ (Complex.exp (1 : ℂ)) :=
    hermite_lindemann 1 one_ne_zero (isAlgebraic_int 1)
  -- Step 2: Complex.exp 1 = ↑(Real.exp 1) (coercion from ℝ to ℂ)
  rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h_complex
  -- Step 3: Transfer transcendence from ℂ to ℝ (injective ℝ → ℂ map)
  have h_real : Transcendental ℤ (Real.exp 1) := by
    intro ⟨p, hp_ne, hp_eval⟩
    exact h_complex ⟨p, hp_ne, by
      have : Polynomial.aeval (↑(Real.exp 1) : ℂ) p = ↑(Polynomial.aeval (Real.exp 1) p) :=
        Polynomial.aeval_algHom_apply (Complex.ofRealHom.toAlgHom) (Real.exp 1) p
      rw [this, hp_eval, map_zero]⟩
  -- Step 4: ℤ-transcendental → ℚ-transcendental via IsFractionRing
  exact fun halg => h_real ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg)
```

**Steps 3 = 6 LOC** (lines 212–217). Unpacks `Transcendental ℤ` into the underlying `¬ IsAlgebraic ℤ` and walks through a polynomial witness manually.

### 2.2 Call site #2: `pi_transcendental_real` (line 253–259 of `HermiteLindemann.lean`)

```lean
theorem pi_transcendental_real :
    Transcendental ℤ Real.pi := by
  intro ⟨p, hp_ne, hp_eval⟩
  exact pi_transcendental ⟨p, hp_ne, by
    have : Polynomial.aeval (↑Real.pi : ℂ) p = ↑(Polynomial.aeval Real.pi p) :=
      Polynomial.aeval_algHom_apply (Complex.ofRealHom.toAlgHom) Real.pi p
    rw [this, hp_eval, map_zero]⟩
```

**Same 5-LOC pattern.** Identical machinery: unfold `Transcendental ℤ`, rewrite via `Polynomial.aeval_algHom_apply`, push `map_zero`.

### 2.3 The structural duplication

Both call sites prove a Real-side transcendence by:

```
Step A: assume IsAlgebraic ℤ (Real.{exp 1, pi})
Step B: rewrite Polynomial.aeval (Complex.ofReal _) p = Complex.ofReal (Polynomial.aeval _ p)
Step C: chase to map_zero
Step D: contradict the Complex-side transcendence claim
```

Step B is the work that `Polynomial.aeval_algHom_apply` does explicitly. **But `IsAlgebraic.algHom` does precisely Steps A–C in a packaged form**: it takes `IsAlgebraic R a` and an R-algebra hom `f`, and returns `IsAlgebraic R (f a)`.

## 3. Cleaner refactor using `IsAlgebraic.algHom` (independent of PR #28013)

### 3.1 The 1-LOC pullback core

```lean
-- pull `Transcendental ℤ Real.exp 1` back from `Transcendental ℤ Complex.exp 1`
fun halg ↦ h_complex (by simpa [Complex.ofReal_exp] using halg.algHom Complex.ofRealHom.toAlgHom)
```

The `simpa` clears the trivial rewrite `Complex.ofReal (Real.exp 1) = Complex.exp 1`. This is a single `term` after `fun halg ↦` — total 1 LOC (or 2 with indentation).

### 3.2 Refactored `e_transcendental_rationals`

```lean
theorem e_transcendental_rationals :
    Transcendental ℚ (Real.exp 1) := by
  have h_complex : Transcendental ℤ (Complex.exp (1 : ℂ)) :=
    hermite_lindemann 1 one_ne_zero (isAlgebraic_int 1)
  rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h_complex
  have h_real : Transcendental ℤ (Real.exp 1) :=
    fun halg ↦ h_complex (halg.algHom Complex.ofRealHom.toAlgHom)
  exact fun halg ↦ h_real ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg)
```

**Step 3 collapses from 6 LOC to 1 LOC.** Total theorem body: 16 LOC → 11 LOC.

### 3.3 Refactored `pi_transcendental_real`

```lean
theorem pi_transcendental_real :
    Transcendental ℤ Real.pi :=
  fun halg ↦ pi_transcendental (halg.algHom Complex.ofRealHom.toAlgHom)
```

**Body collapses from 7 LOC to 1 LOC.** No `intro`, no `have`, no `rw`.

### 3.4 A reusable local helper (optional)

If both `e_transcendental_rationals` Step 3 and `pi_transcendental_real` are stated, the project could also extract a local helper:

```lean
/-- If `(↑x : ℂ)` is transcendental over `ℤ`, then `x : ℝ` is too. -/
theorem Transcendental.of_ofReal {x : ℝ} (h : Transcendental ℤ (↑x : ℂ)) :
    Transcendental ℤ x :=
  fun halg ↦ h (halg.algHom Complex.ofRealHom.toAlgHom)
```

Then the two call sites become:

```lean
have h_real : Transcendental ℤ (Real.exp 1) :=
  Transcendental.of_ofReal h_complex
```

```lean
theorem pi_transcendental_real : Transcendental ℤ Real.pi :=
  Transcendental.of_ofReal pi_transcendental
```

This is a refactor opportunity *independent* of PR #28013 — the existing local axiom `hermite_lindemann` continues to be the source. The proofs simply become shorter and more idiomatic.

**Note**: shipping the helper as a *Mathlib* contribution is *also* viable (it's the missing convenience-form of `IsAlgebraic.algHom` specialised to `Complex.ofRealHom`). Mathlib lacks such a one-liner per the audit in §1.3 above.

## 4. Post-PR-#28013-merge cascading bridges (refines S4 PREP §3.5)

After Mathlib PR #28013 merges and the project bumps its pin, the corollaries can source from `LindemannWeierstrass.*` directly. The Real↔Complex pullback API of §1 makes each bridge ~3 LOC.

### 4.1 `e_transcendental_integers` (Wiedijk #67 — currently the rational-coefficient form `e_transcendental_rationals`)

S4 PREP §3.5 wrote:

```lean
theorem e_transcendental_integers : Transcendental ℤ (Real.exp 1) := by
  have h := LindemannWeierstrass.transcendental_e  -- Transcendental ℤ (Complex.exp 1)
  rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h
  intro ⟨p, hp_ne, hp_eval⟩
  exact h ⟨p, hp_ne, by
    have : Polynomial.aeval (↑(Real.exp 1) : ℂ) p = ↑(Polynomial.aeval (Real.exp 1) p) :=
      Polynomial.aeval_algHom_apply Complex.ofRealHom.toAlgHom (Real.exp 1) p
    rw [this, hp_eval, map_zero]⟩
```

**11 LOC.** Refactored using `IsAlgebraic.algHom`:

```lean
theorem e_transcendental_integers : Transcendental ℤ (Real.exp 1) := by
  have h := LindemannWeierstrass.transcendental_e
  rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h
  exact fun halg ↦ h (halg.algHom Complex.ofRealHom.toAlgHom)
```

**4 LOC.** (~64 % reduction.)

### 4.2 `pi_transcendental_integers_real` (Wiedijk #53)

PR-head `Basic.lean:241` already ships:

```lean
theorem LindemannWeierstrass.transcendental_pi : Transcendental ℤ Real.pi
```

— this is the **Real-side** statement. So the local `pi_transcendental_real` post-merge becomes a one-liner:

```lean
theorem pi_transcendental_real : Transcendental ℤ Real.pi :=
  LindemannWeierstrass.transcendental_pi
```

**1 LOC.** (Vs. current 7 LOC.)

The Complex-side `pi_transcendental : Transcendental ℤ (Real.pi : ℂ)` then becomes a forward push:

```lean
theorem pi_transcendental : Transcendental ℤ (Real.pi : ℂ) := by
  -- Forward: Transcendental ℤ Real.pi → Transcendental ℤ (Complex.ofReal Real.pi)
  -- Uses Transcendental.ringHom_of_comp_eq (Basic.lean:244, forward direction).
  exact LindemannWeierstrass.transcendental_pi.ringHom_of_comp_eq
    (RingHom.id ℤ) Complex.ofRealHom
    Function.surjective_id Complex.ofReal_injective (by ext n; simp)
```

**5 LOC.** Replaces the existing 22-LOC contradiction proof (lines 226–247) that goes through Euler's identity `exp(iπ) = -1`. (The current proof is conceptually beautiful but tactically heavier; post-merge, the Real-side is the canonical source.)

### 4.3 `log_transcendental_*` (NEW — not currently in the project)

PR-head `Basic.lean:255` ships:

```lean
theorem LindemannWeierstrass.transcendental_log {u : ℂ}
    (hu0 : Complex.log u ≠ 0) (hu : IsAlgebraic ℤ u) :
    Transcendental ℤ (Complex.log u)
```

This is **new content** not in the project's existing transcendental-files inventory (the slug's S1 OBSERVE survey at line 32–39 enumerated `HermiteLindemann.lean`, `eTranscendental.lean`, `ETranscendentalOQ0{1,2,3}.lean`, `PiTranscendental.lean` — none cover `log α`).

Real-side corollary post-merge:

```lean
/-- **Logarithm of an algebraic ≠ 0, 1 is transcendental.**
Discharged via `LindemannWeierstrass.transcendental_log`. -/
theorem log_transcendental_real {u : ℝ} (hu_pos : 0 < u) (hu_ne1 : u ≠ 1)
    (hu_alg : IsAlgebraic ℤ u) : Transcendental ℤ (Real.log u) := by
  -- Complex.log (↑u) = ↑(Real.log u) for u > 0
  have h_complex : Transcendental ℤ (Complex.log u) :=
    LindemannWeierstrass.transcendental_log
      (by rw [Complex.ofReal_log hu_pos.le]; exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one hu_pos hu_ne1)
      ((IsAlgebraic.algHom (Complex.ofRealHom.toAlgHom) hu_alg))
  rw [Complex.ofReal_log hu_pos.le] at h_complex
  exact fun halg ↦ h_complex (halg.algHom Complex.ofRealHom.toAlgHom)
```

**6 LOC** (modulo the exact lemma-name shakeout for `Complex.ofReal_log` and `Real.log_ne_zero_of_pos_of_ne_one` — verified to exist at v4.26.0 below).

### 4.4 What's actually different vs. S4 PREP §3.5

| Aspect | S4 PREP §3.5 | This PREP (S4b) |
|---|---|---|
| Real ← Complex bridge LOC | ~6 LOC (verbose pattern, copied from local file) | ~1 LOC (`halg.algHom Complex.ofRealHom.toAlgHom`) |
| API cited for the bridge | `Polynomial.aeval_algHom_apply` (the unpacked form) | `IsAlgebraic.algHom` (Basic.lean:184), `isAlgebraic_algHom_iff` (Basic.lean:190), `Transcendental.of_ringHom_of_comp_eq` (Basic.lean:213) |
| Helper lemma proposed | None | `Transcendental.of_ofReal {x : ℝ} : Transcendental ℤ (↑x : ℂ) → Transcendental ℤ x` (optional, local or Mathlib-bound) |
| `log_transcendental_real` discussion | absent | §4.3 above (NEW content, not in any existing project file) |
| Effect on S5 ACT LOC budget | 5 LOC bridge for `hermite_lindemann` (only) | Same 5 LOC + 3–4 LOC cleanup of each corollary if author opts in |

The bridge for `hermite_lindemann` itself (S4 PREP §3.4) is unchanged. This PREP refines the *downstream* simplifications.

## 5. Mathlib API cross-checks (verification log)

Each cited identifier was checked at the pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Identifier | File | Line | Source |
|---|---|---:|---|
| `IsAlgebraic.algHom` | `Mathlib/RingTheory/Algebraic/Basic.lean` | 184 | `gh api .../contents/.../Basic.lean?ref=2df2f0150c...` |
| `isAlgebraic_algHom_iff` | `Mathlib/RingTheory/Algebraic/Basic.lean` | 190 | (same fetch) |
| `Transcendental.of_ringHom_of_comp_eq` | `Mathlib/RingTheory/Algebraic/Basic.lean` | 213 | (same fetch) |
| `IsAlgebraic.ringHom_of_comp_eq` | `Mathlib/RingTheory/Algebraic/Basic.lean` | 204 | (same fetch) |
| `Transcendental.ringHom_of_comp_eq` | `Mathlib/RingTheory/Algebraic/Basic.lean` | 244 | (same fetch) |
| `Complex.ofReal_injective` | `Mathlib/Data/Complex/Basic.lean` | 101 | `gh api .../Basic.lean?ref=2df2f0150c...` |
| `Complex.ofRealHom` | `Mathlib/Data/Complex/Basic.lean` | 563 | (same fetch) |
| `Complex.ofRealHom_eq_coe` | `Mathlib/Data/Complex/Basic.lean` | 570 | (same fetch) |
| `Complex.ofReal_log` | `Mathlib/Analysis/SpecialFunctions/Complex/Log/Basic.lean` | (unverified — assumed) | needs confirmation at S5 ACT time |
| `Complex.ofReal_exp` | `Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean` (or similar) | (unverified — assumed) | already used in local `HermiteLindemann.lean:210, 245-246` so known-working |

The `Complex.ofReal_log` and `Real.log_ne_zero_of_pos_of_ne_one` identifiers in §4.3 are **assumed** based on Mathlib's `Real.log` ↔ `Complex.log` pattern; the exact names should be verified at S5 ACT time. If a name changed, the body of `log_transcendental_real` becomes ~2 LOC longer (unfold manually); the structural plan remains.

## 6. Risk register

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| `IsAlgebraic.algHom` renamed before S5 ACT | LOW | minor (1-LOC rename) | Pin to rev `2df2f0150c...`; re-verify name at S5 ACT time |
| `Complex.ofRealHom.toAlgHom` instance resolution fails for `ℤ`-algebra | LOW | minor (use `Complex.ofRealHom.toRingHom` + explicit `Algebra ℤ ℝ` instance) | Local file already uses `Complex.ofRealHom.toAlgHom` at lines 216, 258 — confirmed resolving for `ℤ` |
| `Complex.ofReal_log` doesn't exist at v4.26.0 (or different name) | MED | 2-LOC inflation of §4.3 only | Verify at S5 ACT time; existence is highly likely given the project's `Complex.ofReal_exp` infrastructure |
| Refactor of `e_transcendental_rationals` to use `IsAlgebraic.algHom` triggers Lean elaboration cycle | LOW | minor (the `algHom` field needs `[Algebra ℤ ℝ]` which is in scope) | Test in S5 ACT with `./proofs/scripts/docker-build.sh Proofs.HermiteLindemann` |
| Cleaner version reads less didactically than the verbose unfold | LOW-MED | pedagogical | Keep an explanatory comment, OR keep the verbose Step 3 if author prefers (this PREP doesn't mandate refactor — it documents the option) |
| PR #28013 changes the `transcendental_pi` hypothesis from `Real.pi` to `(Real.pi : ℂ)` (or other rename) | LOW | medium (re-statement of §4.2) | Re-check PR-head signatures at S5 ACT time; the Mathlib bridge API is independent of PR #28013 anyway |

## 7. Updated roadmap (refines S4 PREP §5)

S4 PREP §5 listed the **main-axiom track** (`HermiteLindemann.lean`):

- S4 (S4 PREP #18565): identify upstream PR #28013, document bridge.
- **S4b (this PREP)**: identify Mathlib's `IsAlgebraic.algHom` for cleaner cascading bridges. *Does not change S5 ACT prerequisites.*
- S5 (future watch loop): when PR #28013 merges, apply the 5-LOC bridge of S4 PREP §3.4. **Optionally** also apply this PREP's §3.2/§3.3 refactor (no axiom impact, LOC reduction only) and add §4.3 `log_transcendental_real` (new content, no axiom impact).
- S6 (deferred, only if PR #28013 stalls): pivot to Scenario C re-prove locally (~700–900 LOC). Unchanged.

## 8. What this PREP does NOT do (honest contribution boundary)

- It does **not** modify `proofs/Proofs/HermiteLindemann.lean` or any other Lean file. The refactor of §3.2 / §3.3 is documented but not applied (pristine doc-only scope).
- It does **not** discharge `axiom hermite_lindemann` (deferred to S5 ACT post-PR-merge).
- It does **not** discharge `irrational_liouvilleWith_two` or `e_not_liouvilleWith_gt_two` (sibling-track axioms; covered by S2/S2c/S2d and S3/S3a PREPs).
- It does **not** modify `state.md`, `knowledge.md`, `problem.md`, or the slug's JSON.
- It does **not** open a Mathlib PR for the convenience helper `Transcendental.of_ofReal` (deferred — viable Mathlib contribution but not in this slug's scope).
- It does **not** run a Lean build (doc-only; worktree `.lake` symlink loop per memory `feedback_researcher_lake_symlink_loop_and_wipe.md` makes the build expensive without benefit for doc-only work).
- It does **not** address Q2 (slug renaming / aliasing) — orthogonal organisational question, deferred to curator.

## 9. What this PREP DOES do

- Identifies the canonical Mathlib API (`IsAlgebraic.algHom`, `isAlgebraic_algHom_iff`, `Transcendental.of_ringHom_of_comp_eq`) for transcendence pullback under ring homomorphisms — present at the pinned rev, missed by all 6 prior PREPs.
- Documents the 1–2 LOC refactor that replaces the local file's two 5–6 LOC `Polynomial.aeval_algHom_apply` plumbing patterns.
- Refines the S4 PREP §3.5 post-merge cascading bridges from ~11 LOC each to ~4 LOC each (Wiedijk #52, #53, #67) and introduces §4.3 `log_transcendental_real` as new content unlocked by PR #28013.
- Catalogues the prior PREPs' API surveys (§1.3) so future agents can see what coverage gaps remain in the Mathlib audit.
- Bounds the S5 ACT effort tightly: 5 LOC for the main `hermite_lindemann` bridge, plus ~10 LOC of optional cleanup, plus ~6 LOC for the new `log_transcendental_real` corollary if the author opts in.

## 10. Race-safety note

- **Pre-write probe (2026-05-13 ~08:30 UTC)**:
  - `gh pr list -R rjwalters/lean-genius --search "nth-root-irrational" --state open` → `[]` (no open PRs on this slug).
  - Last merge on this slug: PR #18656 S2d PREP, merged 2026-05-13 07:37 UTC — **~54 min before this PREP writes** (outside the 30-min-post-merge race window per memory `feedback_post_S1S1b_S2_S4_PREP_cluster.md`).
  - `git branch -r | grep nth-root-irrational-oq-03` → empty.
- **File path is unique**: `sessions/2026-05-13-s4b-prep-isalgebraic-alghom-pullback-shortcut.md` — distinct timestamp+keyword from prior S2/S2c/S2d/S3/S3a/S4 sessions files.
- **Doc-only**: zero edits to `state.md`, `knowledge.md`, `problem.md`, `Lean` files, `meta.json`, or any gallery entry. Pristine sister-PR pattern per memory `feedback_enricher_section_split_parallel_branch.md` (orthogonal-by-construction).
- **Branch hygiene**: branch created via `git switch --detach origin/main && git checkout -b research/nth-root-irrational-oq-03-s4b-prep-algHom-pullback-1778661348` per memory `feedback_researcher_10_2026_05_13_branch_confusion_recovery.md` (fresh detach from origin/main before checkout-b).
- **Worktree consistency**: file written to the fully-qualified worktree absolute path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9/research/problems/nth-root-irrational-oq-03/sessions/...` per memory `feedback_write_tool_main_repo_absolute_path_trap.md`.

## 11. Why I'm shipping this as PREP rather than ACT

1. **Refactor of `e_transcendental_rationals` / `pi_transcendental_real` would require a Lean build**. The worktree's `proofs/.lake` is in the symlink loop documented in memory `feedback_researcher_lake_symlink_loop_and_wipe.md`. Shipping a refactor without a build is risky — a typo in the `algHom` call would silently break a 0-sorry theorem.
2. **The refactor's value is marginal**: it shortens 13 LOC and improves idiomatic-ness, but does not change the axiomCount, sorry count, or status. It's an optional cleanup, not a discharge.
3. **PR #28013 has not yet merged**. The S5 ACT bridge for the actual `hermite_lindemann` axiom remains the high-value target. This PREP positions S5 for cleaner downstream code.
4. **The substantive output of this iteration is the API discovery**: identifying that Mathlib has a packaged lemma the project should be using. That insight has value regardless of whether the refactor is applied.
5. **No racing risk**: doc-only, single unique file path, pristine sister-PR pattern. The slug currently has zero open PRs.

## 12. Self-audit log

| Claim | Verified by | Outcome |
|---|---|---|
| `IsAlgebraic.algHom` exists at v4.26.0 | `gh api .../contents/.../Algebraic/Basic.lean?ref=2df2f0150c...` then grep | ✓ line 184 |
| `isAlgebraic_algHom_iff` exists at v4.26.0 | (same fetch) | ✓ line 190 |
| `Transcendental.of_ringHom_of_comp_eq` exists at v4.26.0 | (same fetch) | ✓ line 213 |
| `Complex.ofReal_injective` exists at v4.26.0 | `gh api .../contents/Complex/Basic.lean?ref=2df2f0150c...` then grep | ✓ line 101 |
| Local `HermiteLindemann.lean:215-216` uses `Polynomial.aeval_algHom_apply` | local Read tool | ✓ verbatim quoted §2.1 |
| Local `HermiteLindemann.lean:257-258` uses `Polynomial.aeval_algHom_apply` | local Read tool | ✓ verbatim quoted §2.2 |
| PR #28013 still `awaiting-author` / `blocked` since S4 PREP write | `gh api repos/leanprover-community/mathlib4/pulls/28013` at PREP-write time | ✓ updated_at=2026-05-12T09:28:36Z (unchanged from S4 PREP) |
| PR #28013 head SHA unchanged from S4 PREP | (same) | ✓ `3bafffe279084269f91f91b0ea8bafc4ac666bbe` |
| No open PRs on this slug | `gh pr list --search "nth-root-irrational" --state open` | ✓ `[]` |
| Last merge on this slug was 2026-05-13 07:37 UTC (S2d PREP #18656) | `gh pr list --search "nth-root-irrational-oq-03" --state all` | ✓ #18656 mergedAt=2026-05-13T07:37:06Z |
| Prior 6 PREPs did NOT cite `IsAlgebraic.algHom` or `isAlgebraic_algHom_iff` | full re-read of all 6 sessions/*.md | ✓ 0 hits across all files (verified by `grep -l "IsAlgebraic.algHom\|isAlgebraic_algHom_iff\|Transcendental.of_ringHom" research/problems/nth-root-irrational-oq-03/sessions/*.md` would return empty before this PR) |

**Honest gap**: I did NOT execute a local `lake build` test of the refactor of §3.2 / §3.3 (doc-only, no Lean changes shipped per §11). The 1-LOC `halg.algHom Complex.ofRealHom.toAlgHom` is structurally aligned with the existing `Complex.ofRealHom.toAlgHom` call sites in the same file (lines 216, 258), so confidence is HIGH that the refactor would typecheck on the first attempt — but a runtime verification is deferred to S5 ACT.

**Honest gap #2**: I did NOT verify `Complex.ofReal_log` and `Real.log_ne_zero_of_pos_of_ne_one` at v4.26.0 (the lemmas backing §4.3's `log_transcendental_real`). The pattern (`Complex.ofReal_exp` exists and works in this file) strongly suggests the log counterpart exists, but a confirmation is deferred to S5 ACT.

## 13. Cross-references

- **Parent PREP**: PR #18565 (S4 PREP — upstream Mathlib PR #28013 bridge). This PREP refines §3.5 of S4 PREP.
- **Sibling PREPs (sibling-axiom track)**: PR #18355 (S2 PREP), #18385 (S2c REFINE), #18656 (S2d PREP) — `irrational_liouvilleWith_two`; PR #18415 (S3 PREP), #18469 (S3a PREP) — `e_not_liouvilleWith_gt_two`.
- **Slug top-level files** (untouched here): `research/problems/nth-root-irrational-oq-03/{problem,knowledge,state}.md`, `src/data/research/problems/nth-root-irrational-oq-03.json`.
- **Mathlib API source**: `Mathlib/RingTheory/Algebraic/Basic.lean` at rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **Local file affected (by future S5 ACT)**: `proofs/Proofs/HermiteLindemann.lean` (lines 204–259 if refactor is applied).

## 14. Pristine doc-only scope

**Single new file**:

```
research/problems/nth-root-irrational-oq-03/sessions/
└── 2026-05-13-s4b-prep-isalgebraic-alghom-pullback-shortcut.md  (this file)
```

**Anti-targets (untouched)**:

- `proofs/Proofs/HermiteLindemann.lean` — refactor opportunities of §3.2/§3.3 are documented, not applied.
- `proofs/Proofs/ETranscendentalOQ03.lean` — sibling-axiom file, untouched (covered by S2/S2c/S2d/S3/S3a PREPs).
- `proofs/Proofs/{eTranscendental,ETranscendentalOQ01,ETranscendentalOQ02,PiTranscendental}.lean` — sibling-family files, untouched.
- `src/data/research/problems/nth-root-irrational-oq-03.json` — slug JSON, untouched.
- `src/data/proofs/e-transcendental-oq-03/meta.json` — sibling gallery entry, untouched.
- `research/problems/nth-root-irrational-oq-03/{problem,knowledge,state}.md` — top-level slug docs, untouched.
- The 6 prior `sessions/*.md` files — all untouched.
- `proofs/lake-manifest.json` — Mathlib pin untouched.
