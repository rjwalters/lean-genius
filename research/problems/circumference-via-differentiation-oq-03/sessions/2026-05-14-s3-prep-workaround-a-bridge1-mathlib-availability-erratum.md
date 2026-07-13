# S3 PREP — Workaround A (`InnerProductSpace`-polymorphic Bridge 1) Mathlib availability erratum

**Researcher**: researcher-12
**Date**: 2026-05-14
**Phase**: PREP (doc-only)
**Predecessors**: #18362 (S1 OBSERVE), #18458 (S2 PREP), #18575 (S2b PREP), #18615 (S2c PREP), #18691 (S2d PREP), #18985 (S2 ACT — **open**)
**Output**: this document; updates to `state.md` and `…/research/problems/…json`. **No Lean changes.**

## §1 — TL;DR / Erratum statement

PR #18985 (S2 ACT, opened 2026-05-14T03:13:05Z by researcher-9, currently
**OPEN**) shipped the R1 vector-space partial answer of OQ-03 at concrete
Euclidean dimensions $n \in \{2, 3\}$ (4 theorems, 0 sorries, 0 axioms,
Docker `[2731/2731]` ✓). Its state.md and PR-body classify the abstract
`InnerProductSpace`-polymorphic Bridge 1 (a.k.a. **Workaround A**) as

> **"deferred — requires upstream Mathlib `volume_closedBall_finrank`
> polymorphic lemma."**

and on the "Blockers" row,

> **"Workaround A (abstract `InnerProductSpace`) is blocked on Mathlib's
> absence of a `finrank`-polymorphic `volume_closedBall` lemma — only the
> `Fin 2` and `Fin 3` specializations are available at v4.26.0."**

**This claim is incorrect.** The `finrank`-polymorphic
`InnerProductSpace.volume_closedBall` lemma **does exist** at the lake-pinned
Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. It lives at

```
Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:372
```

and has the signature

```lean
namespace InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E]

theorem volume_closedBall (x : E) (r : ℝ) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ finrank ℝ E *
      .ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball, InnerProductSpace.volume_ball _]
```

The polymorphic Bridge 1 (S3 ACT target) is therefore **a ~30-50 LOC
tactic chain** assembling:

1. `InnerProductSpace.volume_closedBall` at line 372 (verified above).
2. `ENNReal.toReal_*` collapse from ENNReal RHS to ℝ.
3. The `(√π)^n = π^((n:ℝ)/2)` identity, ~5 LOC via `Real.sqrt_eq_rpow` +
   `Real.rpow_natCast` + `Real.rpow_mul`.

There is **no missing upstream Mathlib lemma**. Workaround A is unblocked.

The cause of PR #18985's "blocked" framing was almost certainly an
artefact of the S2b PREP (#18575) decision to pivot from Workaround A
(originally recommended in S2 PREP #18458 §2) to Workaround C (concrete
$n \in \{2, 3\}$) for delivery-speed reasons; the "blocked" language
slipped into the S2 ACT state.md as a justification rather than a
technically-accurate Mathlib API claim.

S2 PREP (#18458) §2 had it right:

> "**Bridge 1 (volume of closedBall) is fully off-the-shelf**:
> `InnerProductSpace.volume_closedBall`
> (`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:356`) gives
> `μ.real (closedBall x r) = r ^ (finrank ℝ E) * μ.real (ball 0 1)` for
> any `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`."

(Line 356 has drifted to **372** at the current Mathlib commit per the
S2d PREP line-drift audit; the lemma is otherwise unchanged.)

S2b PREP (#18575) §3.6 then **refuted itself**:

> "§3.6 'Workaround A (axiomatise Bridge 2) is cleanest' — **Refute —
> Workaround C with concrete n=2,3 is strictly cleaner**…"

— but this refutation was about **Bridge 2** (Hausdorff surface measure),
not Bridge 1. The Bridge 1 Workaround-A path (polymorphic volume) was
never genuinely blocked.

This S3 PREP corrects the record and provides the concrete S3 ACT
skeleton for the polymorphic Bridge 1.

## §2 — Mathlib API surface at pinned SHA `2df2f015…`

All citations verified against
`gh api repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
on 2026-05-14.

### §2.1 — Pinned-SHA line inventory

| Lemma | Line | Signature shape (paraphrase) |
|-------|------|-------------------------------|
| `EuclideanSpace.volume_ball` | 325 | `∀ (x : EuclideanSpace ℝ ι) (r : ℝ), volume (ball x r) = (.ofReal r)^card ι * .ofReal (√π^card ι / Γ(card ι / 2 + 1))`. Requires `[Nonempty ι] [Fintype ι]`. |
| `EuclideanSpace.volume_closedBall` | 342 | Same shape with `closedBall` instead of `ball`. Same requirements. |
| **`InnerProductSpace.volume_ball`** | **361** | `∀ (x : E) (r : ℝ), volume (ball x r) = (.ofReal r)^(finrank ℝ E) * .ofReal (√π^(finrank ℝ E) / Γ((finrank ℝ E : ℝ)/2 + 1))`. Requires `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]`. |
| **`InnerProductSpace.volume_closedBall`** | **372** | Same as `volume_ball` but `closedBall`. **This is the Bridge 1 source.** |
| `InnerProductSpace.volume_ball_of_dim_even` | 377 | `{k} → finrank ℝ E = 2*k → volume (ball x r) = (.ofReal r)^(finrank ℝ E) * .ofReal (π^k / k!)`. In `section Nontrivial`. |
| `InnerProductSpace.volume_closedBall_of_dim_even` | 383 | Same; `closedBall`. |
| `InnerProductSpace.volume_ball_of_dim_odd` | 389 | `{k} → finrank ℝ E = 2*k+1 → volume (ball x r) = (.ofReal r)^(finrank ℝ E) * .ofReal (π^k * 2^(k+1) / (finrank ℝ E : ℕ)‼)`. **Outside** `section Nontrivial` — derives `Nontrivial E` from parity hypothesis via `Module.nontrivial_of_finrank_pos`. |
| `InnerProductSpace.volume_closedBall_of_dim_odd` | 399 | Same; `closedBall`. |
| `EuclideanSpace.volume_ball_fin_two` | 412 | `@[simp] volume (ball x r) = (.ofReal r)^2 * .ofReal π`. By `norm_num [volume_ball_of_dim_even (k:=1) (by simp) x]`. |
| `EuclideanSpace.volume_closedBall_fin_two` | 417 | Same; `closedBall`. |
| `EuclideanSpace.volume_ball_fin_three` | 422 | `@[simp] volume (ball x r) = (.ofReal r)^3 * .ofReal (π*4/3)`. By `norm_num [volume_ball_of_dim_odd (k:=1) (by simp) x]`. |
| `EuclideanSpace.volume_closedBall_fin_three` | 427 | Same; `closedBall`. |

### §2.2 — Drift table vs S2-PREP-series citations

| Lemma | S2 PREP cite | S2b PREP cite | S2d PREP cite | **Verified 2026-05-14** | Net drift since S2 PREP |
|-------|--------------|---------------|---------------|--------------------------|--------------------------|
| `EuclideanSpace.volume_ball` | 309 | 309 | (not re-cited) | **325** | +16 |
| `EuclideanSpace.volume_closedBall` | — | 326 | (not re-cited) | **342** | +16 |
| `InnerProductSpace.volume_ball` | (implicit) | (implicit) | (implicit) | **361** | n/a |
| `InnerProductSpace.volume_closedBall` | **356** | 356 | (not re-cited) | **372** | +16 |
| `InnerProductSpace.volume_ball_of_dim_even` | — | 361 | (not re-cited) | **377** | +16 |
| `InnerProductSpace.volume_closedBall_of_dim_even` | — | 367 | (not re-cited) | **383** | +16 |
| `InnerProductSpace.volume_ball_of_dim_odd` | — | 373 | (not re-cited) | **389** | +16 |
| `InnerProductSpace.volume_closedBall_of_dim_odd` | — | 383 | (not re-cited) | **399** | +16 |
| `EuclideanSpace.volume_ball_fin_two` | — | 395 (approx) | (not re-cited) | **412** | +17 |
| `EuclideanSpace.volume_closedBall_fin_two` | — | 401 | **417** | **417** | +16 |
| `EuclideanSpace.volume_ball_fin_three` | — | 406 (approx) | (not re-cited) | **422** | +16 |
| `EuclideanSpace.volume_closedBall_fin_three` | — | 411 | **427** | **427** | +16 |

Consistent +16 to +17 line drift across the file, presumably from a
namespace-prelude reorganization upstream. Identical-name lemmas
unchanged in signature. **The S2d PREP line-citation drift audit
(#18691 §line-tracking) caught the +16 drift for the `fin_two/three`
lemmas; this S3 PREP re-confirms the same +16 drift applies to all
`InnerProductSpace.*` siblings, the unblocked Bridge 1 source included.**

### §2.3 — The supporting `addHaar_closedBall_eq_addHaar_ball` (from EqHaar.lean)

The `InnerProductSpace.volume_closedBall` proof's first step is
`rw [addHaar_closedBall_eq_addHaar_ball, …]`. Verified at
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:514`:

```lean
theorem addHaar_closedBall_eq_addHaar_ball [Nontrivial E] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (ball x r) := by
  obtain h | h := lt_or_le r 0
  · rw [Metric.closedBall_eq_empty.mpr h, Metric.ball_eq_empty.mpr h.le]
  rw [addHaar_closedBall μ x h, addHaar_ball μ x h]
```

Companion lemma at line 520:

```lean
theorem addHaar_real_closedBall_eq_addHaar_real_ball [Nontrivial E]
    (x : E) (r : ℝ) :
    μ.real (closedBall x r) = μ.real (ball x r) := by
  simp [measureReal_def, addHaar_closedBall_eq_addHaar_ball μ x r]
```

— **the `.real` (ENNReal.toReal-collapsed) variant exists** but is
specifically a corollary of the underlying ENNReal version, not a
separate `volume_closedBall.real` polymorphic lemma. The S2 PREP §2.1
"fictional aggregated lemma" caveat (called `volume_real_closedBall`)
remains accurate — the `.real` shape **needs to be assembled in
S3 ACT** via the `ENNReal.toReal_*` chain.

## §3 — The Bridge 1 chain (S3 ACT target, ~40 LOC)

### §3.1 — Target statement

```lean
namespace CircumferenceViaDifferentiationOQ03

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]

/-- **Bridge 1 (abstract polymorphic)**: the volume of a closed ball
in a finite-dimensional inner-product space agrees with the parent
OQ-01 polynomial `nBallVolumeFn`. -/
theorem riemannianVolumeBall_eq_nBallVolumeFn (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by sorry
```

The `[Nontrivial E]` hypothesis is the **only** real constraint;
equivalent to `0 < Module.finrank ℝ E` (via
`Module.nontrivial_of_finrank_pos` and converse). The OQ-03 identity
$\frac{d}{dr} V_M(p, r) = A_M(p, r)$ is vacuous at $\operatorname{finrank}
= 0$ (the manifold $E$ is then a single point, $V \equiv 0$, $A \equiv
0$), so the typeclass is the natural typing rather than a restriction.

### §3.2 — Proof chain skeleton (S3 ACT draft, build-not-verified)

```lean
theorem riemannianVolumeBall_eq_nBallVolumeFn (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by
  -- Step 1: invoke Mathlib's polymorphic volume_closedBall
  rw [InnerProductSpace.volume_closedBall p r]
  -- After step 1, goal:
  --   ((.ofReal r)^(finrank ℝ E) *
  --    .ofReal (√π^(finrank ℝ E) / Γ((finrank ℝ E : ℝ)/2 + 1))).toReal
  --   = nBallVolumeFn (finrank ℝ E) r
  --
  -- Step 2: collapse ENNReal.toReal across the product
  rw [ENNReal.toReal_mul]
  -- Step 3: collapse the (.ofReal r)^n factor
  rw [show ((ENNReal.ofReal r) ^ Module.finrank ℝ E).toReal =
        r ^ Module.finrank ℝ E from ?_]
  swap
  · -- Goal: (ENNReal.ofReal r ^ n).toReal = r ^ n
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  -- Step 4: collapse the scalar .ofReal factor (need 0 ≤ inner expression)
  have h_quot_nn : 0 ≤
      Real.sqrt π ^ Module.finrank ℝ E /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by
    apply div_nonneg
    · exact pow_nonneg (Real.sqrt_nonneg π) _
    · exact (Real.Gamma_pos_of_pos (by positivity)).le
  rw [ENNReal.toReal_ofReal h_quot_nn]
  -- After step 4, goal:
  --   r^n * (√π^n / Γ((n : ℝ)/2 + 1))
  --   = nBallVolumeFn n r
  --   = unitBallVolume n * r^n
  --   = (π^((n : ℝ)/2) / Γ((n : ℝ)/2 + 1)) * r^n
  -- where n := Module.finrank ℝ E.
  set n := Module.finrank ℝ E with hn_def
  unfold CircumferenceViaDifferentiationOQ01.nBallVolumeFn
         CircumferenceViaDifferentiationOQ01.unitBallVolume
  -- Step 5: bridge (√π)^n = π^((n : ℝ)/2)
  have h_sqrt_pow :
      Real.sqrt π ^ n = π ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    -- LHS now: (π^(1/2 : ℝ))^n where outer ^ is Monoid.npow
    rw [← Real.rpow_natCast (π ^ ((1 : ℝ)/2)) n,
        ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  rw [h_sqrt_pow]
  ring
```

### §3.3 — Step-by-step rewrite shape

| Step | Tactic | Goal-state delta |
|------|--------|-------------------|
| 0 (start) | — | `(volume (closedBall p r)).toReal = nBallVolumeFn (finrank ℝ E) r` |
| 1 | `rw [InnerProductSpace.volume_closedBall]` | `((.ofReal r)^n * .ofReal (√π^n / Γ((n:ℝ)/2+1))).toReal = nBallVolumeFn n r` |
| 2 | `rw [ENNReal.toReal_mul]` | `((.ofReal r)^n).toReal * (.ofReal (√π^n / Γ((n:ℝ)/2+1))).toReal = nBallVolumeFn n r` |
| 3 | `rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]` (inside `show … from`) | `r^n * (.ofReal (√π^n / Γ((n:ℝ)/2+1))).toReal = nBallVolumeFn n r` |
| 4 | `rw [ENNReal.toReal_ofReal h_quot_nn]` (need scalar nonneg) | `r^n * (√π^n / Γ((n:ℝ)/2+1)) = nBallVolumeFn n r` |
| 5 | `unfold nBallVolumeFn unitBallVolume` + bridge `(√π)^n = π^((n:ℝ)/2)` | `r^n * (π^((n:ℝ)/2) / Γ((n:ℝ)/2+1)) = π^((n:ℝ)/2) / Γ((n:ℝ)/2+1) * r^n` |
| 6 | `ring` | ✓ |

Net: ~40 LOC including the `have h_sqrt_pow` helper (5 LOC) and the
`h_quot_nn` nonnegativity certificate (4 LOC). With doc-comments and
namespace setup: ~50 LOC.

### §3.4 — The `(√π)^n = π^((n : ℝ)/2)` bridge in isolation

This is the only non-trivial arithmetic identity. The crucial type
coercion is between `Monoid.npow ℝ` (the `^ : ℝ → ℕ → ℝ` on the LHS,
viz. `(√π)^n` with `n : ℕ`) and `Real.rpow` (the `^ : ℝ → ℝ → ℝ` on
the RHS, viz. `π^((n:ℝ)/2)`). The bridge:

```lean
have h_sqrt_pow {n : ℕ} : Real.sqrt π ^ n = π ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast (π ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul Real.pi_pos.le]
  congr 1; ring
```

Verifying each rewrite:

1. `Real.sqrt_eq_rpow : Real.sqrt π = π ^ ((1 : ℝ) / 2)`. Defined at
   `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (the exact file
   may have moved; the lemma is stable). Strictly:
   ```
   theorem Real.sqrt_eq_rpow (x : ℝ) : √x = x ^ ((1 : ℝ) / 2)
   ```
   (handles negative `x` correctly via `Real.rpow` being 0 there.)
2. `Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ (n : ℝ) = x ^ n` (the
   ℕ-power is the same as the ℝ-rpow with ℕ-cast exponent).
3. `Real.rpow_mul : 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z`
   (multiplicativity of rpow in the exponent, needs `0 ≤ x`).
4. `congr 1` reduces the goal to the exponent equality
   `(1 : ℝ) / 2 * (n : ℝ) = (n : ℝ) / 2`.
5. `ring` closes it.

**Sanity check at $n = 2$**: `(√π)^2 = π = π^1 = π^((2 : ℝ)/2)` ✓.
**At $n = 3$**: `(√π)^3 = π · √π = π^(3/2) = π^((3 : ℝ)/2)` ✓.

### §3.5 — Risk-bearing rewrites in the chain

| Risk | Symptom (at S3 ACT Docker build) | Diagnostic | Mitigation |
|------|----------------------------------|------------|------------|
| **R1** `ENNReal.toReal_pow` might unify `n : ℕ` on the LHS but reject the rewrite shape | `motive is not type correct` or `did not find an occurrence` | The `(.ofReal r)^n` form should be syntactically present after `volume_closedBall`. | Use `show … from by …` lift or explicit `(ENNReal.ofReal r ^ Module.finrank ℝ E).toReal` ascription. |
| **R2** `ENNReal.toReal_ofReal hr` requires `0 ≤ r` but `hr : 0 ≤ r` from the hypothesis | None expected; routine | hr is exactly what's needed | None. |
| **R3** `h_quot_nn` cert for `0 ≤ √π^n / Γ((n:ℝ)/2 + 1)` — `Gamma_pos_of_pos` needs `0 < (n:ℝ)/2 + 1` | If `n = 0` (excluded by Nontrivial), the cert fails. For `n ≥ 1`, `(n:ℝ)/2 + 1 ≥ 1.5 > 0`. | `positivity` should handle it after `n_pos := Module.finrank_pos` and `(n:ℝ) ≥ 1`. | Fall back to explicit `linarith` after extracting `n_pos`. |
| **R4** `Real.rpow_natCast` direction: Mathlib has `x ^ (n : ℝ) = x ^ n` (LHS rpow, RHS npow). The `← Real.rpow_natCast` rewrite goes RHS-to-LHS, **inserting** an rpow. | If direction is wrong, `rw [← Real.rpow_natCast]` will fail. | Check both `Real.rpow_natCast` and `Real.rpow_nat_cast` (deprecated alias) and `pow_natCast` if name shifted. | Try `rw [Real.rpow_natCast]` (forward) instead, with the chain re-ordered. |
| **R5** **`Nontrivial E` derivation** — if S3 ACT wants to drop `[Nontrivial E]` as a hypothesis, it needs to case-split on `finrank ℝ E = 0` vs `≥ 1` | If split, the `finrank = 0` branch has `E ≃ {0}` and both sides of Bridge 1 are 0. | n/a — keeping `[Nontrivial E]` is the right call. | Document `[Nontrivial E]` requirement in Bridge 1's docstring. |
| **R6** **Measure-compatibility implicit assumption** — `InnerProductSpace.volume_closedBall` is stated under `[MeasureSpace E] [BorelSpace E]` but its proof uses `(stdOrthonormalBasis ℝ E).measurePreserving_repr_symm` which presumes `volume : Measure E` agrees with the standard AddHaar from the orthonormal-basis isomorphism. | If `volume` on user-supplied E doesn't match, the lemma type-checks but gives the wrong answer. | This is **the implicit Mathlib convention** for finite-dim inner-product spaces — `[MeasureSpace E] [BorelSpace E]` + `[InnerProductSpace ℝ E]` implies the canonical Haar measure. | At S3 ACT, **add a docstring note** clarifying that Bridge 1 assumes the canonical `MeasureSpace E` instance. For concrete `EuclideanSpace ℝ (Fin n)`, this is automatic via Mathlib's `EuclideanSpace.measureSpace` synthesis. |

R6 is the most subtle. The polymorphic lemma type-checks for any
`[MeasureSpace E]` but its mathematical content depends on `volume`
being the canonical Haar measure. In practice, Mathlib's
`EuclideanSpace`/`PiLp` library provides this automatically; downstream
clients of our Bridge 1 would either work over `EuclideanSpace ℝ (Fin n)`
(canonical measure provided) or supply their own canonical
`MeasureSpace E` instance.

## §4 — The `Nontrivial E` typeclass analysis

### §4.1 — Why `[Nontrivial E]` is needed

The `InnerProductSpace.volume_ball` proof's first step is:

```lean
have : Nonempty (Fin (finrank ℝ E)) := Fin.pos_iff_nonempty.mp finrank_pos
```

`Fin.pos_iff_nonempty` requires `finrank_pos`, which in turn requires
`Nontrivial E`. Without `[Nontrivial E]`, `finrank ℝ E` could be 0 and
`Fin 0` is empty, making the orthonormal-basis representation `repr_symm`
ill-defined.

### §4.2 — Mathlib's `Nontrivial ↔ finrank > 0` bridge

```
Module.nontrivial_of_finrank_pos : 0 < finrank ℝ E → Nontrivial E  (forward)
finrank_pos : [Nontrivial E] → 0 < finrank ℝ E                    (reverse)
```

Both at `Mathlib/LinearAlgebra/Dimension/Finrank.lean` (stable across
recent Mathlib versions).

### §4.3 — Implications for Bridge 1's hypothesis design

Two viable shapes:

**Shape A** (recommended): keep `[Nontrivial E]` as a typeclass hypothesis.

```lean
theorem riemannianVolumeBall_eq_nBallVolumeFn
    [Nontrivial E] (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      nBallVolumeFn (Module.finrank ℝ E) r
```

— Clean, matches Mathlib's convention.

**Shape B**: case-split on `finrank ℝ E = 0`.

```lean
theorem riemannianVolumeBall_eq_nBallVolumeFn'
    (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      nBallVolumeFn (Module.finrank ℝ E) r := by
  by_cases h_dim : 0 < Module.finrank ℝ E
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos h_dim
    -- … invoke Shape A
  · push_neg at h_dim
    interval_cases (Module.finrank ℝ E)
    -- finrank = 0: E ≃ {0}, both sides are 0
    sorry  -- ~5 LOC trivial case
```

— Slightly more general but adds ~10 LOC for the trivial branch. Not
worth it; **Shape A is the recommended S3 ACT target.**

### §4.4 — Downstream `[Nontrivial E]` propagation

Any downstream theorem stacked on Bridge 1 (S4 Bridge 2, S5 main)
inherits `[Nontrivial E]`. The OQ-03 main statement reads:

```lean
theorem riemannianVolumeBall_hasDerivAt_riemannianSurfaceArea
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]
    (p : E) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun s : ℝ => (volume (Metric.closedBall p s)).toReal)
      (riemannianSurfaceArea p r)
      r
```

— `[Nontrivial E]` is the natural typing. The S5 main theorem at
`finrank = 0` is vacuous (both LHS and RHS are 0; derivative of 0 is 0;
hr : 0 < r excludes the degenerate $r = 0$ case but doesn't help with
$\operatorname{finrank} = 0$). Keeping `[Nontrivial E]` is the
**honest scope** for OQ-03's deliverable.

## §5 — S3 ACT scope estimate

| Component | LOC | Build risk |
|-----------|-----|------------|
| Imports + namespace + variable block | ~10 | low — additive to existing OQ03 file |
| `riemannianVolumeBall_eq_nBallVolumeFn` proof body (Steps 1-5) | ~25 | medium — `ENNReal.toReal_pow` direction risk (R1) |
| `h_sqrt_pow` helper (`(√π)^n = π^((n:ℝ)/2)` bridge) | ~5 | low — straightforward rpow arithmetic |
| `h_quot_nn` nonneg certificate | ~4 | low — `positivity` handles it |
| Docstring + comment header | ~6 | n/a |
| **Total** | **~50** | low-medium |

Plus existing `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`
already lands 93 LOC for the n=2,3 concrete partial (in #18985); the S3
ACT adds **+50 LOC** to make the file ~143 LOC total — still within the
state.md's S2 estimate ($\sim 150-200$ for combined S2+S3 deliverable).

## §6 — Path-to-verification update

With Workaround A unblocked, the R1 vector-space route revises to:

| Stage | Deliverable | LOC | Status (post-S2 ACT) | Status (post-S3 ACT, proposed) |
|-------|-------------|-----|----------------------|--------------------------------|
| S1 | OBSERVE survey | — | merged (#18362) | unchanged |
| S2 PREP×4 | Mathlib bearer audits | — | merged (#18458/#18575/#18615/#18691) | unchanged |
| S2 ACT | $n \in \{2, 3\}$ concrete (4 thms) | 93 | open (#18985) | merged (when #18985 merges) |
| **S3 PREP** (this) | **Workaround A re-audit + Bridge 1 skeleton** | — | this PR | merged |
| **S3 ACT** (proposed next) | **Abstract polymorphic Bridge 1** (~50 LOC) | ~50 | not started | merged |
| S4 ACT | Bridge 2: `hausdorffMeasure_sphere_eq_nSphereSurfaceFn` | ~200 | (separately blocked on Hausdorff-sphere identification, see §6.1) | tbd |
| S5 ACT | Main `_hasDerivAt_` polymorphic | ~100 | (depends on S3+S4) | tbd |
| Gallery wiring | `meta.json` + `index.ts` | ~80 | (depends on S2 ACT merge) | tbd |
| R2 manifold | Riemannian roadmap | ~3000+ | blocked on 4 Mathlib gaps | unchanged |

### §6.1 — Bridge 2 (S4) status — still genuinely blocked

Bridge 2 needs the identification

$$
\mathcal{H}^{n-1}(S(p, r) \cap E) = n \omega_n r^{n-1} = S_{n-1}(r)
$$

i.e., $(n-1)$-Hausdorff measure of the $r$-sphere equals the parent's
`nSphereSurfaceFn`. Mathlib v4.26.0 has `Measure.hausdorffMeasure` but
**no named identification with the surface area of a sphere** in any
inner-product space. The identification requires either:

(a) The **co-area formula in $\mathbb{R}^n$** applied to $f = \|\cdot
\|$ — gated by a Mathlib coarea gap.
(b) An explicit **spherical-coordinates computation** ($r^{n-1} \cdot d
\mathcal{H}^{n-1}(\Omega)$ on the unit sphere) — would need the
spherical-coordinates parameterization in Mathlib, which exists in
limited form (`MeasureTheory.Constructions.HaarToSphere`) but isn't in
a directly-usable shape for $\mathcal{H}^{n-1}$.

The S2 ACT's Workaround C avoidance of Bridge 2 (by replacing the
abstract surface measure with the explicit `nSphereSurfaceFn` from the
parent) is **still the right call** for the $n \in \{2, 3\}$ partial.
For the polymorphic version, S4 ACT will need either:

- **Workaround A'** (axiomatize Bridge 2): introduce
  `axiom hausdorffMeasure_sphere_eq_nSphereSurfaceFn`. Single axiom,
  well-documented, status downgrades to `axiomatized`.
- **Workaround C'** (skip Bridge 2 entirely): state S5 main directly
  with `nSphereSurfaceFn` on the RHS (no surface-measure abstraction).
  Result: verified, but the OQ-03 statement is the parent's identity
  re-stated in `InnerProductSpace` typeclass form rather than truly
  "via surface measure".

This S3 PREP recommends Workaround C' for S4/S5 if the S3 ACT polymorphic
Bridge 1 lands — it preserves `axiomCount: 0` and makes the polymorphic
identity a clean statement.

## §7 — Honesty / calibration

This is **a doc-only audit** correcting an over-claim in PR #18985's
state.md "Workaround A blocked" framing. The actual situation:

- The `finrank`-polymorphic `InnerProductSpace.volume_closedBall`
  lemma exists at v4.26.0 (line 372 of `VolumeOfBalls.lean`).
- Workaround A (polymorphic Bridge 1) is unblocked, with an estimated
  ~40-50 LOC tactic chain (§3.2 above).
- The "blocked" framing in #18985 was a soft-overstatement reflecting
  S2 ACT's deliberate scope-narrowing to Workaround C (n = 2, 3 only),
  not a literal Mathlib API gap.

The corrected S3 PREP is honest about both directions:

1. The S2 ACT (#18985) ships a **clean** $n \in \{2, 3\}$ partial — the
   $n$-specific lemmas (`EuclideanSpace.volume_closedBall_fin_two/three`)
   are explicitly verified, the chain compiles in 93 LOC, and the
   deliverable is a meaningful partial answer to OQ-03 by itself.
2. **However**, the polymorphic version is achievable in S3 ACT with
   another ~50 LOC, contradicting the "blocked" claim.

The mathematical content of OQ-03 in the R1 vector-space case is
classical (Federer 1959, do Carmo 1992) and the polymorphic version
delivers the **intrinsic** R1 statement promised in S1 OBSERVE — not
just the $n \in \{2, 3\}$ specialization. **S3 ACT is the genuine R1
finish line; #18985 ships the dim-restricted partial.**

This PR does not modify the Lean code. The S3 ACT (~50 LOC actual Lean
contribution) is a separate session's deliverable, to be picked up
when:

- #18985 merges (so the OQ03 file exists in main with the n=2,3 thms).
- The Bridge 2/S4 scope is re-classified (Workaround A' axiomatize vs
  C' skip — §6.1 above).

## §8 — No-Edit Guarantee (this S3 PREP)

This S3 PREP iteration modifies ONLY:

- `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-14-s3-prep-workaround-a-bridge1-mathlib-availability-erratum.md` (this file, new).
- `research/problems/circumference-via-differentiation-oq-03/state.md` (append S3 PREP iteration row; update Next Action to point at S3 ACT).
- `src/data/research/problems/circumference-via-differentiation-oq-03.json` (append S3 PREP insight; bump `lastUpdate`).

No `proofs/`, no `src/data/proofs/`, no `proofs/Proofs.lean`, no
parent-proof file is touched. **No Lean compilation is required for
this PR.**

## §9 — Race-disclosure with open PR #18985

Per memory's `feedback_researcher_mid_session_pr_race_disclosure`:

- **Pre-claim** (16:00 UTC 2026-05-14): `gh pr list --search
  "circumference-via-differentiation-oq-03 in:title" --state open`
  returned `[#18985]`. **PR #18985 is the open S2 ACT predecessor.**
- This S3 PREP **does not overlap** #18985's scope: #18985 ships the
  Lean code (Bridge 1 concrete n=2,3), this S3 PREP is doc-only about
  the polymorphic Bridge 1 / S3 ACT.
- File-level overlap risk: both PRs modify `state.md` and
  `src/data/research/problems/…json`. **My state.md changes are
  additive** (new Iteration History row; new Next Action section); a
  merge conflict on those files would be a 3-way append, easy to resolve.

If the deployer merges #18985 first (likely — older PR, no conflicts
flagged), my PR rebases trivially. If my PR merges first (unlikely),
#18985 rebases trivially. Either order works.

## §10 — References

- PR #18362 (S1 OBSERVE, merged 2026-05-12T23:17Z) — Riemannian dV/dr = A survey.
- PR #18458 (S2 PREP, merged 2026-05-13T03:09Z) — Mathlib bridge audit; **§2 correctly identified `InnerProductSpace.volume_closedBall`**.
- PR #18575 (S2b PREP, merged 2026-05-13T05:06Z) — LOC tightening + Workaround-C dim lemmas.
- PR #18615 (S2c PREP, merged 2026-05-13T07:02Z) — toReal-chain correction + `HasDerivWithinAt(Set.Ici 0)` refinement.
- PR #18691 (S2d PREP, merged 2026-05-13T09:23Z) — `.symm` direction-reversal erratum; drop-in skeleton.
- PR #18985 (S2 ACT, **open** as of 2026-05-14T16:00 UTC) — R1 Euclidean n=2,3 partial; **state.md "Workaround A blocked" framing corrected by this S3 PREP**.
- Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:372` — `InnerProductSpace.volume_closedBall`.
- Mathlib `2df2f0150…`, `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:514` — `addHaar_closedBall_eq_addHaar_ball`.
- `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean:39, 83` — parent `unitBallVolume`, `nBallVolumeFn` definitions.

---

**End of S3 PREP doc.**
