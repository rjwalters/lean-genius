# Session — Iter 5a-β-2 PREP: paste-ready scaffold for weak Mertens M1 via Abel summation

**Date**: 2026-06-02
**Researcher**: researcher-1
**Mode**: PREP (doc-only, no Lean changes this PR)
**Slug**: chebyshev-bounds-oq-04-oq-01
**Base SHA**: 346ab85a658 (origin/main)
**Mathlib pin**: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 (unchanged 17 days since S6 PREP 2026-05-16)

## §1. Mode and trigger

Iter 5a-β-1 ACT shipped at 2026-06-01 as PR #21865 (Mertens partial sum
`mertensM : ℕ → ℝ` + trivial bound `|mertensM N| ≤ N`, +49 LOC,
Docker-verified 7744 jobs in 23s). Follow-up meta fix #21896 corrected
the `lineCount` drift (325 → 374). No further activity on this slug
since (T-22h at session start).

This PREP does **not ship Lean code**. It does:

1. Audit the Mathlib bearer `sum_mul_eq_sub_integral_mul₀'` at
   `Mathlib/NumberTheory/AbelSummation.lean:229` for the partial
   summation step (verified byte-stable at pin `2df2f0150c…`).
2. Resolve the open question from S6 PREP "if no discrete partial-summation
   lemma exists in Mathlib, build a short Abel rearrangement locally" —
   `sum_Ioc_by_parts` *does* exist (`Mathlib/Algebra/BigOperators/Module.lean:47`),
   and `sum_mul_eq_sub_integral_mul₀'` is the right specialisation
   because the c₀ = 0 form is exactly built for `ArithmeticFunction` use cases.
3. Write a paste-ready proof scaffold for Iter 5a-β-2's `mertens_M1_bound`
   targeting `|Σ_{d ∈ Icc 1 N} (μ d : ℝ)/d| ≤ 1 + Real.log N`, with
   bearer manifest, instantiation choices, and the technical traps
   anticipated from the Mathlib statement.
4. Confirm Mathlib v4.26.0 has **no formalised Mertens M1**
   (`Σ μ(d)/d = O(1)` or any weak form) — empirically verified by
   exhaustive Mathlib tree search for "mertens" (0 hits) and code
   search for "moebius/d" patterns in arithmetic-function files.

## §2. Mathematics

The weak Mertens M1 bound is

```
|Σ_{d=1}^{N} μ(d)/d| ≤ 1 + log N,    N ≥ 1.
```

It follows from Abel summation. With `c d := (μ d : ℝ)` (so `c 0 = 0`
since `μ 0 = 0` by `ArithmeticFunction.map_zero`) and `f t := 1/t`
(differentiable on `[1, ∞)`, `deriv f t = -1/t²`):

```
Σ_{d=0}^{N} f(d)·c(d) = f(N)·(Σ_{d=0}^{N} c(d)) − ∫_1^N (deriv f)(t)·(Σ_{d=0}^{⌊t⌋} c(d)) dt
```

Note: at `d = 0`, `f(0) = 1/0` is undefined; the `c₀ = 0` variant
papers over this because `f(0)·c(0)` never appears (the lemma only
needs `f` differentiable on `[1, m]` and `c 0 = 0`).

Rewriting with `mertensM' (n : ℕ) := Σ_{d ∈ Icc 0 n} (μ d : ℝ)`:

```
Σ_{d ∈ Icc 0 N} (μ d : ℝ)/d = (mertensM' N)/N − ∫_1^N (−1/t²)·mertensM' ⌊t⌋ dt
                            = (mertensM' N)/N + ∫_1^N (mertensM' ⌊t⌋)/t² dt.
```

Since `μ 0 = 0`, the LHS equals `Σ_{d ∈ Icc 1 N} (μ d : ℝ)/d`
(the index `d = 0` contributes 0 because of the `μ 0` factor — but the
*ambient* `1/d` term `1/0` is conventionally undefined; safest to
define `f t := if t = 0 then 0 else 1/t` or use `Finset.sum_Icc_eq_sum_range` 
to shift the index and avoid the issue cleanly). For the bound we
take absolute values and use `mertensM_abs_le`:

```
|Σ_{d ∈ Icc 1 N} (μ d : ℝ)/d|
  ≤ |mertensM' N|/N + ∫_1^N |mertensM' ⌊t⌋|/t² dt
  ≤ N/N + ∫_1^N ⌊t⌋/t² dt
  ≤ 1 + ∫_1^N 1/t dt
  = 1 + log N.
```

The last `∫_1^N 1/t dt = log N` uses Mathlib
`integral_one_div_eq_log` / `intervalIntegral.integral_inv` style
bearers; the `⌊t⌋/t² ≤ 1/t` step uses `Nat.floor_le` + monotonicity of
division.

## §3. Bearer manifest at pin `2df2f0150c…`

| Lemma | File | Line | Status |
|---|---|---:|---|
| `sum_mul_eq_sub_integral_mul₀'` | `Mathlib/NumberTheory/AbelSummation.lean` | 229 | byte-stable @ pin ✅ |
| `sum_Ioc_by_parts` (discrete Abel) | `Mathlib/Algebra/BigOperators/Module.lean` | 47 | byte-stable @ pin ✅ (alt bearer) |
| `ArithmeticFunction.map_zero` | `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean` | — | byte-stable @ pin ✅ |
| `ArithmeticFunction.abs_moebius_le_one` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean` | 104 | byte-stable @ pin ✅ |
| `intervalIntegral.integral_one_div` (or `integral_inv`) | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` | TBD @ first build | candidate |
| `Real.log_le_log` / `Real.log_one_le_iff` for log-monotonicity | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | TBD | candidate |
| `Nat.floor_le` (⌊t⌋ ≤ t for t ≥ 0) | `Mathlib/Algebra/Order/Floor/Defs.lean` | — | byte-stable @ pin ✅ |

The exact `sum_mul_eq_sub_integral_mul₀'` statement (at line 229,
verified via `curl … | head` of the pinned blob):

```
theorem sum_mul_eq_sub_integral_mul₀' (hc : c 0 = 0) (m : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) m)) :
    ∑ k ∈ Icc 0 m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) -
        ∫ t in Set.Ioc (1 : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k
```

`hc : c 0 = 0` is satisfied by `(ArithmeticFunction.moebius 0 : ℝ) = 0`
which follows from `ArithmeticFunction.map_zero` + `Int.cast_zero`.

## §4. Paste-ready proof scaffold

```lean
/-! ## Weak Mertens M1 bound (Iter 5a-β-2)

    |Σ_{d ∈ Icc 1 N} (μ(d) : ℝ) / d| ≤ 1 + Real.log N    (N ≥ 1).

This is the M1 form of Mertens' theorem — far from the sharp
`Σ μ(d)/d → 0` (equivalent to PNT) but exactly what summation by parts
delivers via the trivial `|M(N)| ≤ N` bound from Iter 5a-β-1. -/

/-- The Mertens partial sum over `Icc 0 N`, an alias for `mertensM`
    suitable for Abel-summation indexing. -/
noncomputable def mertensM' (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 0 N, (ArithmeticFunction.moebius d : ℝ)

theorem mertensM'_eq_mertensM (N : ℕ) : mertensM' N = mertensM N := by
  unfold mertensM' mertensM
  -- μ 0 = 0 so dropping d = 0 doesn't change the sum
  rw [show (Finset.Icc 0 N) = insert 0 (Finset.Icc 1 N) from ?_]
  · rw [Finset.sum_insert (by simp [Finset.mem_Icc]; omega)]
    simp [ArithmeticFunction.map_zero]
  · ext k
    simp [Finset.mem_Icc, Finset.mem_insert]
    omega

theorem mertensM'_abs_le (N : ℕ) : |mertensM' N| ≤ (N : ℝ) := by
  rw [mertensM'_eq_mertensM]; exact mertensM_abs_le N

/-- Auxiliary: `f(t) := 1/t` is differentiable on `[1, ∞)` with
    derivative `−1/t²`. -/
private lemma inv_differentiableAt_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ => s⁻¹) t :=
  (differentiableAt_id.inv (by linarith : t ≠ 0))

/-- **Weak Mertens M1** for the Möbius function:
    `|Σ_{d ∈ Icc 1 N} (μ d : ℝ)/d| ≤ 1 + log N` for `N ≥ 1`. -/
theorem mertens_M1_bound (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ) / d)|
      ≤ 1 + Real.log N := by
  -- Step 1: re-index Icc 1 N as Icc 0 N (μ 0 = 0 contributes 0; (μ 0)/0 = 0/0 = 0 in ℝ).
  -- Step 2: apply sum_mul_eq_sub_integral_mul₀' with
  --   c d := (ArithmeticFunction.moebius d : ℝ),
  --   f t := if t = 0 then 0 else t⁻¹,
  --   hc  : c 0 = 0 from ArithmeticFunction.map_zero,
  --   hf_diff : on Icc 1 N, t ≠ 0 so f reduces to t⁻¹, differentiable,
  --   hf_int  : deriv f = -t⁻² on (0, ∞), continuous on [1, N], integrable.
  -- Step 3: triangle inequality on the identity from Step 2.
  -- Step 4: bound the boundary term: |f(N) · mertensM' N| ≤ (1/N) · N = 1 via mertensM'_abs_le.
  -- Step 5: bound the integral term: |∫ ... | ≤ ∫ |...| ≤ ∫_1^N (1/t²) · t dt = ∫_1^N 1/t dt = log N.
  sorry

```

## §5. Honest scope and acceptance

| Metric | Pre (post-Iter 5a-β-1) | Post (Iter 5a-β-2 ACT projected) | Δ |
|---|---:|---:|---:|
| `ChebyshevBoundsOQ04OQ01.lean` LOC | 374 | 460–500 | +85±15 |
| theorems | 18 | 21–22 | +3–4 |
| noncomputable defs | 4 | 5 | +1 |
| sorries | 0 | 0 (target) | 0 |
| `axiom` declarations | 0 | 0 (target) | 0 |

**This PREP**: 0 Lean changes. Updates only state.md head, JSON
focus/nextAction/insights/nextSteps/lastUpdate, and this session memo.

**Iter 5a-β-2 ACT estimate** (next claimable iteration, after this
PREP merges): 60–90 LOC of proof code, 3–5 Docker iters (the integral
bound `∫_1^N (mertensM' ⌊t⌋)/t² dt ≤ log N` is the technical heart;
expect Mathlib API friction around `intervalIntegral`'s `Set.Ioc`
vs `Set.Icc` measure conventions and the `Real.log_eq_integral` /
`integral_one_div_eq_log` lemma name).

## §6. Technical traps anticipated

### Trap 1 — `f(0) = 1/0` undefined

`sum_mul_eq_sub_integral_mul₀'` only requires `f` differentiable on
`Set.Icc (1 : ℝ) m`. So we can define `f t := t⁻¹` everywhere
(Lean/Mathlib's convention `(0 : ℝ)⁻¹ = 0` keeps the definition total)
and the lemma's hypotheses don't depend on `f`'s value at `t = 0`.
The `c 0 = 0` condition then ensures the boundary contribution from
`d = 0` vanishes algebraically:

```
f(0) · c(0) = (0 : ℝ)⁻¹ · 0 = 0 · 0 = 0
```

so the identity `Σ_{Icc 0 m} f·c = f(m)·(Σ_{Icc 0 m} c) − ∫…` works
even though `(0 : ℝ)⁻¹ = 0` is not "1/0" in the mathematical sense.
**Use Mathlib's `t⁻¹` convention directly; do not introduce an
`if t = 0` branch — it complicates the differentiability proof.**

### Trap 2 — `deriv` of `t⁻¹`

`deriv (fun t : ℝ => t⁻¹) t = −t⁻²` requires `t ≠ 0`. Mathlib bearer:
`HasDerivAt.inv` (in `Mathlib/Analysis/Calculus/Deriv/Inv.lean`) gives
`HasDerivAt (·⁻¹) (−x⁻¹^2) x` for `x ≠ 0`. Need to lift to `deriv`
via `HasDerivAt.deriv`. Estimate ~3–5 LOC for the differentiability
hypothesis bundle.

### Trap 3 — `IntegrableOn (-t⁻²) (Set.Icc 1 N)`

`t⁻²` is continuous on `[1, N]` (no zeros in the interval), so by
`ContinuousOn.integrableOn_Icc` it is integrable. Same for `−t⁻²`.
Estimate ~2–3 LOC.

### Trap 4 — Bounding the integral `|∫_1^N (mertensM' ⌊t⌋)/t² dt|`

The integrand `mertensM' ⌊t⌋` is a *step function*. The bound
`|mertensM' ⌊t⌋| ≤ ⌊t⌋ ≤ t` (with `t ≥ 1 ≥ 0`) gives

```
|∫_1^N (mertensM' ⌊t⌋)/t² dt| ≤ ∫_1^N |mertensM' ⌊t⌋|/t² dt
                              ≤ ∫_1^N t/t² dt
                              = ∫_1^N 1/t dt
                              = log N.
```

The first step uses `MeasureTheory.abs_integral_le_integral_abs` (or
`norm_integral_le_integral_norm`). The pointwise bound uses
`mertensM'_abs_le ⌊t⌋` then `Nat.cast_floor_le : (⌊t⌋ : ℝ) ≤ t`
(verify exact name at first Docker iteration; candidates
`Nat.floor_le` and `Int.floor_le`). The final `log N` evaluation uses
the Mathlib lemma `integral_one_div_eq_log` or
`intervalIntegral.integral_inv` on `[1, N]`. Estimate ~25–35 LOC.

### Trap 5 — `Set.Ioc` vs `Set.Icc` in `intervalIntegral`

`sum_mul_eq_sub_integral_mul₀'` uses `∫ t in Set.Ioc (1 : ℝ) m` (open
on the left). For Lebesgue integrals on intervals with measure-zero
endpoints, `Ioc` and `Icc` agree, but the syntactic conversion may
need `MeasureTheory.integral_Ioc_eq_integral_Icc` or
`set_integral_Ioc_eq_set_integral_Icc` (verify name at first Docker
iteration). Estimate ~2 LOC bridge.

### Trap 6 — Identifying `Σ_{Icc 0 m} ((μ d : ℝ) / d)` with the
`sum_mul_eq_sub_integral_mul₀'` LHS `Σ_{Icc 0 m} f(d) * c(d)`

The Mathlib statement writes `f k * c k`, multiplication in that
order. Our integrand `(μ d : ℝ) / d = (μ d : ℝ) * (1/d) = c(d) * f(d)`
needs `mul_comm` (or use `f k := k⁻¹` and rewrite `c k * f k = c k / k`).
Estimate ~2 LOC, single `simp_rw [mul_comm]` or `div_eq_mul_inv`.

## §7. Next-iteration roadmap

Unchanged from S6 PREP except:

1. **Iter 5a-β-2 ACT** (60–90 LOC, picker-ready after this PREP merges):
   build the `mertens_M1_bound` per the scaffold above. Bearer-stability
   spot-check confirmed at pin `2df2f0150c…`. Expected Docker iters: 3–5
   (the integral bound is the technical heart).
2. **Iter 5a-α** (60–90 LOC, **independent of 5a-β**, claimable in
   parallel): prove the `(log m)²` partial-sum asymptotic via Abel
   summation against `f(t) = (log t)²` (same bearer
   `sum_mul_eq_sub_integral_mul₀'` at AbelSummation.lean:229).
3. **Iter 5a-γ** (40–60 LOC, requires 5a-α + 5a-β merged): assemble
   Selberg's symmetry formula
   `|selbergSum2 N − 2N·log N| ≤ C·N`.
4. **Iter 5b** (optional): O(N) error-term sharpening.
5. **Iter 6+**: Tauberian inequality + Erdős combinatorial finishing.

## §8. Race awareness

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open`
at session start returned **0 OPEN PRs**:

- Iter 5a-β-1 ACT PR #21865 MERGED 2026-06-01T**
- Meta linecount fix #21896 MERGED 2026-06-01T11:15:57Z
- All older Iter 1-4 and S6/S7 PRs MERGED

Pre-push re-check (per memory `feedback_mechanic_recheck_pr_before_create`):
will re-run `gh pr list` immediately before `git push`.

## §9. Files touched (this PR)

- `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` — head-prepend
  new Iter 5a-β-2 PREP entry; historical tail preserved verbatim.
- `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-06-02-iter5a-beta-2-prep-partial-summation-mertens-M1.md`
  — this memo.
- `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json` —
  phase/since/iteration/focus/nextAction + knowledge.{progressSummary,
  insights += 1, nextSteps += 1} + lastUpdate. No `leanFiles` metadata
  changes (no Lean source touched).

**Not touched**:

- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` — frozen at Iter 5a-β-1
  post-merge state (374 LOC, 18 thm, 4 defs, 0 sorries, 0 axioms).
- Parent file `proofs/Proofs/ChebyshevBoundsOQ04.lean` — unchanged.
- Gallery `src/data/proofs/chebyshev-bounds-oq-04-oq-01/meta.json` —
  unchanged at Iter 5a-β-1 post-merge state (lineCount 374,
  theoremCount 18).

## §10. Mathlib gap re-affirmed

Empirical confirmation that Mathlib v4.26.0 at pin `2df2f0150c…` has:

- **0** files matching "mertens" (case-insensitive) in `Mathlib/`
  (verified via GitHub Tree API recursive listing).
- **0** lemmas in `ArithmeticFunction/Moebius.lean` of the form
  `Σ μ(d)/d ≤ …` or asymptotic / big-O statements about partial sums
  of `μ` or `μ/d` (manual `grep` of the 220-line file).
- The **only** `μ`-related bound in Mathlib at the partial-sum level
  is `abs_moebius_le_one` (pointwise, line 104).

This confirms the S6 PREP claim — Mertens M1 must be built locally.
Iter 5a-β-1 lands the foundational `|M(N)| ≤ N`; Iter 5a-β-2 (this
PREP's target) assembles it with Abel summation into the M1 bound.
After this iteration ships, the slug will have the **first formalised
weak Mertens M1 estimate in Lean 4**, a side-deliverable of independent
gallery interest.
