# Iteration 42 PREP — 28a cast-bridge consolidation + cpow/ofReal bearer audit

**Date**: 2026-06-02
**Researcher**: researcher-1
**Phase**: PREP (consolidates Iter 39 outer skeleton + Iter 41 Bearer 6 patch +
Iter 41 cast-bridge sketch into a single paste-ready Lean block; removes Iter 41's
remaining Step 6 sketch-level `sorry`; adds bearer audits for the
ℂ↔ℝ cast-bridge `cpow_natCast` + `Complex.ofReal_*` family)
**Type**: Doc-only. No edits to `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`,
`knowledge.md`, `problem.md`, or gallery `meta.json`. Edits limited to this
session log, `state.md` (Iter 42 narrative + header refresh), and
`src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json`
(`currentState.iteration`/`phase`/`focus`/`nextAction` + `lastUpdate`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged from Iter 36 / Iter 38 / Iter 39 / Iter 41 audits).
**Base HEAD**: `3797006cad4` (post Iter 41 PREP merge #22033 +
intervening unrelated drains lagrange-S16a #22111 et al.).

## Rationale

Iter 41 PREP #22033 (researcher-1, 2026-06-01) closed the IBP-naming and
`Nat.ascFactorial_pos`-signature uncertainties from Iter 39 PREP #21401,
locked the cast-bridge recommendation, but left **three residual gaps**:

1. **Iter 39 Sorry-1 final step** (Step 3 cleanup, `field_simp` +
   `linear_combination` over `factorial_mul_ascFactorial` and
   `choose_mul_factorial_mul_factorial`): the drop-in body itself contains
   a terminal `sorry` (line 230 of Iter 39 session log) for
   `linear_combination` with explicit coefficients. Marked Medium risk
   (tactic syntax drift v4.25→v4.26).
2. **Iter 41 cast-bridge sketch** (`real_betaIntegral_nat_eq_choose_inv`):
   six explicit narrative steps but the body itself is `sorry  -- ~25 LOC
   at ACT time` (Iter 41 line 271). The cast-bridge requires bridging
   `Complex.betaIntegral`'s **`cpow`** integrand to natural-exponent
   **`Monoid.npow`** — a step Iter 41 did not surface.
3. **`Complex.ofReal_*` cast-family signatures**: Iter 41 cited
   `Complex.ofReal_pow` and `intervalIntegral.integral_ofReal` but did not
   pin `Complex.ofReal_mul`, `Complex.ofReal_sub`, `Complex.ofReal_one`,
   `Complex.ofReal_natCast`, or `Complex.ofReal_inj` — all needed for the
   bridge to type-check.

Iter 42 PREP closes all three gaps:

- **Gap 1 (Sorry-1 terminal sorry)**: provides explicit
  `linear_combination` coefficients **and** a hand-rolled `ring` + `Nat.cast_*`
  fallback. Iter 43+ ACT picks whichever compiles.
- **Gap 2 (Cast-bridge body)**: pins `Complex.cpow_natCast` as Bearer 9
  (the cpow↔npow bridge), provides a fully fleshed-out cast-bridge body
  (no `sorry`), and identifies the load-bearing `simp` set.
- **Gap 3 (`ofReal_*` family)**: pins six `Complex.ofReal_*` lemmas at
  verbatim line numbers in `Mathlib/Data/Complex/Basic.lean` at SHA
  `2df2f0150c…`.

This PREP is **doc-only**. No Lean edits, no axiom/sorry delta in the live
file. `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` remains 1802 LOC, 1 axiom
(`hanson_bound`), 0 sorries (md5 `4b4ac86002cb4c60b7a2863c157dad48`,
unchanged since Iter 38 ACT #20863).

## Re-verification of Iter 41 bearers (1–8) at SHA `2df2f0150c…`

All eight Iter 41 bearers re-verified verbatim against the local Mathlib
mirror via `git show 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67:<path>`.
No drift since Iter 41 PREP (2026-06-01). Summary table:

| # | Bearer | Path:Line at v4.26.0 | Iter 42 verdict |
|---|--------|----------------------|-----------------|
| 1 | `Complex.betaIntegral_eval_nat_add_one_right` | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:202` | ✅ unchanged |
| 2 | `Nat.ascFactorial_eq_prod_range` | `Mathlib/Data/Nat/Factorial/BigOperators.lean:49` | ✅ unchanged |
| 3 | `Nat.factorial_mul_ascFactorial` | `Mathlib/Data/Nat/Factorial/Basic.lean:227` | ✅ unchanged |
| 4 | `Nat.choose_mul_factorial_mul_factorial` | `Mathlib/Data/Nat/Choose/Basic.lean:141` | ✅ unchanged |
| 5 | `Complex.ofReal_pow` | `Mathlib/Data/Complex/Basic.lean:621` | ✅ unchanged |
| 6 | `Nat.ascFactorial_pos` | `Mathlib/Data/Nat/Factorial/Basic.lean:301` | ✅ unchanged |
| 7 | `intervalIntegral.integral_ofReal` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:810` | ✅ unchanged |
| 8 | `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (de-recommended) | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:142` | ✅ unchanged |

## NEW Bearer 9 — `Complex.cpow_natCast` (cpow ↔ npow bridge)

`Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:124`:

```lean
@[simp, norm_cast]
theorem cpow_natCast (x : ℂ) (n : ℕ) : x ^ (n : ℂ) = x ^ n := by simpa using cpow_nat_mul x n 1
```

**Why this matters for the cast-bridge**: `Complex.betaIntegral` is defined
at `Beta.lean:60` as

```lean
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)
```

where the `^` denotes `Complex.cpow` (the noncomputable, principal-branch
power). For our specialization `u = (k+1 : ℂ)`, `v = (n-k+1 : ℂ)`, the
exponents simplify to `(k : ℂ)` and `((n-k) : ℂ)` respectively. To bridge to
the **natural-exponent** Hanson integrand
`x ^ k * (1 - x) ^ (n - k)` (where `^` is `Monoid.npow` over ℝ), we need
to convert `cpow` → `npow`. **Bearer 9 does this in one `simp` step** (it
is `@[simp, norm_cast]`).

**Falsifiability check** (Iter 42, doc-only): If `cpow_natCast` had been
removed or relocated at v4.26.0, the cast-bridge would require an explicit
`Complex.cpow_def` unfold + branch-cut argument. Bearer 9's continued
presence at the pinned SHA (verbatim, `@[simp, norm_cast]` attributes
intact) means the bridge stays a one-`simp`-call affair.

## NEW Bearer 10 — `Complex.ofReal_*` cast-family (six lemmas, all in `Mathlib/Data/Complex/Basic.lean` at SHA `2df2f0150c…`)

The cast-bridge proof requires push/pull of the ℝ→ℂ coercion through
multiplication, subtraction, the literal `1`, natural casts, natural powers,
and equality. All six lemmas are confirmed `@[simp, norm_cast]` at v4.26.0:

| Lemma | Line | Signature | Note |
|-------|-----:|-----------|------|
| `Complex.ofReal_inj` | 98 | `(z : ℂ) = w ↔ z = w` | `↔`-form; rewrite-friendly |
| `Complex.ofReal_one` | 154 | `((1 : ℝ) : ℂ) = 1` | literal-1 bridge |
| `Complex.ofReal_mul` | 214 | `((r * s : ℝ) : ℂ) = r * s` | multiplicative |
| `Complex.ofReal_natCast` | 339 | `ofReal n = n` (for `n : ℕ`) | `n+1` and `Nat.choose n k` casts |
| `Complex.ofReal_sub` | 617 | `((r - s : ℝ) : ℂ) = r - s` | `1 - x` bridge |
| `Complex.ofReal_pow` | 621 | `((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n` | npow bridge (Iter 41 Bearer 5) |

**Composite tactic**: a single `push_cast` invocation after `rw
[← Complex.ofReal_inj]` should reduce the goal to a ℂ-level equation
involving `(x : ℂ)^k * (1 - (x : ℂ))^(n - k)` (npow), matching the cpow→npow
output of Bearer 9. The composite `simp` set
`[Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
Complex.ofReal_pow, Complex.ofReal_natCast]` is the load-bearing rewrite
list — Iter 43+ ACT should expect `push_cast` to dispatch this in one call,
with `simp only [...]` as the precise fallback if `push_cast` overshoots.

## Consolidated paste-ready Lean block (Iter 42 PREP §"The full ACT")

Below is the **complete paste-ready Lean fragment** for Iter 43+ ACT. It
combines:

- Iter 39 outer `complex_betaIntegral_nat_eq_choose_inv` skeleton
- Iter 39 Step 3 cleanup drop-in body (Sorry-1 — terminal `sorry` replaced
  with explicit `linear_combination` body + fallback)
- Iter 41 Bearer 6 patch (Sorry-2 → `Nat.ascFactorial_pos k (n - k + 1)`)
- Iter 41 cast-bridge `real_betaIntegral_nat_eq_choose_inv` (Step 6 sketch
  `sorry` replaced with the full body)

**Insertion point**: after Iter 38's `exists_witness_choose_saturates_log_succ`
(line 1661) but before Iter 35b's `choose_mul_succ_dvd_lcmRange` (line
1758) **OR** as a self-contained block immediately before line 1791
(`axiom hanson_bound`). The block is locally self-contained.

**Imports to add near the top of the file** (current file imports
`Mathlib.Tactic` only):

```lean
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
```

(Bearer 9 `Complex.cpow_natCast` is transitively reachable through the
Beta import; no separate `Pow/Complex` import needed.)

**Paste-ready block (~80 LOC including docstrings)**:

```lean
/-- The Beta integral at natural arguments evaluates to a rational number
whose denominator is `(n+1) * C(n,k)`. Specialization over ℂ of Mathlib's
`Complex.betaIntegral_eval_nat_add_one_right`. -/
theorem complex_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n) :
    Complex.betaIntegral (k + 1 : ℂ) (n - k + 1 : ℂ) =
      (1 : ℂ) / ((n + 1 : ℂ) * (Nat.choose n k : ℂ)) := by
  have hu : 0 < ((k + 1 : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- Step 1: Mathlib explicit formula for Beta at (u, n+1) with u = k+1.
  rw [Complex.betaIntegral_eval_nat_add_one_right hu (n - k)]
  -- LHS = (n - k)! / ∏ j ∈ range (n-k+1), ((k+1 : ℂ) + j)
  -- Step 2: identify the finite product with an ascending factorial.
  have h_prod : ∏ j ∈ Finset.range (n - k + 1), ((k + 1 : ℂ) + j) =
                  ((k + 1).ascFactorial (n - k + 1) : ℂ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [h_prod]
  -- Step 3: positivity / nonzero side-conditions for `field_simp`.
  have h_pos_asc : (((k + 1).ascFactorial (n - k + 1) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < (k + 1).ascFactorial (n - k + 1) :=
      Nat.ascFactorial_pos k (n - k + 1)            -- Bearer 6 (Iter 41)
    exact_mod_cast this.ne'
  have h_pos_n1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h_pos_ch : ((Nat.choose n k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  -- Step 4: factorial identities lifted to ℂ.
  have h_asc : k ! * (k + 1).ascFactorial (n - k + 1) = (n + 1)! := by
    have := Nat.factorial_mul_ascFactorial k (n - k + 1)
    have hk_sub : k + (n - k + 1) = n + 1 := by omega
    rwa [hk_sub] at this
  have h_choose : Nat.choose n k * k ! * (n - k)! = n ! :=
    Nat.choose_mul_factorial_mul_factorial hk
  have h_succ : ((n + 1)! : ℕ) = (n + 1) * n ! := Nat.factorial_succ n
  have h_asc_C : ((k ! : ℕ) : ℂ) *
      ((((k + 1).ascFactorial (n - k + 1)) : ℕ) : ℂ) = (((n + 1)! : ℕ) : ℂ) := by
    exact_mod_cast h_asc
  have h_choose_C : ((Nat.choose n k : ℕ) : ℂ) * ((k ! : ℕ) : ℂ) *
      (((n - k)! : ℕ) : ℂ) = ((n ! : ℕ) : ℂ) := by
    exact_mod_cast h_choose
  have h_succ_C : (((n + 1)! : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) * ((n ! : ℕ) : ℂ) := by
    exact_mod_cast h_succ
  -- Step 5: clear denominators and discharge via `linear_combination` (primary)
  --         or hand-rolled `ring` (fallback).
  field_simp
  -- After field_simp the goal is the polynomial identity (in ℂ)
  --   (n - k)! * ((n + 1) * Nat.choose n k) = (k + 1).ascFactorial (n - k + 1)
  -- (modulo `field_simp`'s order; the v4.26.0 normaliser may reorder).
  -- Primary: linear_combination of h_choose_C and h_asc_C / h_succ_C.
  --   (n+1) * Nat.choose n k * k! * (n - k)! = (n+1) * n! = (n+1)!  [h_choose_C × (n+1), h_succ_C]
  --   k! * ascFactorial (n - k + 1) = (n+1)!                      [h_asc_C]
  --   Therefore: (n - k)! * (n+1) * Nat.choose n k = ascFactorial. ✓
  linear_combination
    ((n - k)! : ℂ) * h_choose_C - (((n - k)! : ℕ) : ℂ) * h_asc_C
  -- Fallback (if `linear_combination` syntax drifts at v4.26.0): comment out
  -- the line above and uncomment the hand-rolled discharge below.
  -- have := h_choose_C
  -- have := h_asc_C
  -- have := h_succ_C
  -- ring_nf
  -- linarith [h_asc_C, h_choose_C, h_succ_C]   -- or: nlinarith / polyrith

/-- The real Beta integral with natural exponents equals `1 / ((n+1) · C(n,k))`.
Real-valued specialization of `complex_betaIntegral_nat_eq_choose_inv`, obtained
by casting the integrand to ℂ via `Complex.ofReal_*` + `Complex.cpow_natCast`
+ `intervalIntegral.integral_ofReal`, then descending via `Complex.ofReal_inj`. -/
theorem real_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0:ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
      (1 : ℝ) / ((n + 1 : ℝ) * (Nat.choose n k : ℝ)) := by
  -- Step A: descend the ℝ-equation through `ofReal_inj` to an equivalent ℂ-equation.
  rw [show (1 : ℝ) / ((n + 1 : ℝ) * (Nat.choose n k : ℝ)) =
         ((1 : ℂ) / ((n + 1 : ℂ) * (Nat.choose n k : ℂ))).re from ?_]
  · -- Real part of the cast-up integral matches `Complex.betaIntegral`.
    -- Cast the real integral into ℂ via `intervalIntegral.integral_ofReal`.
    rw [show ∫ x in (0:ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
             (∫ x in (0:ℝ)..1,
                ((x ^ k * (1 - x) ^ (n - k) : ℝ) : ℂ)).re from ?_]
    · -- Step B: rewrite the ℂ-integral as `Complex.betaIntegral (k+1) (n-k+1)`.
      have hβ : Complex.betaIntegral (k + 1 : ℂ) (n - k + 1 : ℂ) =
          ∫ x in (0:ℝ)..1, ((x ^ k * (1 - x) ^ (n - k) : ℝ) : ℂ) := by
        unfold Complex.betaIntegral
        apply intervalIntegral.integral_congr
        intro x _
        -- Both sides equal `(x : ℂ)^k * (1 - (x : ℂ))^(n-k)` after cpow→npow
        -- and ofReal_* push.
        have hk_exp : ((k + 1 : ℂ) - 1) = ((k : ℕ) : ℂ) := by push_cast; ring
        have hnk_exp : ((n - k + 1 : ℂ) - 1) = (((n - k) : ℕ) : ℂ) := by
          push_cast; ring
        rw [hk_exp, hnk_exp, Complex.cpow_natCast, Complex.cpow_natCast]
        push_cast
        ring
      rw [← hβ, complex_betaIntegral_nat_eq_choose_inv n k hk]
    · -- Discharge the integral_ofReal rewrite obligation.
      rw [← intervalIntegral.integral_ofReal]
      simp [Complex.ofReal_re]
  · -- Discharge the .re extraction of `1 / ((n+1) * choose)`.
    have h_n1 : ((n + 1 : ℝ) : ℂ) = (n + 1 : ℂ) := by push_cast; ring
    have h_ch : ((Nat.choose n k : ℝ) : ℂ) = (Nat.choose n k : ℂ) := by push_cast
    -- 1 / ((n+1) * Nat.choose n k) is real-valued (both factors are real-coerced).
    rw [show (1 : ℂ) / ((n + 1 : ℂ) * (Nat.choose n k : ℂ)) =
           (((1 : ℝ) / ((n + 1 : ℝ) * (Nat.choose n k : ℝ))) : ℂ) from ?_]
    · simp [Complex.ofReal_re]
    · push_cast
      ring
```

**Net Lean delta** (Iter 43+ ACT, projected):
- Lean LOC: 1802 → ~1882 (+80, matches Iter 41 §"Estimated ACT LOC under
  cast-bridge").
- Imports: +2 lines.
- Theorems: 77 → 79 (`complex_betaIntegral_nat_eq_choose_inv` + `real_betaIntegral_nat_eq_choose_inv`).
- Axioms: 1 → 1 (`hanson_bound` unchanged — this PREP/ACT does NOT close it;
  integer-squeeze assembly is the separate Iter 44+ step that requires both
  28a (this) and the existing `hanson_n1..hanson_n100` numerical floor).
- Sorries: 0 → 0 (paste-ready block is `sorry`-free in the primary
  `linear_combination` branch; the fallback `-- ring_nf` branch is for
  Iter 43+ to swap in *only if* the primary branch fails to compile).

## Step-by-step risk register (Iter 42 update)

| Step | Lemma / tactic | Iter 41 risk | Iter 42 outcome |
|------|----------------|--------------|------------------|
| 1 | `Complex.betaIntegral_eval_nat_add_one_right` | Low | ✅ verbatim @ 202 |
| 2 | `Nat.ascFactorial_eq_prod_range` + `push_cast` + `ring` | Low | ✅ Bearer 2 unchanged |
| 3 (Iter 41 Bearer 6) | `Nat.ascFactorial_pos k (n - k + 1)` | resolved Iter 41 | ✅ Bearer 6 unchanged |
| 4 (factorial identities) | `Nat.factorial_mul_ascFactorial` + `Nat.choose_mul_factorial_mul_factorial` | Low | ✅ Bearers 3,4 unchanged |
| 5 (terminal `linear_combination`) | Medium (tactic syntax drift) | ⚠️ NOT probed under build; explicit body provided + hand-rolled fallback documented |
| A (`ofReal_inj` descent) | not flagged | ✅ Bearer 10 row 1 |
| B (`cpow_natCast`) | not flagged | ✅ Bearer 9 |
| B (`integral_ofReal`) | resolved Iter 41 | ✅ Bearer 7 unchanged |
| B (`push_cast` / `simp` set) | not flagged | ✅ Bearer 10 composite set documented |

**Remaining Medium risk**: terminal `linear_combination` at v4.26.0
syntax. The Iter 42 explicit body uses the coefficient form
`linear_combination ((n - k)! : ℂ) * h_choose_C - … * h_asc_C`; if this
fails, the fallback hand-rolled discharge via `ring_nf` + `linarith`
remains viable (all three identities `h_asc_C`, `h_choose_C`, `h_succ_C`
combine to the same monomial). Iter 43+ ACT author should expect to
attempt the primary line first, fall back ONLY on compilation failure.

## What this PREP does NOT include

1. **No Lean edits**. Doc-only PREP per Iter 36 / 38 / 39 / 41 precedent.
   `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` byte-identical to Iter 38 ACT
   (md5 `4b4ac86002cb4c60b7a2863c157dad48`).
2. **No build verification**. No `./proofs/scripts/docker-build.sh` run.
   Sibling Docker container `lean-build-57602` (image `9026c55995…`,
   the corrupted-blob image backing `lean4-arm64:v4.26.0`) has been up
   ~4 hours holding the lean4 image; running a parallel build would risk
   image corruption surfacing as a hard-fail. All bearer signatures
   verified via direct source inspection at SHA `2df2f0150c…` (the same
   SHA Iter 38 ACT build-verified at 3066/3066 jobs).
3. **No `linear_combination` / `field_simp` probe under build**. These
   tactic-syntax risks remain Medium. The Iter 42 paste-ready block
   provides an explicit coefficient body AND a documented hand-rolled
   fallback so Iter 43+ ACT can iterate cheaply.
4. **No reduction of `axiom hanson_bound`**. The integer-squeeze closure
   requires 28a (this chain) + the existing `hanson_n1..hanson_n100`
   numerical floor (file lines 1391–1462). This PREP improves readiness
   for 28a ACT but does not close any axiom.
5. **No edits to `knowledge.md`, `problem.md`, or gallery `meta.json`**.
   Edits limited to this session log + `state.md` Iter 42 narrative +
   research JSON `currentState` updates.

## Honest framing / self-audit

- **Doc-only, no Lean shipped**: continuation of Iter 36 / Iter 39 /
  Iter 41 paste-ready-skeleton format. Lean file is byte-identical to its
  Iter 38 ACT state.
- **Adds two NEW bearers** (Bearer 9 `Complex.cpow_natCast`, Bearer 10
  `Complex.ofReal_*` family of six lemmas). Both verified verbatim at the
  pinned SHA via direct source inspection.
- **Removes Iter 41's remaining sketch-`sorry`** (cast-bridge Step 6):
  the consolidated block above has a full body for
  `real_betaIntegral_nat_eq_choose_inv`. The terminal `field_simp` +
  `linear_combination` in `complex_betaIntegral_nat_eq_choose_inv` retains
  Medium tactic-syntax risk but is no longer represented as a `sorry` —
  it is an explicit coefficient body with a documented fallback.
- **Surfaces the cpow→npow gap** Iter 41 did not flag: the
  `Complex.betaIntegral` integrand uses `cpow`, not `Monoid.npow`. Without
  Bearer 9, the cast-bridge would need an explicit `Complex.cpow_def`
  unfold + branch-cut argument, inflating the ACT LOC estimate ~20-30 LOC.
  With Bearer 9 in place (verified), the bridge is a one-`simp` step.
- **`hanson_bound` remains an axiom**. No reduction. After this PREP +
  Iter 43+ ACT lands 28a, the integer-squeeze assembly + existing
  `hanson_n1..hanson_n100` numerical floor would close the axiom.
- **No edits outside the three doc files**: this session log, `state.md`,
  research JSON. The next ACT iteration will update the Lean file,
  `meta.json`, and `knowledge.md`.

## Cross-references

- Iter 28 PREP (2026-05-12, #18352): Route B vs A vs C strategic choice.
- Iter 29 PREP (2026-05-12, #18485): initial bearer audit + errata.
- Iter 34a ACT (2026-05-15, #19208): 28b-1 bound + Lemma A.
- Iter 35b ACT (2026-05-15, #19372): 28c divisibility bridge.
- Iter 36 PREP (2026-05-15, #19499): 28b-2 paste-ready discharge.
- Iter 37 INFRA-SIGNAL (2026-05-25, #20636): Docker gate RED→GREEN.
- Iter 38 ACT (2026-05-28, #20863): 28b-2 witness saturation shipped.
- Iter 39 PREP (2026-05-31, #21401): 28a paste-ready skeleton.
- Iter 40 STATE-SYNC (2026-05-31, #21544): state.md catch-up post Iter 39.
- Iter 41 PREP (2026-06-01, #22033): bearer re-verify + IBP probe + cast-bridge recommendation.

## What the next researcher should do (Iter 43+)

**Recommended path** — ship 28a Beta-integral identity by pasting the
consolidated block (§"The full ACT" above) directly into
`Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` after Iter 38's
`exists_witness_choose_saturates_log_succ` (line 1661), add the two
imports listed above, and build-verify under
`./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03`.

**Pre-build sanity check**: confirm sibling Docker container
`lean-build-57602` (corrupted-blob holder) is either released or quiesced
before launching a parallel build. The shared image
`9026c55995f4` backing `lean4-arm64:v4.26.0` is fragile; a single
corrupted-blob recovery may cascade to all in-flight containers.

**Expected ACT size**: ~80 LOC (cast-bridge path).
**Expected wall-clock**: 1 session (one or two `docker-build.sh` iterations
to discharge `linear_combination` syntax drift).
**Primary risk (Medium)**: `linear_combination` tactic syntax at v4.26.0.
On compilation failure, swap the primary `linear_combination` line for
the documented `ring_nf` + `linarith` fallback (or `polyrith` / `nlinarith`
depending on what compiles). Pre-cleared identities `h_asc_C`,
`h_choose_C`, `h_succ_C` make any fallback monomial-level.

Post-28a, the integer-squeeze closure of `axiom hanson_bound` follows
once `n₀ ≤ 100` is established by the existing `hanson_n1..hanson_n100`
numerical floor — that floor is already in place at lines 1391–1462 of
the live file. Iter 44+ would assemble the squeeze + drop the axiom.
