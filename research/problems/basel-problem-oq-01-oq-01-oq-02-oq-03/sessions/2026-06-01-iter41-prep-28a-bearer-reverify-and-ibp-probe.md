# Iteration 41 PREP — 28a Beta-integral bearer re-verification + IBP probe

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: PREP (Option B from Iter 39 §"What the next researcher should do"
— front-load uncertainty reduction before 28a ACT)
**Type**: Doc-only. No edits to `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`,
`knowledge.md`, `problem.md`, or gallery `meta.json`. Edits limited to this
session log, `state.md` (Iter 41 narrative + header refresh), and
`src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json`
(`currentState.iteration`/`phase`/`focus`/`nextAction` + `lastUpdate`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged from Iter 36 PREP audit, Iter 38 ACT build, Iter 39 PREP).
**Base HEAD**: `f486a19e2e05985565214fe6be0f7435d12d5d28` (Iter 40
STATE-SYNC #21544 merged → ballot-problem mainTheorems drift fix #21908).

## Rationale

Iter 39 PREP #21401 (researcher-1, 2026-05-31) provided a paste-ready Lean
skeleton for the 28a Beta-integral identity ACT. The skeleton contains
**two unresolved sorries** plus a flagged "Higher risk" item:

- **Sorry-1** (Step 3 cleanup): closes via `field_simp` +
  `linear_combination` over `factorial_mul_ascFactorial` and
  `choose_mul_factorial_mul_factorial`. Marked "Medium risk" (tactic
  syntax drift v4.25 → v4.26).
- **Sorry-2** (`h_pos_asc` witness): needs a lemma
  `0 < (k + 1).ascFactorial (n - k + 1)`. Marked TODO inline as
  `Mathlib's Nat.ascFactorial_pos: 0 < n → 0 < n.ascFactorial k` (the
  predicted signature was wrong — actual signature differs, see §"Bearer 6"
  below).
- **Higher-risk item**: `intervalIntegral.integral_ofReal` exact lemma
  name and module path at v4.26.0. Iter 39 noted "varies between
  `MeasureTheory.integral_re` and `intervalIntegral.integral_ofReal`
  depending on which Mathlib refactor wave is current" but did NOT pin
  the actual path. Iter 41 PREP closes this.

Iter 39 also recommended a 5–10 line probe of
`intervalIntegral.integration_by_parts` to choose between the cast-bridge
path (~30–50 LOC) and direct-IBP path (~50–80 LOC) for the real
↔ complex bridge. Iter 41 PREP performs that probe and pins the actual
v4.26.0 IBP lemma name.

This PREP is **doc-only**. No Lean edits, no axiom/sorry delta in the
live file. File state remains 1802 LOC, 1 axiom (`hanson_bound`), 0
sorries since Iter 38 ACT #20863 (2026-05-28).

## Re-verification of Iter 39 Bearers 1–5 at SHA `2df2f0150c…`

All five Iter 39 bearers re-verified via direct source inspection of the
local Mathlib mirror at the pinned SHA
(`git show 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67:<path>`). No
`lake build` was used — SHA-pinned source is authoritative.

| # | Bearer | Path:Line at v4.26.0 | Iter 39 claim | Iter 41 verdict |
|---|--------|----------------------|---------------|-----------------|
| 1 | `Complex.betaIntegral_eval_nat_add_one_right` | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:202` | line 202–203 | ✅ confirmed |
| 2 | `Nat.ascFactorial_eq_prod_range` | `Mathlib/Data/Nat/Factorial/BigOperators.lean:49–51` | line 49–51 | ✅ confirmed |
| 3 | `Nat.factorial_mul_ascFactorial` | `Mathlib/Data/Nat/Factorial/Basic.lean:227–233` | line 227–233 | ✅ confirmed |
| 4 | `Nat.choose_mul_factorial_mul_factorial` | `Mathlib/Data/Nat/Choose/Basic.lean:141` | line 141 | ✅ confirmed |
| 5 | `Complex.ofReal_pow` | `Mathlib/Data/Complex/Basic.lean:621` | path only (no line in Iter 39) | ✅ confirmed (line 621) |

All five signatures match Iter 39's quoted source verbatim. No drift
since 2026-05-31 (the local mirror was at a later commit `05147a76` for
unrelated CstarAlgebra work; the pinned `2df2f0150c` SHA is reachable as
the `v4.26.0` toolchain-bump commit).

## NEW Bearer 6 — `Nat.ascFactorial_pos` (resolves sorry-2)

`Mathlib/Data/Nat/Factorial/Basic.lean:301`:

```lean
theorem ascFactorial_pos (n k : ℕ) : 0 < (n + 1).ascFactorial k :=
  Nat.lt_of_lt_of_le (Nat.pow_pos n.succ_pos) (pow_succ_le_ascFactorial (n + 1) k)
```

**Status**: present at v4.26.0. The signature requires the base of the
ascending factorial to have the syntactic shape `(n + 1).ascFactorial k`
(NOT arbitrary `m.ascFactorial k`), which the Iter 39 skeleton naturally
satisfies — the application site is `(k + 1).ascFactorial (n - k + 1)`,
so we invoke `Nat.ascFactorial_pos k (n - k + 1) : 0 < (k + 1).ascFactorial (n - k + 1)`.

**Iter 39 prediction error**: the inline TODO claimed signature
`0 < n → 0 < n.ascFactorial k`. The actual signature has the `+1` on the
base **syntactically required** (no hypothesis; positivity is structural).
This is strictly more convenient for our application — no `0 < k+1`
hypothesis to discharge.

**Drop-in replacement for Iter 39 sorry-2** (the `h_pos_asc` helper):

```lean
  have h_pos_asc : (((k + 1).ascFactorial (n - k + 1) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < (k + 1).ascFactorial (n - k + 1) := Nat.ascFactorial_pos k (n - k + 1)
    exact_mod_cast this.ne'
```

Sorry-2 is now **fully resolved** at the Mathlib-API level. ACT cost: 0
additional LOC beyond the Iter 39 skeleton (replaces one `sorry` line with
two tactic-mode lines; net delta ~1 LOC).

## NEW Bearer 7 — IntervalIntegral directory refactor

**Iter 39 omission (now corrected)**: Iter 39 wrote
`Mathlib/MeasureTheory/Integral/IntervalIntegral.lean` as the cast-bridge
file path. **This file does NOT exist at v4.26.0** — it has been
refactored into a **directory** `Mathlib/MeasureTheory/Integral/IntervalIntegral/`
with 11 submodules:

```
Mathlib/MeasureTheory/Integral/IntervalIntegral/
├── Basic.lean
├── ContDiff.lean
├── DerivIntegrable.lean
├── FundThmCalculus.lean
├── IntegrationByParts.lean
├── LebesgueDifferentiationThm.lean
├── Periodic.lean
├── Slope.lean
└── TrapezoidalRule.lean
(plus ParametricIntervalIntegral.lean in Mathlib/Analysis/Calculus/)
```

Furthermore, every file uses the v4.26.0 **module system** keywords
(`module` / `public import`). The Basel file imports `Mathlib.Tactic`
only (not specific IntervalIntegral submodules), so the ACT will need to
add a small number of targeted imports:

```lean
-- For Bearer 1 (betaIntegral_eval_nat_add_one_right):
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

-- For Bearer 7 (integral_ofReal, cast-bridge path):
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- For Bearer 8 (integral_mul_deriv_eq_deriv_mul, direct-IBP path — alternative):
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
```

These imports are **stable transitively reachable** via `import Mathlib`,
but explicit imports keep build times bounded (the Basel file currently
takes ~5 min single-file under Docker; adding `import Mathlib` would
inflate this substantially).

### Bearer 7a — `intervalIntegral.integral_ofReal` (cast-bridge path)

`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:810`:

```lean
nonrec theorem integral_ofReal {a b : ℝ} {μ : Measure ℝ} {f : ℝ → ℝ} :
    (∫ x in a..b, (f x : ℂ) ∂μ) = ↑(∫ x in a..b, f x ∂μ) :=
  RCLike.intervalIntegral_ofReal
```

**Status**: present at v4.26.0, namespace `intervalIntegral`. Signature
takes a real-valued `f : ℝ → ℝ` and casts the integrand to ℂ inside the
integral, equating with the ℂ-coercion of the real integral. This is
exactly the **cast-bridge direction** the Iter 39 skeleton needs (the
predicted `MeasureTheory.integral_re` alternative does NOT exist at this
SHA — `integral_re` would be the dual extracting real parts, not casting
in).

**Iter 39 prediction error**: Iter 39 §"Higher risk" hedged on the lemma
name "varies between `MeasureTheory.integral_re` and
`intervalIntegral.integral_ofReal`". Verdict: it is
**`intervalIntegral.integral_ofReal`** at v4.26.0. The `_root_.integral_ofReal`
companion (for the non-interval version) sits at
`Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:158`:

```lean
theorem integral_ofReal {f : X → ℝ} : ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ) := …
```

(generic over `RCLike 𝕜`; the interval version specializes to ℂ via the
`nonrec` declaration above).

### Bearer 8 — `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (direct-IBP alternative)

`Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:142`:

```lean
theorem integral_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := …
```

**Status**: present at v4.26.0. The lemma name
`intervalIntegral.integration_by_parts` used in the Iter 29 / Iter 39
prose **does NOT exist** as an alias — the actual API is the family
`integral_mul_deriv_eq_deriv_mul` (+ `_of_hasDerivAt`, `_of_hasDerivWithinAt`,
`_of_hasDeriv_right` variants in the same file at lines 87, 98, 111,
123, 142). The relevant variant for the Hanson integrand
`x^k · (1-x)^(n-k)` (polynomial in `x`, so `HasDerivAt` everywhere on
ℝ, not just `[0, 1]`) is the **fully strong** `integral_mul_deriv_eq_deriv_mul`
at line 142, which takes pointwise `HasDerivAt` over the closed interval
`[[a, b]] = uIcc a b`.

**The dual form** `integral_deriv_mul_eq_sub` (line 87) lifts
`∫ x in a..b, u'(x)·v(x) + u(x)·v'(x) = u(b)·v(b) - u(a)·v(a)` and is
the lemma whose subtraction yields the IBP form. For the induction-on-k
direct-IBP proof, both are usable — pick whichever has the cleaner
discharge for the polynomial differentiability obligations.

## The cast-bridge vs direct-IBP choice — recommendation

With both Bearer 7a and Bearer 8 now pinned at v4.26.0, the Iter 39
"choose at ACT time" hedge can be retired:

**Recommendation: cast-bridge path**.

Reasons:

1. **Smaller LOC**: ~30–50 LOC vs. 50–80 LOC.
2. **Reuses the Iter 39 `complex_betaIntegral_nat_eq_choose_inv` skeleton verbatim**;
   the bridge is a single application of `intervalIntegral.integral_ofReal`
   to convert the real-valued Hanson integrand
   `∫ x in (0:ℝ)..1, x^k · (1-x)^(n-k) ∂volume`
   into its ℂ-coerced form
   `∫ x in (0:ℝ)..1, ((x^k · (1-x)^(n-k) : ℝ) : ℂ) ∂volume`,
   then a `Complex.ofReal_pow` + `Complex.ofReal_mul` push of the
   coercion through the polynomial integrand to match Beta's
   `(x : ℂ)^(k : ℕ) · (1 - x : ℂ)^(n - k : ℕ)` shape.
3. **Avoids re-deriving an IBP induction** the Iter 38 chain already
   sidestepped via the Beta-identity route. Direct-IBP would essentially
   rebuild Mathlib's `betaIntegral_recurrence` (used in the proof of
   Bearer 1) inside the Basel file — duplicating work.
4. **Lower API-drift risk**: `Complex.ofReal_pow` and
   `intervalIntegral.integral_ofReal` are both pinned to v4.26.0 line
   numbers with verbatim source above. The IBP route would require
   pinning 3–5 additional `HasDerivAt` lemmas for the polynomial
   integrand.

**Estimated ACT LOC under the cast-bridge recommendation**:

| Section | LOC | Status |
|---|---:|---|
| Imports (3 new lines) | 3 | this PREP |
| `complex_betaIntegral_nat_eq_choose_inv` (Iter 39 calc shell) | ~25 | Iter 39 §"The full chain" |
| Sorry-1 discharge (Step 3 cleanup, `field_simp` + `linear_combination`) | ~25 | Iter 39 drop-in body |
| Sorry-2 discharge (`Nat.ascFactorial_pos k (n - k + 1)`) | ~1 | this PREP §"Bearer 6" |
| `real_betaIntegral_nat_eq_choose_inv` (cast-bridge) | ~25 | this PREP §"sketch below" |
| **Total** | **~80** | matches Iter 39 lower estimate |

The Iter 39 upper bound (100 LOC) was conservative for the
direct-IBP path; with the recommendation locked to cast-bridge, the
working estimate tightens to ~80 LOC.

## Cast-bridge sketch (replaces Iter 39 §"Real ↔ complex bridge" sorry)

```lean
/-- The real Beta integral with natural exponents equals 1/((n+1)·C(n,k)).
Real-valued specialization of `complex_betaIntegral_nat_eq_choose_inv`,
obtained by casting the integrand to ℂ via `Complex.ofReal_pow` +
`intervalIntegral.integral_ofReal`, then taking real parts. -/
theorem real_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0:ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
      (1 : ℝ) / ((n + 1 : ℝ) * (Nat.choose n k : ℝ)) := by
  -- Step 1: cast both sides to ℂ. The real integral becomes
  --   (↑∫ x in 0..1, x^k * (1-x)^(n-k) : ℂ).
  --   The RHS becomes 1 / ((n+1 : ℂ) * Nat.choose n k).
  -- Step 2: by intervalIntegral.integral_ofReal applied to the polynomial integrand,
  --   ↑∫ x in 0..1, x^k * (1-x)^(n-k)
  --     = ∫ x in (0:ℝ)..1, ((x^k * (1-x)^(n-k) : ℝ) : ℂ).
  -- Step 3: push the coercion through ofReal_mul + ofReal_pow + ofReal_sub + ofReal_one
  --   to get  ∫ x in (0:ℝ)..1, (x : ℂ)^k * (1 - (x : ℂ))^(n - k).
  -- Step 4: the integrand matches Complex.betaIntegral (k+1 : ℂ) (n - k + 1 : ℂ)'s
  --   integrand after re-indexing exponents (k+1-1 = k, n-k+1-1 = n-k); apply
  --   the definition unfolding from Complex.betaIntegral.
  -- Step 5: rewrite via complex_betaIntegral_nat_eq_choose_inv n k hk.
  -- Step 6: ofReal_inj to descend back to ℝ.
  sorry  -- ~25 LOC at ACT time; structure pinned by Steps 1-6 above
```

The sketch above leaves a single sorry at the ℂ → ℝ descent (Step 6).
The intermediate Steps 1–5 each have one explicit Mathlib bearer
(pinned in §"Bearer 7a" above). ACT-time author should expect ~5
lines per step, plus a `push_cast` cleanup pass before Step 6's
`ofReal_inj`.

## Status of Iter 39 risk register

Iter 39 §"Risk register" listed three risks. Iter 41 PREP retires two
and keeps one open:

| Item | Iter 39 risk | Iter 41 outcome |
|------|--------------|-----------------|
| Bearers 1–4 at SHA `2df2f0150c…` | Low | ✅ confirmed (all 4 verbatim lines unchanged) |
| `linear_combination` tactic v4.25→v4.26 syntax | Medium | ⚠️ NOT probed (residual risk; ACT-time author must test) |
| `field_simp` over ℂ residual | Medium | ⚠️ NOT probed (residual risk; ACT-time author must test) |
| `intervalIntegral.integral_ofReal` exact name | **Higher** | ✅ confirmed at `IntervalIntegral/Basic.lean:810` |
| IntervalIntegral file vs directory layout | (not flagged) | 🆕 directory at v4.26.0; imports listed §"Bearer 7" |
| `Nat.ascFactorial_pos` exact signature | (sorry-2 inline TODO) | ✅ confirmed at `Factorial/Basic.lean:301`; sorry-2 resolvable in ~1 LOC |
| IBP lemma name `intervalIntegral.integration_by_parts` | (Option B hedge) | ❌ does NOT exist; correct name is `integral_mul_deriv_eq_deriv_mul` |
| cast-bridge vs direct-IBP choice | "decide at ACT time" | 🎯 **cast-bridge recommended** (4 reasons, §"recommendation") |

## What this PREP does NOT include

1. **No Lean edits**. Doc-only PREP per Iter 38 / Iter 39 / Iter 40
   precedent. `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` unchanged at
   1802 LOC, 1 axiom, 0 sorries.
2. **No build verification**. No `lake build` / Docker build was
   performed. All bearer signatures verified via direct source
   inspection at SHA `2df2f0150c…` (the SHA Iter 38 ACT
   build-verified at 3066/3066 jobs).
3. **No `linear_combination` / `field_simp` probe**. These tactic-syntax
   risks remain Medium. Iter 39's drop-in body for Sorry-1 is unchanged
   by this PREP and may still need minor tactic-syntax adjustment at
   ACT time. A focused probe is left to the Iter 42+ ACT author (or a
   tighter follow-up PREP).
4. **No reduction of `axiom hanson_bound`**. The integer-squeeze
   closure of `hanson_bound` requires 28a (this chain) + the existing
   `hanson_n1..hanson_n100` numerical floor. This PREP improves
   readiness for 28a ACT but does not close any axiom.
5. **No edits to `knowledge.md`, `problem.md`, or gallery `meta.json`**.
   Edits limited to this session log + `state.md` Iter 41 narrative +
   research JSON `currentState` updates.

## Honest framing / self-audit

- **Doc-only, no Lean shipped**: this PREP is a continuation of the
  Iter 36 / Iter 39 paste-ready-skeleton format. Lean file is
  byte-identical to its Iter 38 ACT state.
- **Adds two NEW bearers** (Bearer 6 `Nat.ascFactorial_pos`,
  Bearer 7 cast-bridge `intervalIntegral.integral_ofReal`) and **one
  alternative bearer** (Bearer 8 IBP `integral_mul_deriv_eq_deriv_mul`).
  All three pinned to verbatim source at SHA `2df2f0150c…`.
- **Corrects two Iter 39 prediction errors**:
  - `Nat.ascFactorial_pos` signature requires `(n+1).ascFactorial k`
    syntactically (no hypothesis), strictly more convenient than the
    `0 < n → ...` predicted form.
  - `intervalIntegral.integration_by_parts` (as named) does not
    exist; correct API is `integral_mul_deriv_eq_deriv_mul`.
- **Locks a recommendation**: cast-bridge path (~80 LOC) supersedes
  Iter 39's "choose at ACT time" hedge. The Iter 42+ ACT author can
  still override if they discover something during compilation, but
  the default is now pinned.
- **`hanson_bound` remains an axiom**. No reduction. After this PREP
  + Iter 42 ACT lands 28a, the integer-squeeze assembly + existing
  `hanson_n1..hanson_n100` numerical floor would close the axiom.
- **No edits outside the four files listed**: this session log,
  `state.md`, research JSON, and (per request) no proof file, no
  knowledge.md, no problem.md, no gallery meta.json. The next ACT
  iteration will update those.

## Cross-references

- Iter 28 PREP (2026-05-12, #18352): Route B vs A vs C strategic choice.
- Iter 29 PREP (2026-05-12, #18485): initial bearer audit + errata.
- Iter 34a ACT (2026-05-15, #19208): 28b-1 bound + Lemma A.
- Iter 35b ACT (2026-05-15, #19372): 28c divisibility bridge.
- Iter 36 PREP (2026-05-15, #19499): 28b-2 paste-ready discharge.
- Iter 37 INFRA-SIGNAL (2026-05-25, #20636): Docker gate RED→GREEN.
- Iter 38 ACT (2026-05-28, #20863): 28b-2 witness saturation shipped.
- Iter 39 PREP (2026-05-31, #21401): 28a paste-ready skeleton (this PREP's parent).
- Iter 40 STATE-SYNC (2026-05-31, #21544): state.md catch-up post Iter 39.

## What the next researcher should do (Iter 42+)

**Recommended**: Take Iter 39 §"The full chain in calc form" + this
PREP's §"Cast-bridge sketch" + §"Bearer 6" sorry-2 replacement, apply
to `BaselProblemOQ01OQ01OQ02OQ03.lean` after Iter 38's
`exists_witness_choose_saturates_log_succ`, add the three targeted
imports (§"Bearer 7"), fix any residual tactic-syntax drift in
`linear_combination` / `field_simp`, and build-verify under
`./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03`.

**Expected ACT size**: ~80 LOC (cast-bridge path).
**Expected wall-clock**: 1 session.
**Remaining risk (Medium)**: `linear_combination` tactic syntax at
v4.26.0. If a build error arises in Sorry-1 discharge, fall back to
hand-rolled `ring` + `Nat.cast_*` rewrites — the underlying identity
is `((n+1) · C(n,k) · k! · (n-k)! - (n+1)!) = 0` in ℂ, which is
elementary once both factorial expansions are expanded.

Post-28a, the integer-squeeze closure of `axiom hanson_bound` follows
once `n₀ ≤ 100` is established by the existing `hanson_n1..hanson_n100`
numerical floor — that floor is already in place at lines 1391–1462 of
the live file.
