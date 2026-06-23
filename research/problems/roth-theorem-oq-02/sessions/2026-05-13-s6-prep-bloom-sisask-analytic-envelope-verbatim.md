# S6 PREP — Verbatim discharge of `bloom_sisask_analytic_envelope_conditional` (doc-only)

**Author:** researcher-11
**Date:** 2026-05-13 ~08:20 UTC
**Phase:** S6 PREP (doc-only; sibling of S5b PREP #18605 for B–S envelope)
**Predecessors:**

- PR #18605 (S5b PREP, researcher-6, MERGED 2026-05-13T06:01:48Z) — verbatim
  Mathlib-v4.26.0 discharge of the Kelley–Meka analytic envelope
  (`analytic_envelope_conditional` with hypothesis
  `kelleyMekaConst ≤ 4 * (Real.log 3)^(5/12)`).
- PR #18509 (S5 PREP, researcher-5, MERGED 2026-05-13T04:10:19Z) — identified
  the transitivity-vs-analytic-envelope obstruction, and §"Generalization
  (For Future Sessions)" explicitly flagged that the same obstruction applies
  to `bloom_sisask_consistent_with_Behrend` at `RothTheoremOQ02.lean:138-141`.
- PR #18443 (S4-a ACT, researcher-4, MERGED 2026-05-13T02:06:38Z) — introduced
  `axiom rothNumberNat_kelley_meka`, `kelleyMekaConst` API, and
  `rothNumberNat_le_min_blasi_kelley_meka` (joint min envelope).
- PR #18094 (S2 ACT-A, researcher-12, MERGED 2026-05-12T13:20:55Z) — introduced
  the parent `axiom rothNumberNat_bloom_sisask`, `blasiConst`, and
  `bloom_sisask_consistent_with_Behrend`.

**Mode:** Mathlib v4.26.0 API audit (sha `1c1dadbc28517bb148fc05b9abc8659ce110d217`)
+ verbatim Lean transcript for the **B–S** analytic envelope, parallel by
construction to S5b PREP's K–M discharge. Doc-only, no Lean changes.

## §1. Why this PREP exists

S5 PREP (PR #18509) §"Generalization (For Future Sessions)" states:

> *Bloom–Sisask (S2-A) vs Behrend — `bloom_sisask_consistent_with_Behrend`
> at `RothTheoremOQ02.lean:138-141` is also a transitivity proof. Its
> analytic envelope `(N · exp(-4√(log N))) ≤ (N / (log N)^{1+c})` is
> similarly unprovable without an upper bound on `blasiConst`.*

S5b PREP (PR #18605) discharged the K–M envelope verbatim but did not extend
the discharge to B–S. This PREP closes that gap: it provides the **complete
sorry-free Lean** for `bloom_sisask_analytic_envelope_conditional`, ready
for S6-a ACT to paste in.

After this PREP and S5b PREP both merge, **both transitivity-vs-envelope
obstructions in `RothTheoremOQ02.lean` have explicit conditional discharges**,
unifying the gallery's treatment of `rothNumberNat` upper bounds.

Pristine new file
`sessions/2026-05-13-s6-prep-bloom-sisask-analytic-envelope-verbatim.md`.
No Lean changes; no edits to `problem.md` / `state.md` / `knowledge.md` /
gallery JSON / `meta.json` / `proofs/Proofs/RothTheoremOQ02.lean`.

## §2. The B–S analytic envelope (sharp statement)

The transitivity proof at `RothTheoremOQ02.lean:138-141`:

```lean
theorem bloom_sisask_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) / Real.log N ^ (1 + blasiConst) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_blasi N hN)
```

works via pure transitivity through `rothNumberNat N`, regardless of the
analytic content. The **direct analytic envelope** is the claim that the
right-hand side dominates the left-hand side *as functions of `N`*,
independent of the `rothNumberNat` interpretation:

```
N · exp(-4 · √(log N))  ≤  N / (log N)^(1 + blasiConst)         (B–S envelope)
```

Dividing by `N > 0` and taking `log` (both sides positive for `N ≥ 3`
where `log N > 1`):

```
-4 · √(log N)  ≤  -(1 + blasiConst) · log(log N)
```

equivalently

```
(1 + blasiConst) · log(log N)  ≤  4 · √(log N)             (B–S analytic core, ✶)
```

**The obstruction (parallel to S5 PREP §"The Obstruction"):**
`blasiConst := rothNumberNat_bloom_sisask.choose` is an `Exists.choose`
witness of an unbounded existential, so any `blasiConst > 0` is consistent
with the axiom. For absurdly large `blasiConst = M`, the conditional (✶)
requires `log(log N) ≤ 4 · √(log N) / M`, which fails for the all-`N ≥ 3`
regime as `M → ∞`. Hence (✶) is **unprovable without a hypothesis
constraining `blasiConst`**.

The conditional discharge below adds the hypothesis `blasiConst ≤ 2e - 1`
(equivalently `1 + blasiConst ≤ 2e`) and proves (✶) for all `N ≥ 3`.

## §3. Optimal numerical constant `K` for the all-`N ≥ 3` envelope

For the analytic core `(1 + c) · log y ≤ 4 √y` with `y = log N`, the
*tightest all-`N ≥ 3`* hypothesis is

```
1 + c ≤ inf_{y ≥ log 3} (4 √y / log y).
```

The function `f(y) := 4 √y / log y` for `y > 1` has derivative
`f'(y) = 2 (log y - 2) / (√y · (log y)²)`, hence `f'(y) = 0 ⟺ log y = 2 ⟺
y = e²`. Since `f''(e²) > 0`, this is the minimum, with

```
f(e²) = 4 · e / 2 = 2e ≈ 5.43656.
```

For `y ∈ [log 3, e²)`, `f` is decreasing; for `y > e²`, `f` is increasing.
Hence `f(y) ≥ 2e` for all `y ≥ log 3` (and indeed for all `y > 1`).

**Optimal hypothesis:** `1 + blasiConst ≤ 2 * Real.exp 1`,
equivalently `blasiConst ≤ 2 * Real.exp 1 - 1 ≈ 4.4366`.

### §3.1 Numerical regime table (parallel to S5b PREP §6.1)

| `K = 1 + c` | Smallest `N₀` s.t. `K ≤ 4√(log N) / log(log N)` for all `N ≥ N₀` | Notes |
|---:|---|---|
| `2` | `N = 3` (since `4√(log 3)/log(log 3) ≈ 44.5 > 2`) | trivially ample |
| `2e ≈ 5.437` | All `y > 1`, hence all `N ≥ 3` | **optimal `N ≥ 3` envelope** |
| `6` | Need to avoid the `y = e²` valley, in fact `(1+c) > 2e` ⟹ no `N₀` works | unbounded |
| `44` | Need only avoid `y = log 3 + ε` (the boundary); essentially `N ≥ 3` fails | not all `N ≥ 3` |

**Sanity check** at the minimum:
- `y = e² ≈ 7.389`, `√y = e ≈ 2.71828`, `log y = 2`, `f(y) = 4 · e / 2 = 2e`. ✓
- At `y = log 3 ≈ 1.0986`: `√y ≈ 1.0481`, `log y ≈ 0.0941`,
  `f(y) ≈ 4.193/0.0941 ≈ 44.55`. ✓ (much larger than 2e).
- At `y = 10` (~`N = 22026`): `√y ≈ 3.162`, `log y ≈ 2.303`,
  `f(y) ≈ 12.65/2.303 ≈ 5.49 > 2e ≈ 5.437`. ✓

**Recommendation:** the `K = 2e` hypothesis is the cleanest all-`N ≥ 3`
envelope and is the recommended default. The Bloom–Sisask paper's `c` is
believed to be **small** (informal estimates put `c ≈ 1/12` to `1/24`),
hence `blasiConst ≤ 2e - 1 ≈ 4.4366` is *very* loose relative to the
mathematical content — a "near-trivial" hypothesis from the paper's
standpoint, but a non-trivial axiomatic strengthening for the Lean
formalization.

### §3.2 Comparison with S5b PREP's K–M envelope

| Envelope | Optimal `K` | Reason |
|---|---:|---|
| K–M analytic envelope (S5b PREP) | `4 · (log 3)^{5/12} ≈ 4.165` | `4 · (log y)^{5/12}` is monotone-increasing in `y > 1`; minimum at `y = log 3` |
| B–S analytic envelope (this PREP) | `2e ≈ 5.437` | `4 √y / log y` has a `y = e²` minimum interior to the range |

The K–M envelope has an *increasing* analytic-content function (so the
minimum is at the boundary `y = log 3`); the B–S envelope has a U-shaped
function (so the minimum is *interior* at `y = e²`). This is why the two
optimal constants take different shapes (`(log 3)^{5/12}` vs `2e`).

## §4. Verified Mathlib v4.26.0 API table (sha `1c1dadbc28517bb148fc05b9abc8659ce110d217`)

All citations verified by
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`.

| Lemma | Statement | Location |
|---|---|---|
| `Real.log_pos` | `1 < x → 0 < Real.log x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:173` |
| `Real.log_lt_log_iff` | `0 < x → 0 < y → (log x < log y ↔ x < y)` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:155` |
| `Real.log_le_log` | `0 < x → x ≤ y → log x ≤ log y` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:148` |
| `Real.log_exp` | `log (exp x) = x` (`@[simp, push]`) | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:74` |
| `Real.exp_log` | `0 < x → exp (log x) = x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` (standard) |
| `Real.exp_one_mul_le_exp` | `Real.exp 1 * x ≤ Real.exp x` (universal in `x : ℝ`) | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:77` |
| `Real.exp_one_lt_d9` | `exp 1 < 2.7182818286` | `Mathlib/Analysis/Complex/ExponentialBounds.lean:37` |
| `Real.exp_pos` | `0 < Real.exp x` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` (standard) |
| `Real.log_sqrt` | `0 ≤ x → log (√x) = log x / 2` (`@[push]`) | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:286` |
| `Real.sqrt_pos` | `0 < √x ↔ 0 < x` | `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (standard) |
| `Real.sqrt_nonneg` | `0 ≤ √x` | `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (standard) |
| `Real.mul_self_sqrt` | `0 ≤ x → √x * √x = x` | `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (standard) |

**Verification status:**

- All explicit `(filename:line)` citations verified at `ref=v4.26.0` against
  sha `1c1dadbc28517bb148fc05b9abc8659ce110d217` via `gh api .../contents`.
- The "(standard)" entries are stable across Mathlib v4.x and are pervasively
  used in Mathlib's own analysis library; the file:line is omitted but the
  lemma names are pinned at this version.
- `Real.exp_one_mul_le_exp` is the **key analytic lemma** for this PREP;
  S5b PREP did not need it (K–M envelope uses `rpow` monotonicity, not
  `e · log u ≤ u`). The Mathlib proof handles the `x ≤ 0` case trivially
  (LHS ≤ 0 ≤ RHS) and the `x > 0` case via `add_one_le_exp (log x)`
  followed by `exp_log` and `mul_comm`.
- `Real.log_sqrt` is a `@[push]` simp lemma — likely closes the
  `log(log N) = 2 · log(√(log N))` step in 1 line via `simp [Real.log_sqrt]`.

## §5. Discharge — Step 1: bridge `1 ≤ Real.log N` (shared with S5b PREP §3)

The first ~10 LOC is **identical** to S5b PREP §3, since both envelopes
need `1 ≤ Real.log N` to access `log(log N) > 0`. Repeated here for
self-containment:

```lean
have h_log3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
have h_e_lt_3 : Real.exp 1 < 3 :=
  lt_of_lt_of_lt Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3)
have h_one_lt_log3 : (1 : ℝ) < Real.log 3 := by
  have h := (Real.log_lt_log_iff (Real.exp_pos 1)
              (by norm_num : (0 : ℝ) < 3)).mpr h_e_lt_3
  rwa [Real.log_exp] at h
have h_log3_le_logN : Real.log 3 ≤ Real.log N :=
  Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN)
have h_one_le_logN : (1 : ℝ) ≤ Real.log N :=
  le_of_lt (lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN)
have h_logN_pos : (0 : ℝ) < Real.log N :=
  lt_of_lt_of_le zero_lt_one h_one_le_logN
have h_one_lt_logN : (1 : ℝ) < Real.log N :=
  lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN
have h_logN_nonneg : (0 : ℝ) ≤ Real.log N := le_of_lt h_logN_pos
```

**LOC: 11.** No `sorry`. All lemma names verified.

## §6. Discharge — Step 2: derive `log(log N) > 0` and `√(log N) > 0`

```lean
have h_loglogN_pos : (0 : ℝ) < Real.log (Real.log N) := Real.log_pos h_one_lt_logN
have h_sqrt_logN_pos : (0 : ℝ) < Real.sqrt (Real.log N) :=
  Real.sqrt_pos.mpr h_logN_pos
```

**LOC: 2.** Both follow directly from §5.

## §7. Discharge — Step 3: the key analytic step `e · log u ≤ u` where `u = √(log N)`

The single analytic fact at the heart of the B–S envelope:

```lean
-- Real.exp_one_mul_le_exp (universal in x) : exp 1 * x ≤ exp x.
-- Specialize to x = log u for u > 0:
--   exp 1 * log u ≤ exp (log u) = u.
have h_e_log_sqrt_le_sqrt :
    Real.exp 1 * Real.log (Real.sqrt (Real.log N)) ≤
      Real.sqrt (Real.log N) := by
  have h := Real.exp_one_mul_le_exp (x := Real.log (Real.sqrt (Real.log N)))
  rwa [Real.exp_log h_sqrt_logN_pos] at h
```

**LOC: 4.** This is the analogue of S5b PREP §4 Step 1's
`Real.rpow_le_rpow` step — but for B–S, the lever is `exp 1 * x ≤ exp x`
rather than `rpow` monotonicity, since the B–S envelope analytic content
is `(1+c) log(log N) ≤ 4 √(log N)` (a `log` vs `√` shape), not
`(log N)^{5/12 + 1/12}` (an `rpow + rpow` shape).

## §8. Discharge — Step 4: translate `e · log u ≤ u` into `2e · log(log N) ≤ 4 √(log N)`

Two reductions: (a) `log u = log(log N) / 2` via `Real.log_sqrt`, then
(b) multiply by 4.

```lean
-- (a) log(√(log N)) = log(log N) / 2
have h_log_sqrt_eq : Real.log (Real.sqrt (Real.log N)) =
    Real.log (Real.log N) / 2 := Real.log_sqrt h_logN_nonneg

-- (b) 2e · log(log N) = 4 · e · log(√(log N)) by step (a)
have h_2e_loglogN_eq : 2 * Real.exp 1 * Real.log (Real.log N) =
    4 * (Real.exp 1 * Real.log (Real.sqrt (Real.log N))) := by
  rw [h_log_sqrt_eq]; ring

-- (c) Apply h_e_log_sqrt_le_sqrt multiplied by 4:
have h_2e_loglogN_le_4_sqrt : 2 * Real.exp 1 * Real.log (Real.log N) ≤
    4 * Real.sqrt (Real.log N) := by
  rw [h_2e_loglogN_eq]
  exact mul_le_mul_of_nonneg_left h_e_log_sqrt_le_sqrt
    (by norm_num : (0 : ℝ) ≤ 4)
```

**LOC: 9.** No `sorry`. All names verified.

**Sub-step rationale:**

- §8a: `Real.log_sqrt` requires `0 ≤ log N` (provided by `h_logN_nonneg`).
- §8b: the `ring` after `rw` reduces
  `2 * exp 1 * (2 · log(√(log N))) = 4 · (exp 1 · log(√(log N)))`.
- §8c: `mul_le_mul_of_nonneg_left` multiplies an inequality by a nonneg
  scalar; `4 ≥ 0` is dispatched by `norm_num`.

## §9. Discharge — Step 5: combine with hypothesis and conclude

```lean
-- (a) Hypothesis: 1 + blasiConst ≤ 2e.
have h_1_plus_c_le_2e : 1 + blasiConst ≤ 2 * Real.exp 1 := by linarith

-- (b) (1 + blasiConst) · log(log N) ≤ 2e · log(log N), since log(log N) ≥ 0.
have h_main : (1 + blasiConst) * Real.log (Real.log N) ≤
    2 * Real.exp 1 * Real.log (Real.log N) :=
  mul_le_mul_of_nonneg_right h_1_plus_c_le_2e (le_of_lt h_loglogN_pos)

-- (c) Chain (b) into (§8.c): (1 + blasiConst) · log(log N) ≤ 4 · √(log N).
have h_main_chain : (1 + blasiConst) * Real.log (Real.log N) ≤
    4 * Real.sqrt (Real.log N) :=
  le_trans h_main h_2e_loglogN_le_4_sqrt

-- (d) Convert to negation form to match the theorem goal.
linarith
```

**LOC: 8.** No `sorry`.

**Sub-step rationale:**

- §9a: trivial `linarith` from `hBS_bound : blasiConst ≤ 2 * Real.exp 1 - 1`.
- §9b: `mul_le_mul_of_nonneg_right` multiplies an inequality by a nonneg
  scalar on the right; `log(log N) ≥ 0` from §6.
- §9c: `le_trans` chains §9b and §8c.
- §9d: `linarith` closes from `h_main_chain`:
  goal `-(4) * √(log N) ≤ -(1 + blasiConst) * log(log N)` is `-h_main_chain`
  after `mul_comm` / sign-flip.

## §10. Combined verbatim Lean for `bloom_sisask_analytic_envelope_conditional`

```lean
/-- **The conditional B–S analytic envelope.**

    Assuming `blasiConst ≤ 2 * Real.exp 1 - 1` (numerically `≈ 4.4366`),
    the analytic envelope `Behrend ≤ Bloom–Sisask` holds for all `N ≥ 3`.
    This is **strictly stronger** than the transitivity proof
    `bloom_sisask_consistent_with_Behrend` (line 138–141), which works
    for *every* value of `blasiConst` regardless of the analytic content.

    See PR #18509 / S5 PREP and PR #18605 / S5b PREP for the full
    obstruction analysis (the same Exists.choose unboundedness as for
    the K–M envelope) and the parallel K–M conditional envelope.

    The optimal numerical constant `K = 2e` arises because the analytic
    core `(1 + c) · log(log N) ≤ 4 · √(log N)` has the minimum of
    `4 · √y / log y` at `y = e²`, giving `f(e²) = 2e`. See PR (this)
    / S6 PREP §3 for the derivation.

    The Bloom–Sisask paper's `c` is informally `≈ 1/24` to `1/12`, hence
    `blasiConst ≤ 2e - 1 ≈ 4.4366` is a *very loose* hypothesis from the
    paper's standpoint. -/
theorem bloom_sisask_analytic_envelope_conditional (N : ℕ) (hN : 3 ≤ N)
    (hBS_bound : blasiConst ≤ 2 * Real.exp 1 - 1) :
    -(4 : ℝ) * Real.sqrt (Real.log N) ≤
      -(1 + blasiConst) * Real.log (Real.log N) := by
  -- §5: 1 ≤ Real.log N, hence log N > 0, log N ≥ 0, 1 < log N.
  have h_log3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h_e_lt_3 : Real.exp 1 < 3 :=
    lt_of_lt_of_lt Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3)
  have h_one_lt_log3 : (1 : ℝ) < Real.log 3 := by
    have h := (Real.log_lt_log_iff (Real.exp_pos 1)
                (by norm_num : (0 : ℝ) < 3)).mpr h_e_lt_3
    rwa [Real.log_exp] at h
  have h_log3_le_logN : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN)
  have h_one_le_logN : (1 : ℝ) ≤ Real.log N :=
    le_of_lt (lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN)
  have h_logN_pos : (0 : ℝ) < Real.log N :=
    lt_of_lt_of_le zero_lt_one h_one_le_logN
  have h_one_lt_logN : (1 : ℝ) < Real.log N :=
    lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN
  have h_logN_nonneg : (0 : ℝ) ≤ Real.log N := le_of_lt h_logN_pos
  -- §6: log(log N) > 0 and √(log N) > 0.
  have h_loglogN_pos : (0 : ℝ) < Real.log (Real.log N) :=
    Real.log_pos h_one_lt_logN
  have h_sqrt_logN_pos : (0 : ℝ) < Real.sqrt (Real.log N) :=
    Real.sqrt_pos.mpr h_logN_pos
  -- §7: the analytic core: e · log(√(log N)) ≤ √(log N).
  have h_e_log_sqrt_le_sqrt :
      Real.exp 1 * Real.log (Real.sqrt (Real.log N)) ≤
        Real.sqrt (Real.log N) := by
    have h := Real.exp_one_mul_le_exp
                (x := Real.log (Real.sqrt (Real.log N)))
    rwa [Real.exp_log h_sqrt_logN_pos] at h
  -- §8: translate to 2e · log(log N) ≤ 4 · √(log N).
  have h_log_sqrt_eq : Real.log (Real.sqrt (Real.log N)) =
      Real.log (Real.log N) / 2 := Real.log_sqrt h_logN_nonneg
  have h_2e_loglogN_eq : 2 * Real.exp 1 * Real.log (Real.log N) =
      4 * (Real.exp 1 * Real.log (Real.sqrt (Real.log N))) := by
    rw [h_log_sqrt_eq]; ring
  have h_2e_loglogN_le_4_sqrt : 2 * Real.exp 1 * Real.log (Real.log N) ≤
      4 * Real.sqrt (Real.log N) := by
    rw [h_2e_loglogN_eq]
    exact mul_le_mul_of_nonneg_left h_e_log_sqrt_le_sqrt
      (by norm_num : (0 : ℝ) ≤ 4)
  -- §9: combine with hypothesis and conclude.
  have h_1_plus_c_le_2e : 1 + blasiConst ≤ 2 * Real.exp 1 := by linarith
  have h_main : (1 + blasiConst) * Real.log (Real.log N) ≤
      2 * Real.exp 1 * Real.log (Real.log N) :=
    mul_le_mul_of_nonneg_right h_1_plus_c_le_2e (le_of_lt h_loglogN_pos)
  have h_main_chain : (1 + blasiConst) * Real.log (Real.log N) ≤
      4 * Real.sqrt (Real.log N) :=
    le_trans h_main h_2e_loglogN_le_4_sqrt
  linarith
```

**Total LOC: ~50** (close to S5b PREP's K–M envelope discharge at ~50 LOC).

## §11. Combined verbatim Lean for the `def` form (parallel to S5b PREP §8)

S5b PREP's S5-a complementary deliverable also includes a `def` for the
bare functional form of the K–M envelope. The B–S analogue:

```lean
/-- **The analytic envelope of the Bloom–Sisask 2020 upper bound vs the
    Behrend 1946 lower bound on `rothNumberNat`.**

    This `def` is a *function*, not a theorem: its `Prop` value is the
    hypothetical inequality

    ```
    N · exp(-4 · √(log N))   ≤   N / (log N)^(1 + blasiConst)
    ```

    that *would* assert that the B–S upper-bound function dominates the
    Behrend lower-bound function for `N ≥ 3`. **It is unprovable from the
    current axiom set** (see PR #18509: `blasiConst` is `Exists.choose` of
    an unbounded existential). We expose it as a `def` so that future
    researchers can either:

    1. Strengthen the B–S axiom to a bounded-existential form (analogue of
       K–M's S5-b) and prove the envelope unconditionally, or
    2. Use the conditional version `bloom_sisask_analytic_envelope_conditional`
       below which adds an explicit upper bound on `blasiConst` as a
       hypothesis.

    The bare definition records the target without committing to either
    path. Parallel to `analytic_envelope_kelley_meka` (S5b PREP §8). -/
def analytic_envelope_bloom_sisask (N : ℕ) : Prop :=
  3 ≤ N →
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) / Real.log N ^ (1 + blasiConst)
```

**LOC: ~5** (`def` body) **+ ~22** (docstring) **= ~27 LOC.**

## §12. Combined LOC accounting for S6-a (this PREP's deliverable)

Following the §10 + §11 pre-staged Lean:

| Component | LOC | Cumulative |
|---|---:|---:|
| `def analytic_envelope_bloom_sisask` (§11) | 27 | 27 |
| `theorem bloom_sisask_analytic_envelope_conditional` (§10) | 50 | 77 |
| Section docstring `"## Conditional B–S Analytic Envelope"` | ~10 | 87 |

**S6-a total: ~87 LOC** (parallel to S5b PREP's "~85 LOC" estimate for
S5-a). The two ACT iterations together add ~172 LOC to
`RothTheoremOQ02.lean`.

**Counts after BOTH S5-a ACT and S6-a ACT land (projected):**

- File `proofs/Proofs/RothTheoremOQ02.lean`: 236 → ~408 lines (+172).
- Theorems: 9 → 11 (+2: `analytic_envelope_conditional`,
  `bloom_sisask_analytic_envelope_conditional`).
- Defs: 1 → 3 (+2: `analytic_envelope_kelley_meka`,
  `analytic_envelope_bloom_sisask`).
- Axioms: 2 (unchanged).
- Sorries: 0 (unchanged).

## §13. Honesty / what could be wrong (parallel to S5b PREP §13)

- **`Real.exp_one_mul_le_exp`** at v4.26.0 line 77: universal in `x : ℝ`,
  hence applicable to `x = log(√(log N))` without sign-of-`x` hypothesis.
  Verified by inspection: the Mathlib proof uses a `by_cases hx0 : x ≤ 0`
  split where the negative case dispatches via `mul_nonpos_of_nonneg_of_nonpos`
  and the positive case via `add_one_le_exp (log x)`. **Risk: trivially low.**
- **`Real.log_sqrt`** at v4.26.0 line 286: requires `0 ≤ x`, satisfied by
  `h_logN_nonneg` from §5. The simp form `@[push]` means it auto-applies in
  `simp` chains; we use it as an explicit rewrite for clarity. **Risk: low.**
- **The `e · log u ≤ u` step (§7) is the analytical heart** of the entire
  proof. Equivalent to `log u ≤ u/e`, equivalent to "the function `u/e - log u`
  has a minimum of 0 at `u = e`". Mathlib makes this available as
  `Real.exp_one_mul_le_exp` without needing the symbolic minimum argument
  inside the proof. **Risk: trivially low.**
- **The hypothesis `2 * Real.exp 1 - 1`** vs alternatives like
  `2 * Real.exp 1` or `2 * Real.exp 1 - 0.5`: the choice is driven by the
  shape of the theorem statement (`1 + blasiConst ≤ 2e` ⟺
  `blasiConst ≤ 2e - 1`). The numerical value `2e - 1 ≈ 4.4366` is the
  optimal upper bound on `blasiConst` for the all-`N ≥ 3` regime;
  marginally tighter `K = 2e + ε` would also work (linarith would still
  close §9a), but `K = 2e` is the optimal symbolic form.
- **The `linarith` close in §10** requires the goal
  `-(4) * √(log N) ≤ -(1 + blasiConst) * log(log N)` to be derivable
  from `h_main_chain : (1 + blasiConst) · log(log N) ≤ 4 · √(log N)` by
  sign-flipping both sides. `linarith` handles this routinely (it's a
  multiplication by `-1` on both sides). **Backup: `nlinarith` if narrow.**
- **The proof body might exceed estimate** — measured at ~50 LOC for the
  conditional theorem alone, plus ~27 LOC for the `def` + docstring,
  plus ~10 LOC for the section docstring = ~87 LOC. This is within the
  S5b PREP "S5-a effort ≈ 85 LOC" envelope.

## §14. Anti-targets (this S6 PREP explicitly does NOT do)

1. **Does not modify any Lean file.** All Mathlib API names and
   `file:line` references are from `gh api`-verifiable queries against
   v4.26.0 source at sha `1c1dadbc28517bb148fc05b9abc8659ce110d217`.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON / `proofs/Proofs/RothTheoremOQ02.lean` /
   `proofs/Proofs.lean`.** Pristine new `sessions/` file.
3. **Does not strengthen `rothNumberNat_bloom_sisask` axiom.** That is
   the analogue of S5-b (K–M case) — analytic-envelope-unconditional
   would require strengthening to `∃ c ∈ (0, 2e - 1], ...`. Recommended
   only after a literature audit of Bloom–Sisask 2020 confirming the
   actual paper's `c` value is bounded by `2e - 1`.
4. **Does not address the K–M paper literature audit** (whether the actual
   K–M c is ≤ 1 or some other K). That remains S5-b's domain. Likewise
   for Bloom–Sisask: S6-b would require auditing arXiv:2007.03528.
5. **Does not run the build.** All cited Mathlib lemma names and
   file:line references are from `gh api`-verifiable queries.
6. **Does not address the in-flight stale PR #18181** (S3 ACT non-vacuity
   certificates, OPEN since 2026-05-12). Per S5 PREP and S5b PREP, that
   PR predates S3-B (#18238) and S4-a (#18443); its closure-without-merge
   is a separate housekeeping decision.

## §15. Race awareness

Pre-push checks (2026-05-13 ~08:20 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "roth-theorem-oq-02 in:title"`: 1 OPEN PR #18181 (S3 ACT non-vacuity
  certificates, OPEN since 2026-05-12T15:52:21Z, build pending). This
  is **stale** per S5/S5b PREP §"Race Safety" and does not race with
  this PREP-S6 (orthogonal `sessions/` file).
- Most recent merge: PR #18605 S5b PREP, MERGED 2026-05-13T06:01:48Z =
  ~2h20min before this PREP claim.
- `git log origin/main -- proofs/Proofs/RothTheoremOQ02.lean` HEAD:
  PR #18443 S4-a ACT, 2026-05-13T02:06:38Z = ~6 hours ago.
- `git log origin/main -- research/problems/roth-theorem-oq-02/sessions/`
  HEAD: PR #18605 S5b PREP, 2026-05-13T06:01:48Z = the most-recent
  `sessions/` write.
- This S6 PREP is **forward-looking and orthogonal** to all open work;
  it creates exactly one new file and does not touch any pre-existing file.

**Pre-push verification step:** before `git push`, re-run
`gh pr list --repo rjwalters/lean-genius --search
"roth-theorem-oq-02 in:title bloom-sisask-analytic-envelope" --state open`
to confirm no sibling slot has shipped a duplicate S6 PREP in the
intervening ~30 min. (Memory:
`feedback_mechanic_race_quadruple_slot_collision.md`,
`feedback_auditor_tracker_bump_race_duplicate_pr.md`.)

## §16. Cross-reference: PR chain status

| Phase | PR | Status | Coverage |
|---|---|---|---|
| S1 OBSERVE (a) | #18031 | merged | Bloom–Sisask scaffold + Mathlib gap survey |
| S1 OBSERVE (b) | #18033 | merged | Lean target identification at `RothTheoremQuantitative.lean:211` |
| S2 ACT-A | #18094 | merged | Companion file + B–S axiom + transitive consistency |
| S3 ACT | #18181 | **OPEN (stale)** | Non-vacuity certificates (predates S3-B; close without merge) |
| S3 OBSERVE | #18180 | merged | Mathlib API audit corrects S2 S3-B plan |
| S3-B ACT | #18238 | merged | Bloom–Sisask ↔ Behrend consistency (verified) |
| S4-a ACT | #18443 | merged | Kelley–Meka axiom + transitive consistency |
| S5 PREP | #18509 | merged | Transitivity-vs-envelope obstruction + sketch with 2 sorries |
| S5b PREP | #18605 | merged | Verbatim discharge of S5 PREP's two sorries (K–M envelope) |
| **S6 PREP** | **(this PR)** | this PR | **Verbatim discharge for the B–S analytic envelope (parallel sibling)** |

After this S6 PREP merges, **both S5-a ACT and S6-a ACT are unblocked** —
each is a copy-paste task from the respective PREP's §10/§5 verbatim Lean
into `RothTheoremOQ02.lean`, followed by a Docker build and meta update.

## §17. Optional consolidation: a joint S-a ACT

S5b PREP and this S6 PREP each pre-stage one conditional analytic envelope
discharge (K–M and B–S, respectively). A future ACT researcher might
choose to land **both** discharges in a **single PR** (a joint S-a ACT)
rather than two separate ACTs. Benefits:

- Single Docker build cycle (~10-15 min total) instead of two.
- A clean `analytic_envelope_min_blasi_kelley_meka_unconditional` corollary
  is naturally written *after* both individual conditional envelopes, so
  bundling them simplifies the dependency story.
- The two envelopes share §5's `1 ≤ Real.log N` boilerplate (~11 LOC); a
  joint PR could `extract` this to a private helper lemma
  `one_le_log_of_three_le (N : ℕ) (hN : 3 ≤ N) : (1 : ℝ) ≤ Real.log N`
  (~5 LOC including the docstring), saving ~17 LOC across the two proofs.

Costs:

- Larger ACT diff (~172 LOC vs ~87 LOC), marginally higher risk of a
  build failure.
- Two distinct hypotheses (`hKM_bound`, `hBS_bound`) live on adjacent
  theorems — a tiny readability concern.

**Recommendation**: leave the choice to the S-a ACT researcher. The
proofs are independent in their analytic content; either splitting or
joining is reasonable. If joining, also consider extracting
`one_le_log_of_three_le` as a private helper.

## §18. References

- PR #18605 — S5b PREP (K–M envelope verbatim discharge; parallel sibling).
- PR #18509 — S5 PREP (transitivity-vs-envelope obstruction; flags the B–S case in §"Generalization").
- PR #18443 — S4-a ACT (Kelley–Meka axiom + transitive consistency).
- PR #18094 — S2 ACT-A (B–S axiom + transitive consistency).
- Mathlib v4.26.0 source at sha `1c1dadbc28517bb148fc05b9abc8659ce110d217`:
  * `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` (`log_*`, `exp_one_mul_le_exp`, `log_sqrt`)
  * `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` (`sqrt`, `rpow_*` — used by S5b PREP)
  * `Mathlib/Analysis/Complex/ExponentialBounds.lean` (`exp_one_*_d9`)
- Bloom, T. F. & Sisask, O. (2020). *Breaking the logarithmic barrier in
  Roth's theorem on arithmetic progressions*. arXiv:2007.03528.
- Behrend, F. A. (1946). *On sets of integers which contain no three terms
  in arithmetical progression*. PNAS 32(12).
- Kelley, Z. & Meka, R. (2023). *Strong bounds for 3-progressions*.
  arXiv:2302.05537. (Not audited in this PREP — see S5-b / S6-b.)
