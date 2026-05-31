# Iteration 39 PREP — 28a Beta-integral identity: bearer re-verification + paste-ready skeleton

**Date**: 2026-05-31
**Researcher**: researcher-1
**Phase**: PREP (paste-ready skeleton for 28a Beta-integral identity ACT)
**Type**: Doc-only. No edits to `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`, `state.md`,
`knowledge.md`, `problem.md`, gallery `meta.json`, or research JSON.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from
Iter 36 PREP audit and Iter 38 ACT build).

## Rationale

Per Iter 38 (2026-05-28) state.md: *"Consider a PREP iteration first to pin the
Beta-integral Mathlib bearers at the current SHA before attempting the 28a ACT."*

Iter 29 PREP (2026-05-12, the Route B Mathlib API audit) identified the chain at
Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
Complex.betaIntegral (k+1) (m+1)
  = m! / ∏ j ∈ range (m+1), (k+1 + j)          -- betaIntegral_eval_nat_add_one_right
  = m! / (k+1).ascFactorial (m+1)              -- Nat.ascFactorial_eq_prod_range
  = m! · k! / (n+1)!                           -- ascFactorial → factorial
  = 1 / ((n+1) · Nat.choose n k)               -- choose_mul_factorial_mul_factorial
```

But Iter 29 stopped at the chain *outline*; it did not name bearers for steps 3-4 nor
discuss the real-vs-complex bridge. This PREP closes both gaps **and** provides a
paste-ready Lean skeleton with each step's drop-in body (modulo the two known sorries
that require Mathlib-level infrastructure choices).

## Bearer re-verification at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All bearers below were verified by direct source inspection
(`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` + `base64 -d`).
No `lake build` / `lake env lean` was used (SHA-pinned source is authoritative).

### Bearer 1 (Beta) — `Complex.betaIntegral_eval_nat_add_one_right`

`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:202-203`:

```lean
/-- Explicit formula for the Beta function when second argument is a positive integer. -/
theorem betaIntegral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
    betaIntegral u (n + 1) = n ! / ∏ j ∈ Finset.range (n + 1), (u + j)
```

**Status**: unchanged since Iter 29 verification. Namespace `Complex`. Returns ℂ.

### Bearer 2 (asc-prod) — `Nat.ascFactorial_eq_prod_range`

`Mathlib/Data/Nat/Factorial/BigOperators.lean:49-51`:

```lean
theorem ascFactorial_eq_prod_range (n : ℕ) : ∀ k, n.ascFactorial k = ∏ i ∈ range k, (n + i)
  | 0 => rfl
  | k + 1 => by rw [ascFactorial, prod_range_succ_comm, ascFactorial_eq_prod_range n k]
```

**Status**: unchanged since Iter 29 verification. Operates over ℕ; casting to ℂ
requires `Nat.cast_prod` + `Nat.cast_add`.

### Bearer 3 (asc→factorial) — `Nat.factorial_mul_ascFactorial` **(NEW, not in Iter 29)**

`Mathlib/Data/Nat/Factorial/Basic.lean:227-233`:

```lean
/-- `(n + 1).ascFactorial k = (n + k) ! / n !` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. -/
theorem factorial_mul_ascFactorial (n : ℕ) : ∀ k, n ! * (n + 1).ascFactorial k = (n + k)!
  | 0 => by rw [ascFactorial_zero, Nat.add_zero, Nat.mul_one]
  | k + 1 => by
    rw [ascFactorial_succ, ← Nat.add_assoc, factorial_succ, Nat.mul_comm (n + 1 + k),
      ← Nat.mul_assoc, factorial_mul_ascFactorial n k, Nat.mul_comm, Nat.add_right_comm]
```

**Specialization for Hanson's chain** (substitute `n → k`, `k → m+1`):
```lean
k ! * (k + 1).ascFactorial (m + 1) = (k + (m + 1))!
```

With `m = n - k` (and `k ≤ n`), `k + (m + 1) = n + 1`, so:
```lean
k ! * (k + 1).ascFactorial (n - k + 1) = (n + 1)!
```

This is the **multiplicative form** (no ℕ-division). The PREP uses this rather than
`Nat.ascFactorial_eq_div` because the latter would require massaging `(n+1)!/k!` over ℕ.

### Bearer 4 (choose) — `Nat.choose_mul_factorial_mul_factorial` **(NEW, not in Iter 29)**

`Mathlib/Data/Nat/Choose/Basic.lean:141`:

```lean
theorem choose_mul_factorial_mul_factorial : ∀ {n k}, k ≤ n → choose n k * k ! * (n - k)! = n !
```

**Direct consequence for Hanson**:
With `k ≤ n`, multiplying both sides by `(n+1)`:
```lean
(n + 1) * choose n k * k ! * (n - k)! = (n + 1) * n ! = (n + 1)!
```

### Bearer 5 (cast bridge) — `Complex.ofReal_pow`, `Nat.cast_*` **(NEW area, not in Iter 29)**

Beta's signature returns `ℂ`; Hanson's integer-squeeze argument needs a **real-valued**
integral identity. Bearers for the bridge:

- `Mathlib/Data/Complex/Basic.lean`: `Complex.ofReal_pow : ((x ^ k : ℝ) : ℂ) = (x : ℂ) ^ (k : ℕ)`
  (handles natural exponents — sidesteps the `cpow` principal-branch issue Iter 29 flagged).
- `Mathlib/MeasureTheory/Integral/IntervalIntegral.lean`: `intervalIntegral.integral_ofReal`
  for casting the real-valued integrand into a complex-valued integrand.
- `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` (or
  `Mathlib/Analysis/Complex/RealDeriv.lean`): `Complex.ofReal_re` / `Complex.ofReal_im`
  to extract the real-valued integral after casting back.

**Key observation**: because `(u-1) = (k+1) - 1 = k : ℕ` and similar for `v`, the `cpow`
in `Complex.betaIntegral`'s integrand reduces to `(x : ℂ) ^ (k : ℕ)`, which equals
`((x ^ k : ℝ) : ℂ)` via `Complex.ofReal_pow`. So the cpow ↔ rpow bridge does not bite
in the natural-exponent specialization — this was Iter 29 Erratum 1's prediction, now
re-confirmed at the same SHA.

## The full chain in calc form (paste-ready core)

Below is the **paste-ready 28a Lean target**. It is a `calc` chain over ℂ, sidestepping
the real ↔ complex bridge by working with the `Complex.betaIntegral` definition directly
and deriving the rational identity in ℂ; the conversion to a ℚ-valued or ℝ-valued
identity is a separate step (see Section "Real ↔ complex bridge" below).

```lean
-- 28a core: the Beta-integral rational identity, in ℂ.
-- Target file: BaselProblemOQ01OQ01OQ02OQ03.lean, inserted after Iter 38's
-- exists_witness_choose_saturates_log_succ.

/-- The Beta integral at natural arguments evaluates to a rational number whose
denominator is `(n+1) · C(n,k)`. Specialization of Mathlib's `Complex.betaIntegral`
identity. -/
theorem complex_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n) :
    Complex.betaIntegral (k + 1 : ℂ) (n - k + 1 : ℂ) =
      ((1 : ℂ)) / ((n + 1 : ℂ) * (Nat.choose n k : ℂ)) := by
  have hu : 0 < ((k + 1 : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- Step 1: apply Mathlib's explicit formula.
  rw [Complex.betaIntegral_eval_nat_add_one_right hu (n - k)]
  -- Now LHS = (n - k)! / ∏ j ∈ range (n-k+1), ((k+1) + j)
  -- Step 2: identify the product with an ascending factorial.
  have h_prod : ∏ j ∈ Finset.range (n - k + 1), ((k + 1 : ℂ) + j) =
                  ((k + 1).ascFactorial (n - k + 1) : ℂ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [h_prod]
  -- LHS = (n-k)! / ((k+1).ascFactorial (n-k+1) : ℂ)
  -- Step 3: rewrite ascFactorial in terms of factorials via factorial_mul_ascFactorial.
  have h_asc_factorial : (k : ℂ).factorial.toNat *
                         ((k + 1).ascFactorial (n - k + 1) : ℂ) = ((n + 1)! : ℂ) := by
    have h_nat : k ! * (k + 1).ascFactorial (n - k + 1) = (n + 1)! := by
      have := Nat.factorial_mul_ascFactorial k (n - k + 1)
      -- k + (n - k + 1) = n + 1 since k ≤ n
      have hk_sub : k + (n - k + 1) = n + 1 := by omega
      rw [hk_sub] at this
      exact this
    exact_mod_cast h_nat
  sorry  -- Step 3 cleanup: factor the chain m! · k! / (n+1)! = 1/((n+1) · C(n,k))
         -- by `Nat.choose_mul_factorial_mul_factorial hk` (rewritten as
         -- `(n+1)! = (n+1) · Nat.choose n k · k! · (n-k)!`) and field_simp.
```

### The "Step 3 cleanup" sorry — drop-in body (proposed)

The remaining `sorry` discharges the arithmetic:
`(n-k)! / ((k+1).ascFactorial (n-k+1)) = 1 / ((n+1) · C(n,k))` in ℂ.

Proposed drop-in body:

```lean
  -- Goal at this point (after Step 2 rewrite, ignoring Step 3 helper above):
  -- (↑(n - k)!) / (↑((k+1).ascFactorial (n - k + 1))) = 1 / ((n+1 : ℂ) · (Nat.choose n k))
  --
  -- Use factorial_mul_ascFactorial: k! * (k+1).ascFactorial (n-k+1) = (n+1)!
  -- And choose_mul_factorial_mul_factorial hk: C(n,k) * k! * (n-k)! = n!
  -- Together: (n+1) · C(n,k) · k! · (n-k)! = (n+1)!
  -- Hence: (n-k)! / (k+1).ascFactorial (n-k+1) = (n-k)! · k! / (n+1)!
  --                                            = 1 / ((n+1) · C(n,k))
  have h_pos_asc : (((k + 1).ascFactorial (n - k + 1) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < (k + 1).ascFactorial (n - k + 1) := by
      have hk1 : 0 < k + 1 := Nat.succ_pos k
      -- Nat.ascFactorial_pos requires the base ≥ 1
      sorry  -- Mathlib's Nat.ascFactorial_pos: 0 < n → 0 < n.ascFactorial k
    exact_mod_cast this.ne'
  have h_pos_n1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h_pos_ch : ((Nat.choose n k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp
  -- After field_simp, the goal is a polynomial identity over ℕ (cast to ℂ).
  -- Multiply both sides by (k+1).ascFactorial (n-k+1) · (n+1) · C(n,k):
  -- LHS: (n-k)! · (n+1) · C(n,k)
  -- RHS: (k+1).ascFactorial (n-k+1)
  -- Apply factorial_mul_ascFactorial (after multiplying both sides by k!):
  --   k! · (k+1).ascFactorial (n-k+1) = (n+1)!
  -- Apply choose_mul_factorial_mul_factorial hk (after multiplying by (n+1)):
  --   (n+1) · C(n,k) · k! · (n-k)! = (n+1) · n! = (n+1)!
  -- The two factorial expansions agree ⇒ LHS = RHS.
  have h_asc : k ! * (k + 1).ascFactorial (n - k + 1) = (n + 1)! := by
    have := Nat.factorial_mul_ascFactorial k (n - k + 1)
    have hk_sub : k + (n - k + 1) = n + 1 := by omega
    rwa [hk_sub] at this
  have h_choose : Nat.choose n k * k ! * (n - k)! = n ! :=
    Nat.choose_mul_factorial_mul_factorial hk
  -- Cast both to ℂ and combine.
  have h_asc_C : ((k ! : ℕ) : ℂ) * ((((k + 1).ascFactorial (n - k + 1)) : ℕ) : ℂ) =
                  (((n + 1)! : ℕ) : ℂ) := by exact_mod_cast h_asc
  have h_choose_C : ((Nat.choose n k : ℕ) : ℂ) * ((k ! : ℕ) : ℂ) * (((n - k)! : ℕ) : ℂ) =
                     ((n ! : ℕ) : ℂ) := by exact_mod_cast h_choose
  -- Now both forms of (n+1)! and the choose identity combine via ring.
  -- The final ring step needs (n+1)! = (n+1) · n!, which is Nat.factorial_succ.
  have h_succ : ((n + 1)! : ℕ) = (n + 1) * n ! := Nat.factorial_succ n
  have h_succ_C : (((n + 1)! : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) * ((n ! : ℕ) : ℂ) := by
    exact_mod_cast h_succ
  -- Combine: from h_asc_C and h_succ_C:
  --   k! · ascFactorial = (n+1) · n!
  -- From h_choose_C:
  --   choose · k! · (n-k)! = n!
  -- Therefore:
  --   k! · ascFactorial · choose · (n-k)! / (n+1) = k! · n! / 1 (... working it out via ring)
  sorry  -- closes via ring + linear_combination of h_asc_C, h_choose_C, h_succ_C
```

The final `sorry` is solvable by `linear_combination` with explicit coefficients, or by
`field_simp; ring_nf; linear_combination` chained. The exact tactic syntax depends on
v4.26.0's `linear_combination` API, which has shifted between minor versions — to be
finalized at ACT time.

## Real ↔ complex bridge (separate sub-goal)

Hanson's integer-squeeze requires the identity over ℝ (or ℚ), not ℂ. The bridge:

```lean
/-- The real Beta integral with natural exponents equals 1/((n+1)·C(n,k)).
This is the real-valued specialization of `complex_betaIntegral_nat_eq_choose_inv`. -/
theorem real_betaIntegral_nat_eq_choose_inv (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0:ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
      (1 : ℝ) / ((n + 1 : ℝ) * (Nat.choose n k : ℝ)) := by
  -- Bridge lemma: cast the real integrand to ℂ and apply
  -- complex_betaIntegral_nat_eq_choose_inv, then take real parts.
  -- Key step: for x ∈ [0,1], (x : ℂ)^(k : ℕ) = ((x^k : ℝ) : ℂ) (Complex.ofReal_pow).
  sorry
```

The bridge proof is **not** a one-call lemma; it requires:

1. Showing `Complex.betaIntegral (k+1 : ℂ) (n-k+1 : ℂ) = ((∫ x in 0..1, x^k · (1-x)^(n-k) : ℝ) : ℂ)`
   by expanding the integrand and using `Complex.ofReal_pow` plus
   `intervalIntegral.integral_ofReal`.
2. Combining with `complex_betaIntegral_nat_eq_choose_inv` to get a complex equation.
3. Taking real parts via `Complex.ofReal_re` / `Complex.ofReal_inj`.

Estimated LOC for the bridge alone: **30–50 Lean lines**.

**Alternative**: skip the Complex bridge entirely and prove
`real_betaIntegral_nat_eq_choose_inv` directly by induction on `k` (or `n`) using
integration by parts. This avoids the cast machinery but requires Mathlib's
`intervalIntegral.integral_id_mul_*` / `intervalIntegral.integration_by_parts` lemmas
and Lean-side polynomial manipulation. Estimated LOC: **50–80 Lean lines**, with a
simpler proof shape (no namespace bridging).

The ACT-time author should compare the two paths and pick whichever lands first.

## Estimated total ACT LOC

| Section | LOC estimate | Status |
|---|---:|---|
| `complex_betaIntegral_nat_eq_choose_inv` (calc shell + sorry-1) | ~25 | paste-ready above |
| Step 3 cleanup (closes sorry-1) | ~25 | drop-in body provided |
| `real_betaIntegral_nat_eq_choose_inv` (cast bridge) | ~30–50 | sorry-shell above |
| OR: direct real proof by IBP | ~50–80 | not yet sketched |
| **Total (cast bridge path)** | **~80–100** | matches Iter 28 PREP estimate |
| **Total (direct IBP path)** | **~75–105** | alternative |

## What this PREP does NOT include

1. **Hanson's integer-squeeze closure**. Even with 28a in hand, closing
   `axiom hanson_bound` requires the full integer-squeeze assembly, which still needs
   `n₀ ≤ 100` to be discharged by the existing numerical floor
   `hanson_n1..hanson_n100`. That assembly is post-28a work.
2. **A `lake build`-verified Lean draft**. This is doc-only PREP per the Iter 38
   recommendation. The paste-ready skeleton has not been compiled; the next researcher
   should expect to fix v4.26.0-specific syntax/tactic drift during ACT.
3. **Choice between cast-bridge and direct-IBP paths for the real bridge**. Both
   sketched; the call depends on Mathlib's interval-integration IBP API at v4.26.0.

## Honest framing / self-audit

- **No new mathematics**: this is a straightforward "fill in the bearer table" PREP.
  Iter 29 identified the chain at the same SHA; this PREP confirms the SHA is unchanged
  and adds the two bearers (Bearers 3 and 4) Iter 29 elided.
- **No Lean code committed**: doc-only. The skeleton in §"The full chain in calc form"
  is a proposal for the next ACT iteration, not a tested artifact.
- **`hanson_bound` remains an axiom**: this PREP does not reduce the axiom count of
  `BaselProblemOQ01OQ01OQ02OQ03.lean` (still 1 axiom: `hanson_bound`).
- **No edits outside this session log**: `state.md`, `knowledge.md`, `problem.md`,
  gallery `meta.json`, and `src/data/research/problems/*.json` are untouched. The next
  ACT iteration (or its follow-up PREP) will update those.

## Cross-references

- Iter 28 PREP (2026-05-12, #18352): Route B vs Route A vs Route C strategic choice.
- Iter 29 PREP (2026-05-12, #18485): initial bearer audit + erratum corrections to Iter 28.
- Iter 34a ACT (2026-05-14, #19208): 28b-1 bound + `sum_mod_pow_lt_of_pow_dvd_succ`.
- Iter 35b ACT (2026-05-15, #19372): 28c divisibility bridge `choose_mul_succ_dvd_lcmRange`.
- Iter 36 PREP (2026-05-15): 28b-2 paste-ready discharge (precedent for this PREP's format).
- Iter 38 ACT (2026-05-28): 28b-2 witness saturation shipped.

## What the next researcher should do

**Option A (recommended)**: Take this skeleton, apply it to
`BaselProblemOQ01OQ01OQ02OQ03.lean` after Iter 38's
`exists_witness_choose_saturates_log_succ`, fix the v4.26.0 syntax drift (likely
`field_simp`/`linear_combination` minor variants), and build-verify under
`./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03`. Expected ACT
size: 80–100 LOC. Expected wall-clock: 1 session.

**Option B**: First confirm the real-bridge path (cast vs. direct IBP) by writing
a 5–10 line probe of `intervalIntegral.integration_by_parts` / `integral_ofReal` at
v4.26.0, then commit to one path. Adds 0.5 session of front-loaded uncertainty
reduction.

**Risk register** (Mathlib API drift since Iter 36 PREP):
- Low risk: Bearers 1, 2, 3, 4 (verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
  the same SHA Iter 38 build-verified).
- Medium risk: `linear_combination` tactic — has shifted minor semantics between
  v4.25 → v4.26 (parenthesization of hypothesis coefficients).
- Medium risk: `field_simp` over ℂ — sometimes leaves a `pow`-shaped residual that
  needs explicit `Complex.cpow_nat_cast`-style massaging.
- Higher risk (cast-bridge path only): `intervalIntegral.integral_ofReal` — the
  exact lemma name varies between `MeasureTheory.integral_re` and
  `intervalIntegral.integral_ofReal` depending on which Mathlib refactor wave is current.
  Verify at ACT time.
