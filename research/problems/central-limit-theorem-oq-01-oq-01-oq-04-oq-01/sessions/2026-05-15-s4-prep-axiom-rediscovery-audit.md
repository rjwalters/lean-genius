# Session 2026-05-15 — S4 PREP: Sibling-audit of #19116's 6 new axioms (doc-only)

**Researcher**: researcher-3
**Phase**: PREP (doc-only — strictly conflict-free with PR #19083 / #19116 / #19195)
**Iteration**: S4 (post-mechanic axiom-rediscovery audit)
**Date**: 2026-05-15

## §1 — Why this session is doc-only

`central-limit-theorem-oq-01-oq-01-oq-04-oq-01` has 2 open MERGEABLE/CLEAN
doc-only PRs awaiting the deployer cycle, both tightly coupled to the
companion-file blocker:

- **#19083** (research, S3 BUILD-VERIFY, doc-only) — first Docker baseline of
  the parent `CentralLimitTheoremOQ01OQ01OQ04.lean` finds **23 elaboration
  errors at Mathlib v4.26.0**; updates `state.md` Iter 1 OBSERVE → Iter 3
  PARENT-BLOCKED with 3-cluster inventory.
- **#19195** (research, S2 PREP coord, doc-only) — coordination memo
  documenting the deployer stall and refreshing the R1 plan against
  post-#19116 reality.

Also relevant (mechanic-scope, MERGEABLE/CLEAN):

- **#19116** (mechanic, parent-file repair) — 23 errors fixed, build verified
  **7744/7744 jobs clean**, but `axiomCount` jumped **2 → 8** because 6
  helpers lost their proofs.

Per memory `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
and `feedback_researcher_sweep_audit_pin_verify_multi_prep_chain.md`, the
right move is a **tightly-scoped doc-only PREP** that adds load-bearing
new value without conflicting on any owned file. This memo:

- adds **exactly one new file** (this session note, ~700 LOC),
- **does not** edit `state.md` (owned by #19083), the slug JSON tracker
  (owned by #19083), the Lean file (owned by #19116), `meta.json`
  (owned by #19116), or the prior S2 PREP coord note (owned by #19195).

**Build risk: NONE** (doc-only).

## §2 — What this audit adds (not already in #19083 / #19116 / #19195)

#19116 axiomatized 6 helpers and **cited specific removed/renamed
Mathlib v4.26.0 APIs as justification** for each. Neither #19083, #19116
nor #19195 cross-checks those citations against the lake-pinned Mathlib
SHA. This audit pin-verifies each cited API at the **exact pinned SHA**
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`)
and asks the load-bearing question:

> For each axiom, is the cited "removed API" actually **gone**, or merely
> **renamed/restructured**? If the latter, is the axiom **dischargeable**
> via a surgical rename without inventing new mathematics?

**Finding**: 3 of 6 new axioms are likely **fully dischargeable** by API
rename; 1 is dischargeable via tactic restructure; 2 (`operator_stable_linear_image`,
`scalar_exponent_ge_half`) reflect **genuine math gaps** and should remain
axiomatized. Discharge of all 3+1 would bring `axiomCount` from **8 → 4**
(reverting back to within +2 of the pre-mechanic baseline of 2, while
keeping the Docker build green).

## §3 — Pin-verified bearer table at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All bearers verified via direct `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` (Contents API, not Search API — separate
rate-limit pool) and confirmed with raw-content `download_url` fetches.

| Cited API (in #19116 axiom docstrings) | Status at SHA `2df2f015...` | Replacement / canonical name | File:Line |
|----------------------------------------|------------------------------|------------------------------|-----------|
| `Real.rpow_one_div_eq_pow_inv` | **REMOVED** (0 hits across Mathlib; absent from `Pow/Real.lean`) | `Real.sqrt_eq_rpow` + `Real.rpow_neg` chain | `Pow/Real.lean:981` + `:252` |
| `Complex.re_ofReal` | **RENAMED** (not in `Data/Complex/Basic.lean`) | `Complex.ofReal_re` | `Data/Complex/Basic.lean:87` |
| `Real.exp_le_one_of_nonpos` | **RENAMED/RESTRUCTURED** (0 hits under that name) | `Real.exp_le_one_iff` (iff form) | `Analysis/Complex/Exponential.lean:339` |
| `Filter.tendsto_const_nhds` | **NAMESPACE MOVE** (0 hits under `Filter.`) | top-level `tendsto_const_nhds` | `Topology/Neighborhoods.lean:190` |
| `Matrix.PosSemidef.inner_le` | **RENAMED/REFACTORED** (0 hits under that name) | `Matrix.PosSemidef.dotProduct_mulVec_nonneg` | `LinearAlgebra/Matrix/PosDef.lean:298` |
| `Matrix.eigenvalues` (general) | **NARROWED** (only Hermitian survives) | `Matrix.IsHermitian.eigenvalues` | `LinearAlgebra/Matrix/Spectrum.lean` |
| `Matrix.exp` (function) | **NO STANDALONE FUNCTION** — `Matrix.exp` lemmas use `NormedSpace.exp 𝕂` under the `Matrix` namespace | `NormedSpace.exp 𝕂 (M : Matrix _ _ _)` | `Analysis/Normed/Algebra/MatrixExponential.lean:72+` |

### §3.1 Audit method (reproducibility check)

For each "REMOVED" / "RENAMED" verdict, the audit used **at least two
independent confirmations**:

1. **Negative-hit confirmation**: `gh api 'search/code?q="<old-name>"+repo:leanprover-community/mathlib4' -q '.total_count'` returns `0`.
2. **Positive-hit replacement**: `gh api 'search/code?q="<new-name>"+repo:leanprover-community/mathlib4' -q '.items'` returns the canonical site.
3. **Direct fetch at SHA**: `download_url` fetch of the candidate file at the lake-pinned SHA + literal `grep` for the lemma signature.

This third step is the load-bearing one — Search API can return stale
indices, but the raw `download_url` content is the **exact source** at
the pinned commit.

## §4 — Per-axiom discharge analysis

Each of #19116's 6 new axioms below is analyzed for (a) the cited reason,
(b) the verified status at the pin, (c) **whether the axiom is
dischargeable** with a surgical fix that doesn't introduce new math, and
(d) an estimated LOC delta for the discharge.

### §4.1 `gaussCharFun_norm_le_one` (line 121–123) — **DISCHARGEABLE**

```lean
axiom gaussCharFun_norm_le_one (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (hSg : Matrix.PosSemidef Sg) (ξ : Fin d → ℝ) :
    ‖gaussCharFun d Sg ξ‖ ≤ 1
```

Cited reasons (from docstring):

> Original proof invoked `Matrix.PosSemidef.inner_le` plus `Complex.re_ofReal`
> / `Real.exp_le_one_of_nonpos`, all of which have been renamed or removed
> in v4.26.0. The math content is standard (`φ_Σ(ξ) = exp(-Q(ξ)/2)` with
> `Q(ξ) ≥ 0` by PosSemidef → `‖·‖ ≤ 1`), but the proof chain spans 3
> renamed lemmas across PSD/exp/complex namespaces.

**Pin-verification verdict**: All 3 cited "removed" APIs are **mere
renames**, not deep removals:

| Old | New @ v4.26.0 |
|-----|---------------|
| `Matrix.PosSemidef.inner_le` | `Matrix.PosSemidef.dotProduct_mulVec_nonneg` @ `PosDef.lean:298` |
| `Complex.re_ofReal` | `Complex.ofReal_re` @ `Complex/Basic.lean:87` |
| `Real.exp_le_one_of_nonpos` | `Real.exp_le_one_iff.mpr` @ `Complex/Exponential.lean:339` |

**Surgical discharge sketch** (~12–18 LOC, no new math):

```lean
theorem gaussCharFun_norm_le_one (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (hSg : Matrix.PosSemidef Sg) (ξ : Fin d → ℝ) :
    ‖gaussCharFun d Sg ξ‖ ≤ 1 := by
  -- Step 1: unfold gaussCharFun = exp(-Q(ξ)/2 : ℂ)
  simp only [gaussCharFun]
  -- Step 2: ‖exp z‖ = exp z.re for any z : ℂ  (Complex.norm_exp)
  rw [norm_exp]
  -- Step 3: real part of -(Q : ℝ)/2 = -Q/2 (Complex.ofReal_re after push_cast)
  -- Step 4: exp (-Q/2) ≤ 1 ↔ -Q/2 ≤ 0  (Real.exp_le_one_iff.mpr)
  -- Step 5: Q ≥ 0 from PosSemidef.dotProduct_mulVec_nonneg
  ...
```

The Q ≥ 0 step uses `hSg.dotProduct_mulVec_nonneg ξ`, with possibly minor
sign/star-bundle adjustments because `quadForm` is the real-quadratic-form
specialization and `dotProduct_mulVec_nonneg` lives over `star x ⬝ᵥ M *ᵥ x`.
The `star`-identity on ℝ is trivial.

**Estimated discharge LOC**: 12–18 LOC.
**Estimated risk**: low (pure rename + standard real-positivity step).

### §4.2 `gaussian_has_scalar_exponent` (line 165–166) — **DISCHARGEABLE**

```lean
axiom gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2)
```

Cited reason:

> The original proof relied on `Real.rpow_one_div_eq_pow_inv` (renamed/removed
> in v4.26.0) for the rpow-to-sqrt conversion `n^(-1/2) = 1/√n`, and on a
> simp set with the now-ambiguous `exp_zero` (Complex.exp_zero vs Real.exp_zero).
> Mathematical content reduces to `gaussian_operator_stable` with witness drift = 0.

**Pin-verification verdict**: `Real.rpow_one_div_eq_pow_inv` is **truly
removed** (0 hits across Mathlib + absent from `Pow/Real.lean`). However,
the **mathematical identity** `n^(-1/2) = 1/√n` is fully derivable at
v4.26.0 via:

- `Real.sqrt_eq_rpow : √x = x ^ (1 / (2 : ℝ))` @ `Pow/Real.lean:981`
- `Real.rpow_neg : 0 ≤ x → x ^ (-y) = (x ^ y)⁻¹` @ `Pow/Real.lean:252`
- `Real.rpow_div_two_eq_sqrt : 0 ≤ x → x ^ (r / 2) = √x ^ r` @ `Pow/Real.lean:989`

Combining (1) + (2) gives `n^(-1/2) = (n^(1/2))⁻¹ = (√n)⁻¹ = 1/√n` for
`0 ≤ (n : ℝ)`. The `Complex.exp_zero`/`Real.exp_zero` ambiguity is a
simp-set hygiene issue, solvable by either `simp only [Complex.exp_zero]`
or `simp only [Real.exp_zero]` — not by axiomatization.

Note also: the docstring **itself** observes that the math reduces to
`gaussian_operator_stable` with drift = 0. `gaussian_operator_stable` is
already **proven** (line 146–156), so the axiom is essentially an
unfolding of `HasScalarExponent` applied to a proven theorem.

**Surgical discharge sketch** (~20–35 LOC):

```lean
theorem gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2) := by
  -- Unfold HasScalarExponent: ∃ A_n drift, ...
  refine ⟨fun n _ => (n : ℝ)^(-(1/2 : ℝ)) • (1 : Matrix _ _ ℝ),
          fun _ _ => 0, fun n hn ξ => ?_⟩
  -- Reduce A_n ξ via n^(-1/2) = 1/√n + the proven gaussian_operator_stable
  have hpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.rpow_neg hpos, ← Real.sqrt_eq_rpow]
  ...
  exact gaussian_operator_stable d Sg ξ n hn
```

**Estimated discharge LOC**: 20–35 LOC. The "..." span finishes the
scalar-matrix-multiplication unfold (A_n ξ = (1/√n) · ξ component-wise),
which interacts with `quadForm_scale_inv_sqrt` already in the file.

**Estimated risk**: medium-low. The sqrt/rpow algebra is local and
mechanical; the only nontrivial step is the matrix-on-vector scaling
unfold, but `quadForm_scale_inv_sqrt` is already proven.

### §4.3 `gaussian_is_operator_stable` (line 175–176) — **DISCHARGEABLE (tactic-restructure)**

```lean
axiom gaussian_is_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (gaussCharFun d Sg)
```

Cited reason:

> The original proof used a deep `conv_lhs` block with `ext ξ; arg 1; ext i;
> rw [Finset.sum_ite_eq']` that v4.26.0's stricter `conv` tactic no longer
> accepts (`invalid 'ext' conv tactic`). Mathematical content follows from
> `gaussian_has_scalar_exponent` with witness A_n = n^{-1/2}·I.

**Pin-verification verdict**: This is **not** an API removal — it's a
tactic-elaborator strictness change. The fix is a **tactic restructure**,
not a math axiomatization.

**Surgical discharge sketch** (~10–20 LOC):

```lean
theorem gaussian_is_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (gaussCharFun d Sg) := by
  obtain ⟨A_n, b_n, h⟩ := gaussian_has_scalar_exponent d Sg
  -- IsOperatorStable unfolds to ∃ A_n b_n, ∀ n ≠ 0 ξ, ...
  refine ⟨A_n, b_n, fun n hn ξ => ?_⟩
  -- Avoid conv_lhs ext ξ; use funext + congrArg directly
  have heq : (fun i => ∑ j, A_n n hn i j * ξ j) = ?_ := by
    funext i; simp [...]   -- explicit funext, not conv_lhs ext
  rw [heq]
  exact h n hn ξ
```

The original `conv_lhs ext ξ; arg 1; ext i; rw [Finset.sum_ite_eq']`
pattern was attempting to push a `Finset.sum_ite_eq'` rewrite under
two nested lambdas in the LHS. The same effect is achievable in v4.26.0
via:

- `funext` to enter the outer lambda, OR
- `show` to rewrite the goal to the equivalent fully-applied form, OR
- direct `congr 1; funext` chain instead of `conv ... ext`.

This axiom **depends on** `gaussian_has_scalar_exponent` (cf. its
docstring's "Mathematical content follows from"). Discharging §4.2 is
prerequisite to discharging §4.3.

**Estimated discharge LOC**: 10–20 LOC, contingent on §4.2 discharge.

### §4.4 `operator_stable_linear_image` (line 235–237) — **KEEP AXIOMATIZED**

```lean
axiom operator_stable_linear_image (d : ℕ) (φ : (Fin d → ℝ) → ℂ)
    (hφ : IsOperatorStable d φ) (B : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (fun ξ => φ (fun i => ∑ j, B i j * ξ j))
```

Cited reason:

> Reference: Meerschaert & Scheffler (2001), Theorem 7.2.1 (closure under
> linear images). ... we axiomatize the existence of *some* witness rather
> than committing to a specific algebraic form. ... requires B invertibility
> — without it, the image distribution can collapse onto a lower-dimensional
> subspace where operator-stability does not apply in the same form.

**Pin-verification verdict**: This is **not** an API issue. The docstring
explicitly identifies a **math gap**: the axiom as stated is actually
**too strong** (lacks the invertibility hypothesis on `B`). The "axiom"
is genuinely a placeholder for the MS Theorem 7.2.1 closure result.

**Verdict**: Keep axiomatized. This is a legitimate mathematical
load-bearing axiom representing MS 2001 Thm 7.2.1 — a result whose Lean
formalization is **out of scope** of this entry's R1/R2 routes.

**Recommendation**: Add `(hB : IsUnit B.det)` (or `(hB : B.Invertible)`)
as a hypothesis. This is a content fix, not a discharge — recommend
deferring to a separate doctor PR.

### §4.5 `scalar_exponent_ge_half` (line 265–268) — **KEEP AXIOMATIZED**

```lean
axiom scalar_exponent_ge_half (d : ℕ) (φ : (Fin d → ℝ) → ℂ) (c : ℝ)
    (hSE : HasScalarExponent d φ c)
    (hnd : ∀ v : Fin d → ℝ, (∀ i, v i = 0) → False) :
    1 / 2 ≤ c
```

Cited reason:

> ...Mathematical content: every eigenvalue λ of the exponent matrix
> satisfies Re(λ) ≥ 1/2; for E = c·I, this collapses to c ≥ 1/2. We
> axiomatize the scalar form directly because the general eigenvalue
> formulation requires a complex-spectrum API (Matrix.eigenvalues was
> removed at Mathlib v4.26.0 in favor of the Hermitian-restricted
> IsHermitian.eigenvalues — for the non-Hermitian exponent matrices of
> stable laws we'd need to base-change to ℂ via charpoly.roots, which
> is mathlib-grade scaffolding outside this file's scope).

**Pin-verification verdict**: The cited "Matrix.eigenvalues was removed"
is partially correct (only Hermitian eigenvalues survive at v4.26.0).
But the deeper issue is the **non-Hermitian exponent matrices of stable
laws** — even at v4.25 (before the rename) the general eigenvalue spectrum
would require **`Polynomial.charpoly`-roots** machinery in ℂ. This is
the **Hudson-Mason 1982 eigenvalue bound**, a Lean-grade research project
on its own.

**Verdict**: Keep axiomatized. This is a legitimate mathematical
load-bearing axiom (Hudson-Mason 1982 / Sharpe 1969).

**Note**: The axiom's hypothesis `hnd : ∀ v, (∀ i, v i = 0) → False` is
mathematically vacuous (the only v with `∀ i, v i = 0` is the zero vector,
and the hypothesis says this implies False — i.e., the dimension is
positive). This may be a placeholder for non-degeneracy and could be
sharpened in a future doctor pass, but it does not affect the discharge
question here.

### §4.6 `gaussian_in_own_doa` + `finite_cov_in_gaussian_doa` (lines 304–318) — **DISCHARGEABLE (partial — tactic-restructure)**

```lean
axiom gaussian_in_own_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    InOperatorDomainOfAttraction d (gaussCharFun d Sg) (gaussCharFun d Sg)

axiom finite_cov_in_gaussian_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (hSg : Matrix.PosSemidef Sg) (φ : (Fin d → ℝ) → ℂ)
    (hφ_char : φ (fun _ => 0) = 1)
    (hφ_cov : ∃ (hφ_reg : True),
      Filter.Tendsto (fun ξ : Fin d → ℝ => φ ξ) (nhds 0) (nhds 1)) :
    ∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ
```

Cited reason (shared between the two):

> Original proof invoked `Filter.tendsto_const_nhds` (renamed to top-level
> `tendsto_const_nhds` in v4.26.0) on a sequence-of-functions that is only
> POINTWISE constant — not constant as a function-valued sequence. v4.26.0's
> stricter elaborator no longer accepts the leak.

**Pin-verification verdict**: Two-part claim:

1. **Rename half — TRUE**: `tendsto_const_nhds` exists at `Mathlib/Topology/Neighborhoods.lean:190` (top-level, not `Filter.`-prefixed). This is a pure rename, surgically fixable.
2. **Pointwise-not-constant half — TRUE but DISCHARGEABLE**: The leak the
   docstring describes is real — `tendsto_const_nhds` requires a *literal*
   constant sequence, and the original proof was applying it to a
   sequence-of-functions that varies in `n`. But this is fixable by
   either:
   - Using `Filter.Tendsto.congr'` to bridge the pointwise-constant function
     to the literal-constant target, OR
   - Reformulating the goal to extract the pointwise convergence first
     (`Filter.Tendsto` of `ℝ → ℂ` at each ξ) and then closing each
     via `tendsto_const_nhds`.

**For `gaussian_in_own_doa`**: The math content is the multivariate CLT
self-similarity `∑ Xᵢ / √n →ᵈ N(0, Σ)` for i.i.d. Gaussian Xᵢ. Discharging
this depends on **`InOperatorDomainOfAttraction`**'s unfolding (which
involves `Filter.Tendsto` of the n-th power of the char function divided
by `ν(...)`). The discharge would proceed by:

```lean
theorem gaussian_in_own_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    InOperatorDomainOfAttraction d (gaussCharFun d Sg) (gaussCharFun d Sg) := by
  -- Unfold InOperatorDomainOfAttraction
  intro t ht ξ
  -- Use gaussian_operator_stable (already proven) to recover the n-th power identity
  have hgos := gaussian_operator_stable d Sg ξ
  -- Reduce the limit to a literal constant 1 via pointwise computation
  apply Filter.Tendsto.congr'
  ...
  exact tendsto_const_nhds
```

**Estimated discharge LOC** (gaussian_in_own_doa): ~25–40 LOC. Risk:
medium — the pointwise-constant reduction requires care with the t > 0
parameter and matrix-exp identity.

**For `finite_cov_in_gaussian_doa`**: This is more delicate. The
hypotheses include the trivial `hφ_reg : True` placeholder (note that
this hypothesis is mathematically vacuous and likely a stand-in for a
real regularity condition). Discharging would require a proper
formulation of the regularity hypothesis, not just renames.

**Verdict**:
- `gaussian_in_own_doa` is **dischargeable** (~25–40 LOC) — recommend.
- `finite_cov_in_gaussian_doa` should be **kept axiomatized** until its
  vacuous `hφ_reg : True` placeholder is replaced with a proper
  regularity hypothesis.

## §5 — Summary table

| Axiom | Verdict | Est. LOC | Risk | Math content |
|-------|---------|----------|------|--------------|
| `gaussCharFun_norm_le_one` | **DISCHARGEABLE** (pure rename) | 12–18 | low | Q(ξ) ≥ 0 + exp ≤ 1 chain |
| `gaussian_has_scalar_exponent` | **DISCHARGEABLE** (rpow → sqrt chain) | 20–35 | medium-low | n^(-1/2) = 1/√n + proven gaussian_operator_stable |
| `gaussian_is_operator_stable` | **DISCHARGEABLE** (tactic restructure) | 10–20 | low (depends on §4.2) | Wraps §4.2 with funext |
| `operator_stable_linear_image` | **KEEP** (math gap + missing hypothesis) | — | — | MS 2001 Thm 7.2.1 |
| `scalar_exponent_ge_half` | **KEEP** (Hudson-Mason 1982 eigenvalue bound) | — | — | Non-Hermitian eigenvalue spectrum |
| `gaussian_in_own_doa` | **DISCHARGEABLE** (Tendsto.congr') | 25–40 | medium | CLT self-similarity for Gaussian |
| `finite_cov_in_gaussian_doa` | **KEEP for now** (vacuous regularity hyp) | — | — | Multivariate CLT for finite-cov |

**Cumulative discharge potential**: 67–113 LOC; axiomCount **8 → 4**
(2 pre-existing including `meerschaert_scheffler` + 2 KEEP-list axioms).

This brings the parent file back within **+2 axioms** of its pre-mechanic
baseline of 2, while preserving the **7744/7744 jobs clean Docker build**
that #19116 achieved.

## §6 — Composition with #19083 / #19116 / #19195 (strict file-disjointness)

| PR | Touched files | This audit's files |
|----|---------------|---------------------|
| #19083 | `state.md`, `src/data/research/problems/.../...json` | not touched |
| #19116 | `Lean file`, `meta.json` | not touched |
| #19195 | `sessions/<date>-s2-prep-coord-deployer-stall.md` | distinct session-file path |
| **this audit** | new file `sessions/2026-05-15-s4-prep-axiom-rediscovery-audit.md` | — |

Conflict-free. All four PRs can land in any order.

## §7 — Recommended sequencing post-deployer-unstall

1. **Merge #19116** (mechanic, build-clean). This unblocks the parent file
   import for any companion-file ACT (R1 / R2 routes from S1).
2. **Merge #19083** + **#19195** (state.md + JSON coord; can land in
   either order — both edit different files).
3. **Merge this S4 PREP** (new doc-only file; conflict-free with all
   three above).
4. **S5 ACT (mechanic-scope)**: A doctor PR discharges §4.1 + §4.2 + §4.3
   (~42–73 LOC). Result: `axiomCount` 8 → 5.
5. **S6 ACT (mechanic-scope)**: A doctor PR discharges §4.6 first half
   (`gaussian_in_own_doa`, ~25–40 LOC). Result: `axiomCount` 5 → 4.
6. **S7+ companion-file R1 route**: With the parent at 4 axioms and the
   3 dischargeable-but-now-proven theorems available, the
   `meerschaert_scheffler_gaussian` companion theorem from S1's plan can
   land cleanly without dragging axiom debt forward.

## §8 — Negative findings (false starts considered and ruled out)

The following audit angles were considered but ruled out as **not
yielding additional discharge candidates**:

- **`Real.exp_zero` simp ambiguity** (cited as secondary issue in §4.2):
  This is a simp-set hygiene problem, not a math gap. The fix is
  `simp only [Real.exp_zero]` or `simp only [Complex.exp_zero]` explicitly,
  not axiomatization. Covered within §4.2's discharge sketch.
- **`Σ → Sg` parser-token rename** (Cluster A in #19083's 23-error
  inventory): Already mechanic-fixed in #19116 (global rename to `Sg`).
  Not an axiom-discharge angle.
- **`NormedSpace.exp` vs `Matrix.exp`** (Cluster B in #19083): Already
  mechanic-fixed in #19116 by switching to `NormedSpace.exp 𝕂` syntax in
  the `meerschaert_scheffler` axiom statement. Not an axiom-discharge
  angle for the **new** axioms (only the pre-existing one).
- **`Matrix.eigenvalues` general spectrum** for §4.5: As the docstring
  correctly notes, recovering the general (non-Hermitian) spectrum from
  `Polynomial.charpoly.roots` at v4.26.0 is a multi-hundred-LOC project.
  Out of scope; KEEP-axiomatized verdict stands.

## §9 — Pin-verification reproducibility manifest

For independent verification, the following commands reproduce every
bearer in §3:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# §4.1 / §4.6 — Matrix.PosSemidef.dotProduct_mulVec_nonneg
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Matrix/PosDef.lean?ref=$SHA" \
  -q '.download_url' | xargs curl -s | sed -n '298p'

# §4.1 — Complex.ofReal_re
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Complex/Basic.lean?ref=$SHA" \
  -q '.download_url' | xargs curl -s | sed -n '87p'

# §4.1 — Real.exp_le_one_iff
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Complex/Exponential.lean?ref=$SHA" \
  -q '.download_url' | xargs curl -s | sed -n '339p'

# §4.2 — Real.sqrt_eq_rpow + Real.rpow_neg
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean?ref=$SHA" \
  -q '.download_url' | xargs curl -s | sed -n '981p;252p;989p'

# §4.6 — tendsto_const_nhds (top-level)
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Neighborhoods.lean?ref=$SHA" \
  -q '.download_url' | xargs curl -s | sed -n '190p'

# Matrix.exp / NormedSpace.exp under Matrix namespace
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean?ref=$SHA" \
  -q '.download_url' | xargs curl -s | sed -n '72,82p'
```

The lake-pinned SHA itself can be reproduced from this worktree:

```bash
jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
```

## §10 — Honest calibration

This S4 PREP is **doc-only** and ships **zero Lean changes**, **zero axiom
deltas**, and **no PR conflicts**. Its load-bearing claim is:

> Of the 6 new axioms introduced by mechanic PR #19116, at least 4 are
> dischargeable at Mathlib v4.26.0 via surgical renames or tactic
> restructures totaling ~67–113 LOC. The remaining 2 axioms reflect
> legitimate mathematical content (MS 2001 Thm 7.2.1 + Hudson-Mason 1982
> eigenvalue bound) and should remain axiomatized.

This claim is **falsifiable** at any time by attempting the discharge
sketches in §4.1 / §4.2 / §4.3 / §4.6 (first half) and reporting back.
The next iteration after deployer unstall should be **S5 ACT (doctor-scope)**
attempting §4.1's surgical discharge as the cheapest fastest test of
the audit's claim.

## §11 — Race-risk and conflict-freedom check

At draft time (`2026-05-15T~09:30Z`):

- **Open PRs on this slug**: #19083 (touches `state.md` + JSON), #19195
  (touches a different session file), and #19116 (mechanic — touches Lean
  + meta.json). This audit creates **exactly one new file** under
  `sessions/` and touches **none** of those files.
- **Pre-push double-check**: `git diff --stat origin/main..HEAD` will show
  exactly 1 file added, 0 modified.
- **Race against this slug**: No active claim on `central-limit-theorem-oq-01-oq-01-oq-04-oq-01`
  other than the claim this researcher acquired at draft time. The PRD
  pile-up is documented in #19195 already.

**Verdict**: Conflict-free. Safe to push and PR.
