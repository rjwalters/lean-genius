# ORIENT — Min-max scaffolding for Cauchy interlacing

**Author**: researcher-11, 2026-06-15 (iter 2 ORIENT; iter 3 verified API spot-check)
**Status**: orientation + Mathlib API spot-check — no Lean shipped (both proof
backends down: Docker build pool saturated at 3 concurrent `lean-build`
containers on the 7.65 GiB VM; Aristotle MCP `prove` → `Resource not found`).
This memo pins the Mathlib surface and the proof decomposition so the next
session (or Aristotle, when it returns) can go straight to formalization.

> ## ⚑ ITER 3 CORRECTION — verified against Mathlib master (docs + source)
> The host `.lake` is a self-referential (ELOOP) symlink and the build image
> ships only oleans, so no local grep was possible — instead the API was
> spot-checked against the canonical Mathlib4 source/docs on GitHub. Findings:
>
> **The iter-2 gap claim "No sorted eigenvalue function" is WRONG and is
> retracted.** Mathlib provides sorted eigenvalues at **both** levels:
> - **Matrix-native (use this for the statement):**
>   `Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card n) → ℝ` (noncomputable),
>   sorted **DECREASING** with `Matrix.IsHermitian.eigenvalues₀_antitone`.
>   (`Matrix.IsHermitian.eigenvalues` reuses the original index type `n` and is
>   **not** sorted — that is what the stale note conflated.) Companion:
>   `Matrix.IsHermitian.eigenvectorBasis`. File:
>   `Mathlib.LinearAlgebra.Matrix.Spectrum`.
> - **Operator (needed only for the extreme-case proofs via Rayleigh):**
>   `LinearMap.IsSymmetric.eigenvalues : Fin n → ℝ` — sorted DECREASING with
>   `eigenvalues_antitone`, `hasEigenvalue_eigenvalues`, `eigenvectorBasis`,
>   `exists_eigenvalues_eq`, `card_filter_eigenvalues_eq`. File:
>   `Mathlib.Analysis.InnerProductSpace.Spectrum`.
>
> Consequence: the §2.1 "build a monotone enumeration / state abstractly over
> monotone tuples" obligation **disappears**. State interlacing directly over
> `eigenvalues₀` on the matrix (no abstract tuples, no operator bridge in the
> *statement*); the operator/Rayleigh layer is needed only to *prove* the
> extreme cases (§4-verified). The §5 abstract statement is superseded by
> **§5-revised**.
>
> **Still confirmed absent (the real keystone gap):** no k-th
> Courant–Fischer / min-max characterization in `InnerProductSpace.Rayleigh` or
> `InnerProductSpace.Spectrum`. Only the two EXTREME eigenvalues are
> variationally characterized — exact signatures in **§4-verified**.

## 1. What the theorem says (one-step interlacing)

Let `A : Matrix (Fin n) (Fin n) ℂ` be Hermitian with eigenvalues sorted
`λ₀ ≤ λ₁ ≤ ⋯ ≤ λ_{n-1}`, and let `B` be the principal `(n-1)×(n-1)` submatrix
obtained by deleting row/column `i`, with sorted eigenvalues
`μ₀ ≤ ⋯ ≤ μ_{n-2}`. Then for every `k` with `0 ≤ k ≤ n-2`:

```
λ_k ≤ μ_k ≤ λ_{k+1}.
```

This is the codimension-one case. The "delete `m` rows/cols" generalization
(`λ_k ≤ μ_k ≤ λ_{k+m}`) is a stretch goal and should NOT be attempted before
the one-step case lands.

## 2. The real obstacle is NOT the mathematics — it is missing Mathlib scaffolding

The math is classical (Courant–Fischer min-max + a dimension count). The
formalization gap, confirmed against the pinned tree, is:

1. ~~**No sorted eigenvalue function.**~~ **RETRACTED (iter 3).** This was
   carried from stale survey notes and is false for the operator formulation.
   While `Matrix.IsHermitian.eigenvalues` is indeed indexed by the matrix's own
   index type, the operator API `LinearMap.IsSymmetric.eigenvalues : Fin n → ℝ`
   **is** sorted (decreasing) with a packaged `eigenvalues_antitone` proof — see
   the iter-3 correction box above. **Formalize in the operator setting** and
   the sorting obligation vanishes; the only residual is the routine
   `Matrix → LinearMap` bridge (`Matrix.toEuclideanLin` / the Hermitian
   `IsSymmetric` instance), and the principal-submatrix ↔ hyperplane-restriction
   identification, both of which are local bookkeeping, not missing theory.

2. **No k-th Courant–Fischer min-max.** Mathlib's
   `Mathlib.Analysis.InnerProductSpace.Rayleigh` packages only the **extreme**
   eigenvalues via `iSup`/`iInf` of the Rayleigh quotient
   (`⨆ x, ⟪T x, x⟫ / ‖x‖²` = top eigenvalue, and the `iInf` dual). There is no
   `λ_k = ⨅_{dim S = k+1} ⨆_{x ∈ S} R(x)` statement. **This lemma is the
   keystone** and is independently reusable (Weyl inequalities, eigenvalue
   monotonicity under perturbation, Lidskii). Building it is the bulk of the
   work and is itself a worthwhile standalone contribution.

## 3. Proof decomposition (Courant–Fischer route, Approach A)

Once the min-max lemma exists, interlacing is short. Write
`R_A(x) = ⟪A x, x⟫ / ‖x‖²` for the Rayleigh quotient and identify `B` with the
restriction of `A` to the coordinate hyperplane `H_i = {x : x i = 0}`
(`dim H_i = n-1`). Then `R_B = R_A` restricted to `H_i`.

**Lower bound `λ_k ≤ μ_k`** (min over (k+1)-dim subspaces of a max):
```
μ_k = ⨅_{S ⊆ H_i, dim S = k+1} ⨆_{x ∈ S} R_A(x)
    ≥ ⨅_{S ⊆ ℂⁿ, dim S = k+1} ⨆_{x ∈ S} R_A(x) = λ_k,
```
because restricting the feasible subspaces to those inside `H_i` shrinks the
domain of the outer `⨅`, hence raises (or keeps) the infimum.

**Upper bound `μ_k ≤ λ_{k+1}`** (dual max-min form, the dimension count):
```
λ_{k+1} = ⨆_{dim S = k+1} ⨅_{x ∈ S} R_A(x)   -- dual Courant–Fischer
```
For any `(k+2)`-dim subspace `S ⊆ ℂⁿ`, `S ∩ H_i` has dimension `≥ k+1` (a
`(k+2)`-dim space meets a codimension-1 hyperplane in `≥ k+1` dims). Feeding
`S ∩ H_i` into `B`'s min-max gives `μ_k ≤ λ_{k+1}`. **Key lemma 2** is exactly
this `dim (S ∩ H_i) ≥ dim S - 1` fact — in Mathlib,
`Submodule.finrank_sup_add_finrank_inf_eq` /
`Submodule.finrank_le` give the inequality; the codim-1 input is
`finrank H_i = n - 1`.

## 4. Extreme cases are reachable TODAY from existing Rayleigh API

Before the general min-max lands, the boundary cases are provable from what
Mathlib already has and make good first PRs / good Aristotle targets. NOTE the
sign flip below: §1 used the textbook *increasing* convention `λ₀ ≤ ⋯`, but
Mathlib's `eigenvalues` is *decreasing*, so spell the extreme cases out in the
convention you actually formalize against.

- `k = 0` (top): largest eigenvalue of `B` ≤ largest eigenvalue of `A`. The
  largest eigenvalue equals `⨆` of the Rayleigh quotient; restricting the
  domain from the whole space to `H_i ⊆ ℂⁿ` can only **lower** an `⨆`, so the
  `B`-side `⨆` ≤ the `A`-side `⨆`.
- `k = n-2` (bottom): smallest eigenvalue of `A` ≤ smallest eigenvalue of `B`.
  The smallest eigenvalue equals `⨅` of the Rayleigh quotient; restricting to
  `H_i` can only **raise** an `⨅`, so the `A`-side `⨅` ≤ the `B`-side `⨅`.

These pin the endpoints without the k-th min-max lemma and exercise the `H_i`
restriction plumbing the general case needs.

### §4-verified — exact Mathlib signatures (checked iter 3)

From `Mathlib.Analysis.InnerProductSpace.Rayleigh` (master):
```lean
-- the supremum of the Rayleigh quotient IS an eigenvalue (the largest):
theorem LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional
    [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T (⨆ x : {x : E // x ≠ 0}, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : ℝ)

-- dual: the infimum IS an eigenvalue (the smallest):
theorem LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
    [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T (⨅ x : {x : E // x ≠ 0}, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : ℝ)
```
Rayleigh quotient itself: `ContinuousLinearMap.rayleighQuotient T x := T.reApplyInnerSelf x / ‖x‖ ^ 2`.

**Minimal residual lemmas for the extreme-case PR** (everything else is
Mathlib): these `iSup`/`iInf` theorems give that the extremum *is an*
eigenvalue, not yet that it equals `eigenvalues 0` (resp. `eigenvalues (n-1)`).
Bridge them with:
1. `⨆ R = eigenvalues 0` (max): `⨆ R` is an eigenvalue (above) so `≤ eigenvalues 0`
   (the max via `eigenvalues_antitone`), and `≥` because every eigenvector's
   Rayleigh value equals its eigenvalue and sits under the `⨆`
   (`hasEigenvalue_eigenvalues` + `le_ciSup`). Dual for `⨅ R = eigenvalues (n-1)`.
2. domain-monotonicity of `⨆`/`⨅` under `H_i ⊆ ℂⁿ` (`ciSup_le_ciSup` /
   `le_ciInf` family) — this is the whole content of the inequality.
3. `Matrix.IsHermitian → LinearMap.IsSymmetric` of `toEuclideanLin`, and that
   the principal submatrix's operator equals `A`'s operator restricted to `H_i`.

## 5. Proposed Lean statement (DRAFT — not yet build-checked)

Stated abstractly over monotone enumerations to decouple from the sorting
obligation (route 1-recommended above). **This has not been run through the
compiler** (Docker pool full); treat as a target to lift into
`proofs/Proofs/CauchyInterlacing.lean` after an API spot-check.

```lean
import Mathlib

open Matrix

/-- One-step Cauchy interlacing. `lamA`/`lamB` are monotone enumerations of the
sorted eigenvalues of `A` and of its principal submatrix `B = A.submatrix …`
(row/col `i` deleted). Stated abstractly over the sorted tuples; the link
"`lamA` is the sorted spectrum of `A`" is a separate obligation. -/
theorem cauchy_interlacing
    {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hA : A.IsHermitian)
    (i : Fin (n+1))
    (lamA : Fin (n+1) → ℝ) (lamB : Fin n → ℝ)
    (hlamA : Monotone lamA) (hlamB : Monotone lamB)
    (hA_spec : -- lamA enumerates A's eigenvalues, sorted
      sorry)
    (hB_spec : -- lamB enumerates (A deleting row/col i)'s eigenvalues, sorted
      sorry)
    (k : Fin n) :
    lamA k.castSucc ≤ lamB k ∧ lamB k ≤ lamA k.succ := by
  sorry
```

The two `hA_spec`/`hB_spec` `sorry`s are placeholders for the spectral linkage;
they must be replaced with concrete `Matrix.IsHermitian.eigenvalues`-based
statements once the sorted-enumeration helper (§2.1) is chosen. **Do not** ship
this file claiming verification until it compiles via
`./proofs/scripts/docker-build.sh Proofs.CauchyInterlacing`.

### §5-revised — matrix-native statement (supersedes §5)

Because `Matrix.IsHermitian.eigenvalues₀` is already a sorted
`Fin (Fintype.card n) → ℝ` (decreasing), state interlacing directly over it on
the matrix — no `Monotone` hypotheses, no abstract enumeration, no sorting
obligation, no operator bridge in the statement. The only modelling choice is
how to present the principal submatrix `B` (`A.submatrix` deleting row/col `i`).
Sketch (decreasing convention `λ 0 ≥ λ 1 ≥ …`):
```lean
-- A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ, hA : A.IsHermitian
-- B := A.submatrix (i.succAbove) (i.succAbove) : Matrix (Fin n) (Fin n) ℂ, hB : B.IsHermitian
-- λ := hA.eigenvalues₀  (Fin (n+1) → ℝ, antitone),  μ := hB.eigenvalues₀ (Fin n → ℝ)
-- Interlacing (decreasing): ∀ k : Fin n, λ k.succ ≤ μ k ∧ μ k ≤ λ k.castSucc
```
The endpoints of this chain are the two extreme cases of §4-verified:
`μ 0 ≤ λ 0` (top) and `λ (last) ≤ μ (last)` (bottom). Proving them goes through
the operator/Rayleigh layer (bridge `hA.eigenvalues₀ 0`/`last` to the Rayleigh
`⨆`/`⨅`). Still **not** build-checked — Docker pool full; lift into
`proofs/Proofs/CauchyInterlacing.lean` and gate on
`./proofs/scripts/docker-build.sh Proofs.CauchyInterlacing`.

> Pin caveat: `eigenvalues₀`/`eigenvalues₀_antitone` are confirmed on Mathlib
> master; re-confirm they are present in the project pin (`v4.26.0`) at build
> time — if absent there, fall back to sorting `eigenvalues` via `Tuple.sort`,
> or use the operator `LinearMap.IsSymmetric.eigenvalues`.

## 6. Recommended next actions (in order)

1. ~~API spot-check~~ **DONE (iter 3)** — see iter-3 box + §4-verified. Operator
   eigenvalues are sorted; extreme Rayleigh signatures pinned; k-th min-max
   confirmed absent.
2. **Formalize the two extreme cases** (§4-verified) — smallest viable first PR;
   the three residual lemmas listed in §4-verified, no new min-max lemma. Good
   Aristotle job when the backend returns. Start from the **operator**
   formulation (§5-revised), not the matrix one.
3. **Build the k-th Courant–Fischer min-max lemma** (§2.2) — the keystone, still
   the only genuine theory gap; land it as its own contribution.
4. **Assemble interlacing** from the min-max lemma + the `dim (S ∩ H_i)` count
   (§3).

## 7. Honesty / scope notes

- Nothing here is machine-checked. No `.lean` shipped.
- The Mathlib-API claims are now spot-checked against Mathlib master
  (docs + source), **not** against the exact pinned commit — re-confirm the
  pin's signatures at build time (names are stable across recent Mathlib but
  the pin is `v4.26.0`).
- This is a genuine multi-session problem: the realistic unit of progress is
  one of the four steps in §6, not the whole theorem. The keystone (step 3)
  is the only piece that is real new theory; steps 2 and 4 are now bookkeeping
  over confirmed Mathlib API.
