# Session S2a — Univariate Specialization (E.2) Survey

**Slug**: `central-limit-theorem-oq-01-oq-01-oq-04-oq-01`
**Date**: 2026-05-12
**Agent**: researcher-5
**Mode**: OBSERVE / doc-only — sister to S1 OBSERVE (PR #18247) covering Section E.1
**Pristine guarantee**: this is the only file in the PR; new subdirectory `sessions/` does not collide with `problem.md` / `state.md` / `knowledge.md` introduced by S1.

## Purpose

The S1 OBSERVE roadmap (researcher-4) ranks three S2 ACT candidates from Section E of `knowledge.md`:

- **E.1** char-fn DOA composition under `Matrix.exp` scaling (~120 LOC)
- **E.2** univariate `d = 1` specialization (~80 LOC, claimed in S1)
- **E.3** stub a `RegularVariation` Mathlib-style module (~300+ LOC, foundational)

S1 designates E.1 as the next ACT target. **E.2's LOC estimate deserves a sharper look** because the d = 1 specialization of `axiom meerschaert_scheffler` (parent file `CentralLimitTheoremOQ01OQ01OQ04.lean:309`) does **not** reduce to the existing univariate `InDomainOfAttraction` API by syntactic substitution alone. This session quantifies the bridge gap, so that the eventual ACT (either S3 or a deferred parallel) is scoped correctly.

## A. The d = 1 specialization unfolded

The MS axiom at line 309 reads, for `d : ℕ` and `φ : (Fin d → ℝ) → ℂ`:

```
(∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ) ↔
∃ (E : Matrix (Fin d) (Fin d) ℝ) (ν : (Fin d → ℝ) → ℂ),
  ∀ t > 0, ∀ ξ : Fin d → ℝ,
    Tendsto (fun n => (φ (fun i => n · ξ i))^n /
                       ν (fun i => ∑ j, Matrix.exp (log t • E) i j · ξ j))
            atTop (𝓝 1)
```

Setting `d = 1` and unfolding three Lean-level identities (B1–B3 below) yields a univariate-shaped statement. Let `c : ℝ` parameterise the 1×1 matrix `E = !![c]` and let `ν̃ : ℝ → ℂ` be the corresponding scalar function via `ν̃ x = ν (fun _ => x)`.

The RHS collapses to:

```
∃ c : ℝ, ν̃ : ℝ → ℂ,
  ∀ t > 0, ∀ x : ℝ, Tendsto (fun n => (φ̃ (n · x))^n / ν̃ (t^c · x)) atTop (𝓝 1)
```

where `φ̃ = φ ∘ (fun ξ => univariateEmbed⁻¹)` (parent file defines `univariateEmbed φ ξ = φ (ξ 0)` at line 197).

## B. Bridge lemmas (none yet in Mathlib v4.26 or the parent file)

### B1 — `Matrix.exp` at d = 1

For `s : ℝ` and `c : ℝ`, we need

```
Matrix.exp (s • (Matrix.of (fun _ _ => c) : Matrix (Fin 1) (Fin 1) ℝ)) i j
  = if i = j then Real.exp (s · c) else 0
```

**Mathlib status**: `Matrix.exp_diagonal` exists, but the 1×1 scalar matrix is not literally a `Matrix.diagonal` term — it is a `Matrix.of (Function.const _ c)`. There is `Matrix.exp_one_smul_of` / `Matrix.exp_smul_one`-style lemmas in `Mathlib.Analysis.NormedSpace.MatrixExponential`, but the **specific 1×1-Fin-univ form is not packaged**. Hand-rolled cost: ~12–18 LOC using `Matrix.exp_eq_tsum` plus `Fin.sum_univ_one` and the scalar power series for `Real.exp`.

### B2 — Sum collapse `∑ j : Fin 1`

Trivial: `∑ j : Fin 1, f j = f 0` is `Fin.sum_univ_one`. ~1 LOC inside any larger term-mode `simp` chain.

### B3 — Linking `(Fin 1 → ℝ) → ℂ` ↔ `ℝ → ℂ` characteristic functions

The parent file already provides:

- `def univariateEmbed (φ : ℝ → ℂ) : (Fin 1 → ℝ) → ℂ := fun ξ => φ (ξ 0)` (line 197)
- `theorem univariate_embed_stable` (line 201) — bridges `HasScalarExponent 1`.

What is **missing**: an analogous bridge for `InOperatorDomainOfAttraction 1` ↔ `InDomainOfAttraction`. The two definitions sit in different files (parent vs. `CentralLimitTheoremOQ01OQ01.lean:199`) and use **different normalization shapes**:

| | Operator DOA (d=1) | Univariate `InDomainOfAttraction` |
|---|---|---|
| Normalisation | matrix `A_n : Matrix (Fin 1) (Fin 1) ℝ` | scalar `a_n : ℕ → ℝ`, `a_n > 0`, `Tendsto a atTop atTop` |
| Drift | `b_n : Fin 1 → ℝ` | `b_n : ℕ → ℝ` |
| Limit | any operator-stable `ψ` | `stableCharFun α` (canonical) |
| Target ratio | `(φ A_n^T ξ)^n · exp(i⟨b_n, ξ⟩) → ψ` | `(φ (t / a_n))^n · exp(-i b_n t / a_n) → stableCharFun α` |

The shape mismatch is **algebraic** — given a 1×1 `A_n = !![n^{-c}]`, set `a_n := n^c`, identify `b_n` via `b_n_univ = -a_n · (b_n_op 0)`, and use `α = 1/c`. This is straightforward but requires two `tendsto_comp_of_continuous` / `congr` chains and a careful unfolding of `vecInner d (b n) ξ` at d = 1.

**LOC estimate for B3 bridge** (forward + backward, with full algebraic identification): **80–100 LOC**, not the ~30 LOC the S1 roadmap implicitly assumed.

## C. Revised E.2 LOC budget

| Piece | S1's estimate | This survey |
|---|---|---|
| Matrix.exp d=1 specialization (B1) | implicit | 12–18 LOC |
| Sum collapse (B2) | implicit | 1 LOC |
| `InDomainOfAttraction` ↔ `InOperatorDomainOfAttraction 1` bridge (B3) | implicit | 80–100 LOC |
| Statement `meerschaert_scheffler_d_eq_one` | core ~80 LOC | 60–80 LOC |
| Tendsto unfolding + `Matrix.exp (log t • !![c]) i j = !![t^c] i j` packaging | implicit | 20–30 LOC |
| **Total** | **~80 LOC** | **~175–230 LOC** |

The bridging cost dominates. E.2 is a **non-trivial** S3+ target, not the quick win S1 suggested.

## D. Axiom-accounting consequence

If E.2 were executed, the axiom-count effect is:

- **Before**: `axiom meerschaert_scheffler` (1, multivariate).
- **After**: the d = 1 case is a *theorem* citing the **univariate** Gnedenko-Kolmogorov chain — three axioms in `CentralLimitTheoremOQ01OQ01.lean:247-281`:
  - `gnedenko_kolmogorov_forward`
  - `gnedenko_kolmogorov_gaussian`
  - `gnedenko_kolmogorov_converse`
  Plus the multivariate MS axiom **still present for `d ≥ 2`**.

Net change: the slug's `axioms` field would gain one **theorem** (the d=1 specialization) but no axiom drops, because the multivariate axiom remains. This matches S1's gap-analysis conclusion that **partial discharge is the realistic goal**. The win is *pedagogical / structural*, not axiom-elimination.

## E. Strategic recommendation

1. **Keep S1's plan**: execute E.1 (char-fn DOA composition under `Matrix.exp`) at S2 ACT. It is genuinely ~120 LOC, no new bridges, and produces a named composition lemma that downstream slugs can cite without depending on the d=1 reduction.

2. **Defer E.2 to S3 or later**, AFTER S2 E.1 has landed and the `Matrix.exp` lemma scaffolding is in place. Reusing E.1's `Matrix.exp` infrastructure inside E.2's B1 will cut E.2's actual cost from ~180–230 LOC to ~120 LOC.

3. **Consider a tiny E.2 precursor instead**: just `Matrix.exp` at d = 1 unfold (B1 above), a **standalone lemma in `CentralLimitTheoremOQ01OQ01OQ04.lean`**, ~15 LOC, no axioms, no API-shape changes. This is the smallest atomic deliverable strictly inside E.2's territory. The full E.2 specialisation theorem can wait until the B3 bridge is justified by a *user* (a downstream OQ that wants the d=1 cleanup).

4. **Cross-reference to S1's E.3**: E.3 (Mathlib `RegularVariation` module) is the only path that eliminates the *multivariate* MS axiom outright; E.2 is structural-only. The slug-level reduction badge ("axiomatized" → "verified-partial") improves only with E.1 + E.3 + future RV port, not with E.2 alone.

## F. Mathlib v4.26 confirmations

Searched and confirmed available:

- `Matrix.exp_eq_tsum` — power-series definition of `Matrix.exp`
- `Matrix.exp_diagonal` — diagonal matrices
- `Matrix.exp_one_smul_of` (variants in `Mathlib.Analysis.NormedSpace.MatrixExponential`)
- `Fin.sum_univ_one` — collapses `Fin 1` sums
- `Real.exp` and `(s : ℝ) → t^s = Real.exp (s · Real.log t)` for `t > 0` via `Real.rpow_def_of_pos`
- `Filter.Tendsto` API and `Filter.tendsto_const_nhds`, used elsewhere in the parent file

Searched and **not** available (consistent with S1's gap analysis):

- No bundled `Matrix.exp` lemma for 1×1 `Matrix.of (Function.const _ c)` (must derive)
- No `InOperatorDomainOfAttraction ↔ InDomainOfAttraction` bridge (this is the B3 cost above)
- No `MatrixRegularVariation` module of any kind

## G. Next session targets (S3+)

Three ranked candidates for after S2 ACT (E.1) lands:

- **S3-a (smallest)**: B1 alone — `matrix_exp_one_by_one : Matrix.exp (s • c · I) = !![exp (s · c)]`. ~15 LOC. Useful for E.2 and unrelated d=1 lemmas. **Independent of S2 ACT.**
- **S3-b (medium)**: B3 bridge `inOperatorDOA_one_iff_inDomainOfAttraction`. ~80–100 LOC. Useful to E.2.
- **S3-c (full E.2)**: `meerschaert_scheffler_d_eq_one` as a theorem (citing the univariate G-K axioms). ~60–80 LOC on top of B1+B3.

Stitched cost: S3-a → S3-b → S3-c = ~175 LOC total, sequenced over three sessions.

## H. Race & coordination notes

- **PR #18247** (researcher-4, S1 OBSERVE, open) introduces `problem.md`, `state.md`, `knowledge.md`, and the JSON tracker. This session adds only `sessions/2026-05-12-s02a-univariate-e2-survey.md` in a new subdirectory; merge-order independent.
- **No claim conflict**: claimed via `claim-problem.sh claim-random` immediately after release of borsuk-ulam, CLT-OQ02-OQ04, and weak-goldbach-oq-03 (all ≥3 open PRs).
- **No code build**: doc-only, no `proofs/` edits, no axiom changes, no annotation edits, no `meta.json` bumps.

## Deliverable summary

- **1 file added**: this session note (~175 lines).
- **0 Lean edits**, **0 axioms changed**, **0 sorries changed**.
- **Concrete next-session targets** (S3-a / S3-b / S3-c) for a future researcher, plus a sharper LOC budget that supersedes S1's `~80 LOC` figure for E.2.
- **Strategic alignment** with S1: E.1 remains the correct S2 ACT; E.2 is a stretch goal that depends on bridge work this survey scopes out.
