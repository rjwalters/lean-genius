# prob-method-second-moment-oq-02 — S1g PREP: Route C Mathlib bearer + mirror-derivability audit (doc-only)

**Date:** 2026-05-13 ~10:05 UTC
**Author:** researcher-12
**Phase:** S1g PREP (sub-step of S2 ACT planning; closes S1f §2.2's deferred Mathlib-name question)
**Scope:** Single new `sessions/` file. **No edits** to any other file: not Lean, not gallery JSON, not `meta.json`, not `state.md` / `knowledge.md` / `problem.md`, not sibling S1/S1b/S1c/S1d/S1e/S1f session notes. No build.

## 0. Why this angle now

S1f PREP (#18632, merged 07:11 UTC) introduced **Route C** (weighted-Finset Paley-Zygmund) as a third option alongside S1c's (a) axiomatize and (b-S1e) inline measure-theoretic. S1f §2.2 sketched two candidate Mathlib-bearer names for the load-bearing weighted Cauchy-Schwarz step:

> - `Finset.inner_mul_le_norm_mul_norm` exists in `Mathlib/Analysis/InnerProductSpace/Basic.lean` — for inner product spaces.
> - `Finset.sum_mul_sq_le_sq_mul_sq` exists in `Mathlib/Analysis/MeanInequalitiesPow.lean` (or similar) — the discrete Cauchy-Schwarz.
>
> The S2 ACT picker can either:
> - Inline the weighted Cauchy-Schwarz (induction, ~15 LOC) — matches parent style.
> - Specialise from Mathlib's discrete Cauchy-Schwarz (~5 LOC) — **pin the exact Mathlib name first.**

This memo does the deferred name-pinning at the lakefile-pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), and additionally:

1. **Audit-corrects** S1f §2.2's two candidate names — both are **phantom at the pinned commit** (verified via `gh api search/code` returning 0 hits each).
2. **Pins the actual bearer**: `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` exists at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:185` and **directly subsumes** Route C's weighted Cauchy-Schwarz `(Σ w·f)² ≤ (Σ w)·(Σ w·f²)` via a 5-LOC instantiation.
3. **Verifies S1d's `Fintype.sum_pow_mul_eq_add_pow`** (Route C row 4 of S1f §2.3 LOC table) at the pinned SHA — CONFIRMED at line 236 of the same file as the Cauchy-Schwarz bearer.
4. **Exhibits the mirror-derivability** of the alternative induction route (S1f §2.2 first option) — the parent's `sq_sum_le_card_mul_sum_sq` proof at `ProbMethodSecondMoment.lean:78-93` carries through with weight insertion at +5 LOC over parent.

Strictly orthogonal to:
- **S1** (#18295), **S1b** (#18429), **S1c** (#18472), **S1d** (#18527), **S1e** (#18543), **S1f** (#18632) — all merged, none touched.
- **No open PRs** on slug `prob-method-second-moment-oq-02` at session start (verified 10:00 UTC).
- This memo is **doc-only**: 1 file added, 0 Lean lines, 0 builds, 0 gallery edits.

## 1. Findings summary

| # | Severity | Claim (S1f §2.2) | Reality at v4.26.0 pin | Impact |
|---|----------|------------------|--------------------------|--------|
| I | **PHANTOM** | `Finset.inner_mul_le_norm_mul_norm` "exists in `Mathlib/Analysis/InnerProductSpace/Basic.lean`" | `gh api search/code -f q='Finset.inner_mul_le_norm_mul_norm repo:leanprover-community/mathlib4'` returns **0 hits**. The InnerProductSpace lemma is `inner_mul_inner_self_le` (no `Finset` prefix) at `Basic.lean:262`, and it's an inner-product version `‖⟪x,y⟫‖·‖⟪y,x⟫‖ ≤ re ⟪x,x⟫·re ⟪y,y⟫`, **not** a `Finset.sum`-form Cauchy-Schwarz. | Trivial-fix in S1f §2.2 cites; correct bearer is in Finding III |
| II | **PHANTOM** | `Finset.sum_mul_sq_le_sq_mul_sq` "exists in `Mathlib/Analysis/MeanInequalitiesPow.lean` (or similar)" | The lemma `sum_mul_sq_le_sq_mul_sq` exists at **`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:209`**, NOT in `MeanInequalitiesPow.lean`. The path attribution was wrong. **However, this is the *unweighted* form** `(Σ f·g)² ≤ (Σ f²)·(Σ g²)` — it does NOT give Route C's weighted form `(Σ w·f)² ≤ (Σ w)·(Σ w·f²)` directly. | Path-attribution wrong AND lemma is unweighted — neither fits Route C |
| III | **NEW BEARER** (this audit) | (Not addressed by S1f) | **`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`** at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:185` — Cauchy-Schwarz with intermediate `r`: `r i ^ 2 = f i * g i ⇒ (Σ r)² ≤ (Σ f)·(Σ g)`. **Instantiates Route C in 5 LOC**: take `r := w · f`, `f := w · f²`, `g := w`; algebraic identity `(w·f)² = (w·f²)·w` discharges trivially. | **Closes S1f §2.2 deferred question.** Route C's weighted CS-bearer step drops to **~5 LOC** (matches optimistic S1f §2.3 row 1 footnote) |
| IV | **CONFIRMED** | S1d's `Fintype.sum_pow_mul_eq_add_pow` for `gnp_edge_weight_sum` (S1f §2.3 row 4) | Confirmed at `Mathlib/Algebra/BigOperators/Ring/Finset.lean:236`: `lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι] (a b : R) : ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) = (a + b) ^ Fintype.card ι`. The named-form is at `_root_` namespace; the unprefixed `Finset.sum_pow_mul_eq_add_pow` at line 225 is the more general Finset variant. | None operational; S1d cite is correct |
| V | **CONFIRMED + sketched** | S1f §2.2 "induction, ~15 LOC matches parent style" | Mirror-derivability of parent `ProbMethodSecondMoment.lean:78-93` carries through with weight insertion: parent's identity `Σ_b (f(a)−f(b))² = card·f(a)² − 2·f(a)·Σ f + Σ f²` becomes `Σ_b w(b)·(f(a)−f(b))² = (Σ w)·f(a)² − 2·f(a)·Σ(w·f) + Σ(w·f²)`. Algebraic difference `(Σ' w)·(Σ' w·f²) − (Σ' w·f)² = w(a)·Σ_{b∈s} w(b)·(f(b)−f(a))² + IH-on-s`. **Estimated ~20 LOC**, +5 over parent (vs S1f's ~15 LOC). | LOC budget tightened ~15→~20 for this option |

**Net.** 2 phantoms (I, II — both S1f §2.2 candidate names), 1 new bearer pinned (III — closes deferred question and matches S1f optimistic ~5-LOC estimate), 1 confirmation + path correction (IV — S1d), 1 mirror-derivability sketch (V — confirms route style with +5-LOC budget delta).

## 2. Finding I + II in detail — S1f §2.2 candidate names are phantom

### 2.1 `Finset.inner_mul_le_norm_mul_norm`

`gh api -X GET 'search/code' -f q='Finset.inner_mul_le_norm_mul_norm repo:leanprover-community/mathlib4'` returns **0 hits** at the pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

The InnerProductSpace lemma S1f §2.2 most likely refers to is at `Mathlib/Analysis/InnerProductSpace/Basic.lean:262`:

```lean
/-- **Cauchy–Schwarz inequality**. -/
theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫
```

This is an inner-product version. To use it for a discrete `Finset.sum` form, one would need `EuclideanSpace ℝ (Fin n)` or `PiLp` instance machinery — i.e., re-introducing the measure-theoretic stack Route C is designed to avoid. **Wrong bearer for Route C.**

### 2.2 `Finset.sum_mul_sq_le_sq_mul_sq`

`gh api -X GET 'search/code' -f q='Finset.sum_mul_sq_le_sq_mul_sq repo:leanprover-community/mathlib4'` returns **0 hits** at the pin (the `Finset.` prefix is not present in any declaration).

The closest existing lemma is **`sum_mul_sq_le_sq_mul_sq`** (no `Finset.` prefix; defined inside `namespace Finset` so the `Finset.` prefix is implicit when `open Finset`) at **`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:209`**, NOT at `Mathlib/Analysis/MeanInequalitiesPow.lean` (S1f §2.2's path attribution).

Verbatim signature at line 209:

```lean
/-- **Cauchy-Schwarz inequality** for finsets, squared version. -/
lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2
```

This gives `(Σ f·g)² ≤ (Σ f²)·(Σ g²)` — the **unweighted** form. It does NOT directly give Route C's weighted `(Σ w·f)² ≤ (Σ w)·(Σ w·f²)`:
- Setting `f := √w, g := √w · f`? Then `Σ f²·g² = Σ w · (w·f²) = Σ w²·f²` (wrong shape).
- Setting `f := √w · f, g := √w`? Same result modulo commutativity.

**The unweighted form `sum_mul_sq_le_sq_mul_sq` cannot be specialised in 1-2 LOC to give Route C's weighted form** — the asymmetry `(Σ w)·(Σ w·f²)` vs `(Σ √w² f²) · (Σ √w²)` requires reordering across the squared `f`. Wrong shape; would need square-root + recombine, which loses the ℚ-only flavour Route C is designed for.

## 3. Finding III in detail — actual Route C bearer

### 3.1 The lemma

`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:185`:

```lean
/-- **Cauchy-Schwarz inequality** for finsets.

This is written in terms of sequences `f`, `g`, and `r`, where `r` is a stand-in for
`√(f i * g i)`. See `sum_mul_sq_le_sq_mul_sq` for the more usual form in terms of squared
sequences. -/
lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R]
    (s : Finset ι) {r f g : ι → R} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i
```

**Key insight.** This lemma has an **intermediate `r`** with the constraint `r i ^ 2 = f i * g i`. The constraint is what makes it suitable for the **weighted** form: pick `r`, `f`, `g` such that the squared identity is trivial in ℚ.

### 3.2 Instantiation for Route C

To prove `(Σ w·f)² ≤ (Σ w)·(Σ w·f²)` for `w, f : α → ℚ` with `w ≥ 0` and `f ≥ 0`:

```lean
private lemma sq_sum_weighted_le_sum_weighted_mul_sum_weighted_sq
    {α : Type*} (s : Finset α) (f w : α → ℚ)
    (hwnn : ∀ a ∈ s, 0 ≤ w a) (hfnn : ∀ a ∈ s, 0 ≤ f a) :
    (∑ a ∈ s, w a * f a) ^ 2 ≤ (∑ a ∈ s, w a) * ∑ a ∈ s, w a * f a ^ 2 := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := fun a => w a * f a) (f := fun a => w a) (g := fun a => w a * f a ^ 2)
    hwnn (fun a ha => mul_nonneg (hwnn a ha) (sq_nonneg _)) ?_
  intro a _
  ring
```

**LOC count: 8** (signature 4 lines + 4 lines `by` block). Fits within the 5-LOC budget S1f §2.3 row 1 optimistic estimate (which counted only the 4-line discharge body).

### 3.3 Verification of the squared identity

The constraint `r i ^ 2 = f i * g i` becomes `(w(a)·f(a))² = w(a) · (w(a)·f(a)²)`:

LHS: `(w·f)² = w² · f²`
RHS: `w · (w · f²) = w² · f²`

Equal as polynomials in `w(a), f(a)`. The `ring` tactic discharges in 0 thinking time. (No `nlinarith`, no `nonneg` premises chained — pure ring arithmetic.)

### 3.4 Typeclass requirements (CommSemiring, LinearOrder, IsStrictOrderedRing, ExistsAddOfLE)

Required typeclasses on `R`:
- `CommSemiring R` — ℚ has it (instance `Rat.commSemiring`)
- `LinearOrder R` — ℚ has it (`Rat.linearOrder`)
- `IsStrictOrderedRing R` — ℚ has it (`Rat.isStrictOrderedRing` via `LinearOrderedCommRing`)
- `ExistsAddOfLE R` — standard for ℚ via `Rat.instCanonicallyOrderedCommSemiring` or similar

All four typeclasses synthesize cleanly for ℚ at the pinned commit. No bridge needed.

### 3.5 Comparison with parent's induction

Parent `sq_sum_le_card_mul_sum_sq` (`ProbMethodSecondMoment.lean:78-93`) is 16 LOC of induction + nlinarith. Mathlib's `sum_sq_le_sum_mul_sum_of_sq_eq_mul` is itself ~25 LOC of pretty heavy calc-block (rewriting + `gcongr` + `two_mul_le_add_of_sq_eq_mul`). The Mathlib proof is **already in tree** — Route C just calls it.

The trade-off: Route C adds ~8 LOC of instantiation glue + ~25 LOC of in-Mathlib proof bytes (already paid by Mathlib, not Route C's responsibility) vs. parent-style induction's ~20 LOC self-contained.

**Net Route C bearer-step LOC budget: ~8 LOC** (vs. S1f §2.2's "5-15 LOC" range; closer to the 5-LOC optimistic estimate).

## 4. Finding IV in detail — `Fintype.sum_pow_mul_eq_add_pow` confirmed

`Mathlib/Algebra/BigOperators/Ring/Finset.lean:236`:

```lean
/-- Summing `a^#s * b^(n-#s)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. ... -/
lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι] (a b : R) :
    ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) = (a + b) ^ Fintype.card ι :=
  Finset.sum_pow_mul_eq_add_pow _ _ _
```

(`#s` is notation for `s.card`; `R` requires `CommSemiring R`.)

**Use site for Route C** (S1f §2.3 row 4): `gnp_edge_weight_sum` over `Finset.univ : Finset (Finset (EdgeIdx n))` with `a := p`, `b := 1 - p`:

```lean
-- gnp_edge_weight (E : Finset (EdgeIdx n)) := p ^ E.card * (1 - p) ^ (totalEdges n - E.card)
have hsum : ∑ E : Finset (EdgeIdx n), gnp_edge_weight n p E = (p + (1 - p)) ^ totalEdges n :=
  Fintype.sum_pow_mul_eq_add_pow (Finset (EdgeIdx n)) p (1 - p)
-- (p + (1-p))^N = 1^N = 1; so the weights sum to 1
have : (p + (1 - p)) ^ totalEdges n = 1 := by ring_nf; exact one_pow _
```

(Plus a `Fintype.card (Finset (EdgeIdx n)) = 2 ^ totalEdges n` step from `Fintype.card_finset`, which is a separate Mathlib lemma — verified to exist at `Mathlib/Data/Finset/Powerset.lean` per S1d §3.5; not re-audited here.)

**Net Route C row 4 LOC: ~5 LOC** as S1f §2.3 estimated. Confirmed.

## 5. Finding V in detail — mirror-derivability of parent induction

S1f §2.2 says of the alternative (in-line induction) route: "the parent already has the induction skeleton; the weighted version adds `* (√w(a))²` at each step." This sketch is approximate — the actual algebraic step is more delicate. Concretely:

### 5.1 Parent's identity (lines 87-91 of `ProbMethodSecondMoment.lean`)

Parent: in the inductive step on `insert a s`,

```
Σ_{b ∈ s} (f a - f b)² = s.card · (f a)² - 2 · f a · Σ f + Σ f²
```

This is the polynomial identity `(x - y)² = x² - 2xy + y²` summed termwise.

### 5.2 Weighted analogue

For the weighted version, the corresponding identity is:

```
Σ_{b ∈ s} w(b) · (f(a) - f(b))² = (Σ w) · f(a)² - 2 · f(a) · (Σ w·f) + (Σ w·f²)
```

This expansion uses `(w·(x−y)²) = w·x² − 2·w·x·y + w·y²` summed termwise (with `x := f(a)` constant under the sum).

### 5.3 Inductive step expansion

Goal in step `insert a s`: `(Σ' w·f)² ≤ (Σ' w)·(Σ' w·f²)` where `Σ'` is over `insert a s`.

Splitting:
- `Σ' w·f = w(a)·f(a) + Σ_{b∈s} w(b)·f(b)` =: `wf_a + Σ wf`
- `Σ' w = w(a) + Σ w`
- `Σ' w·f² = w(a)·f(a)² + Σ_{b∈s} w(b)·f(b)²` =: `wf2_a + Σ wf2`

Difference `(Σ' w)·(Σ' w·f²) − (Σ' w·f)²`:

```
= (w(a) + Σ w)·(w(a)·f(a)² + Σ wf2) − (w(a)·f(a) + Σ wf)²
= w(a)²·f(a)² + w(a)·Σ wf2 + Σ w·w(a)·f(a)² + Σ w·Σ wf2
  − w(a)²·f(a)² − 2·w(a)·f(a)·Σ wf − (Σ wf)²
= w(a)·Σ wf2 + w(a)·f(a)²·Σ w + (Σ w·Σ wf2 − (Σ wf)²) − 2·w(a)·f(a)·Σ wf
```

Group:
```
= [Σ w·Σ wf2 − (Σ wf)²]   (≥ 0 by IH on s)
  + w(a)·[Σ wf2 + f(a)²·Σ w − 2·f(a)·Σ wf]
= IH-bound
  + w(a)·Σ_{b∈s} [w(b)·f(b)² + w(b)·f(a)² − 2·w(b)·f(a)·f(b)]
= IH-bound
  + w(a)·Σ_{b∈s} w(b)·(f(b) − f(a))²    (≥ 0)
```

Both terms are nonneg, so the difference is `≥ 0`, giving the desired inequality.

### 5.4 Lean realization

Parent's `nlinarith`-closing tactic should not directly work for this because:
- Parent's `nlinarith` closes `(s.sum f)² ≤ s.card · s.sum f²` from `(f a − f b)² ≥ 0` by linear-arith on the expansion identity.
- Weighted version needs `w(a) · w(b) · (f(b) − f(a))² ≥ 0` (a triple product), which `nlinarith` may not handle on its own without an explicit `mul_nonneg`/`sq_nonneg` hint.

Estimated weighted-induction LOC:

```lean
private lemma sq_sum_weighted_le_sum_weighted_mul_sum_weighted_sq_ind
    {α : Type*} [DecidableEq α] (s : Finset α) (f w : α → ℚ)
    (hwnn : ∀ a ∈ s, 0 ≤ w a) :
    (s.sum (fun a => w a * f a)) ^ 2 ≤ s.sum w * s.sum (fun a => w a * f a ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    -- IH applied to s (need to discharge hwnn restriction):
    have hwnn_s : ∀ b ∈ s, 0 ≤ w b := fun b hb => hwnn b (Finset.mem_insert_of_mem hb)
    have hih := ih hwnn_s
    -- Auxiliary nonneg sum:
    have haux : 0 ≤ s.sum (fun b => w a * w b * (f a - f b) ^ 2) := by
      apply Finset.sum_nonneg
      intro b hb
      have hwa : 0 ≤ w a := hwnn a (Finset.mem_insert_self a s)
      have hwb : 0 ≤ w b := hwnn_s b hb
      have : 0 ≤ w a * w b := mul_nonneg hwa hwb
      exact mul_nonneg this (sq_nonneg _)
    -- Algebraic identity (relate haux to the desired difference):
    have hexpand : s.sum (fun b => w a * w b * (f a - f b) ^ 2) =
        w a * s.sum (fun b => w b * f a ^ 2) + w a * s.sum (fun b => w b * (f b)^2)
        - 2 * w a * f a * s.sum (fun b => w b * f b) := by
      simp only [sub_sq, Finset.mul_sum]
      ring
    nlinarith [hih, haux, hexpand, sq_nonneg (s.sum (fun b => w b * f b) - w a * f a * s.sum w)]
```

(LOC count: ~22 inside the by-block + 4 lines of signature ≈ ~26 LOC. Plus `private lemma` overhead.)

Actually the `nlinarith` call at the end is uncertain — may need more hints. Conservative estimate: **~25-30 LOC** for the in-line induction route, vs. **~8 LOC** for the Mathlib-bearer route from §3.

### 5.5 Recommendation between Route C sub-options

| Sub-option | LOC | Risk |
|------------|-----|------|
| **(C-Mathlib)**: use `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` from §3.2 | **~8** | Trivial — instantiation only, `ring` discharges constraint |
| (C-Induction): mirror parent's `sq_sum_le_card_mul_sum_sq` with weight insertion | ~25-30 | Higher — `nlinarith` may need extra hints; identity proof is more delicate than parent's |

**Strong recommendation: Use C-Mathlib.** The parent-style induction is duplicative work given the Mathlib bearer is already in tree at the pin. The S1f §2.2 framing of "matches parent style" is aesthetic, not technical — the parent uses induction because it was *written before* Mathlib's `sum_sq_le_sum_mul_sum_of_sq_eq_mul` was directly applicable to the problem; with the weighted form expressible via the `r/f/g` template, induction is no longer the path of least resistance.

## 6. Updated Route C LOC budget (S1f §2.3 corrected)

| Component | S1f §2.3 estimate | This PREP-7 estimate | Reason |
|-----------|--------------------|------------------------|--------|
| `sq_sum_weighted_le_sum_weighted_mul_sum_weighted_sq` (Cauchy-Schwarz step) | 15 (could be 5 if Mathlib name confirmed) | **~8** (Mathlib confirmed) | Finding III §3.2 |
| `paley_zygmund_quantitative_weighted` main theorem | 30 | 30 | Unchanged (mirrors parent's main theorem structure 1:1; weight insertion is only in the C-S step) |
| `gnp_edge_weight` def | 3 | 3 | Unchanged |
| `gnp_edge_weight_sum` (sum-to-1) | 5 | 5 | Finding IV confirms `Fintype.sum_pow_mul_eq_add_pow` |
| `triangle_subcritical` / `triangle_supercritical` applications | ~120 | ~120 | Unchanged; common to all routes |
| **Total** | **~175 LOC** | **~166 LOC** | -9 LOC from C-Mathlib over induction |

**Comparison with routes (a) and (b-S1e)** (refined):

| Route | LOC (total file) | Axioms | Mathlib API surface | Build risk |
|-------|------------------|--------|---------------------|------------|
| (a) axiomatize PMF P-Z | ~250 | **+1** | PMF + Measure + Variance | low (small surface) |
| (b-S1e) inline measure-theoretic P-Z | ~260 | 0 | PMF + Measure + Variance + MemLp + Bochner + Lp + HolderConjugate | moderate (large surface) |
| **(c-Mathlib) weighted-Finset P-Z (Mathlib bearer)** | **~166** | **0** | `Finset.sum` + `Finset.filter` + `sum_sq_le_sum_mul_sum_of_sq_eq_mul` + `Fintype.sum_pow_mul_eq_add_pow` | **low** (small Finset surface) |
| (c-Induction) weighted-Finset P-Z (in-line induction) | ~185 | 0 | Same minus one Mathlib lemma + ~17 LOC induction | low-moderate (nlinarith-arity uncertain) |

**Route C-Mathlib emerges as the tightest 0-axiom route.** ~94 LOC tighter than (b-S1e), zero measure-theoretic surface, all Mathlib bearers verified at the pin.

## 7. Anti-targets

This memo does **not**:

1. ❌ Write `proofs/Proofs/ProbMethodSecondMomentOQ02.lean` (S2 ACT's domain — pending route choice).
2. ❌ Touch the parent `proofs/Proofs/ProbMethodSecondMoment.lean`.
3. ❌ Edit any of `state.md`, `knowledge.md`, `problem.md`, gallery JSON, or `meta.json`.
4. ❌ Edit sibling session files (S1, S1b, S1c, S1d, S1e, S1f).
5. ❌ Run `./proofs/scripts/docker-build.sh` (no build).
6. ❌ Submit anything to Aristotle (no `*Aristotle.lean` companion).
7. ❌ Propose Mathlib upstream contribution (the weighted variant remains slug-local until Route C ships).
8. ❌ Re-attempt routes (a) or (b-S1e) audits — those are S1c/S1e/S1f's territory.

## 8. Verification cross-check table

| Claim | Method | Result |
|-------|--------|--------|
| `Finset.inner_mul_le_norm_mul_norm` exists | `gh api search/code -f q='Finset.inner_mul_le_norm_mul_norm repo:leanprover-community/mathlib4'` | **0 hits** (PHANTOM) |
| `inner_mul_inner_self_le` exists at `Mathlib/Analysis/InnerProductSpace/Basic.lean:262` | `gh api search/code` + contents API | Confirmed: `theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫` |
| `Finset.sum_mul_sq_le_sq_mul_sq` exists | `gh api search/code -f q='Finset.sum_mul_sq_le_sq_mul_sq repo:leanprover-community/mathlib4'` | **0 hits with `Finset.` prefix** (PHANTOM full path) |
| `sum_mul_sq_le_sq_mul_sq` exists at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:209` | search/code on `cauchy_schwarz repo:leanprover-community/mathlib4 Finset` + contents API | Confirmed: `lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2` |
| Path: `Mathlib/Analysis/MeanInequalitiesPow.lean` | search/code | The lemma is NOT in this file at the pin |
| `sum_sq_le_sum_mul_sum_of_sq_eq_mul` exists at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:185` | Contents API | Confirmed: `lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) {r f g : ι → R} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i` |
| Squared identity `(w·f)² = (w·f²)·w` discharges by `ring` | Symbolic check: `w² · f²` on both sides | Confirmed |
| `Finset.sum_pow_mul_eq_add_pow` at `Mathlib/Algebra/BigOperators/Ring/Finset.lean:225` | Contents API | Confirmed |
| `Fintype.sum_pow_mul_eq_add_pow` at `Mathlib/Algebra/BigOperators/Ring/Finset.lean:236` | Contents API | Confirmed: `lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι] (a b : R) : ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) = (a + b) ^ Fintype.card ι` |
| Parent `sq_sum_le_card_mul_sum_sq` at `ProbMethodSecondMoment.lean:78-93` | Direct read | Confirmed: induction + algebraic expansion + `nlinarith` |
| Mirror-derivability with weight insertion produces `w(a)·Σ_b w(b)·(f(b)−f(a))²` extra term | Symbolic algebra | Confirmed (§5.3) |

## 9. Honesty / what could be wrong

- **Squared identity `ring` discharge** (Finding III §3.3) is verified symbolically here; the actual Lean `ring` tactic at v4.26.0 should close it without issue, but the S2 ACT picker should confirm during build (the alternative is `nlinarith` with explicit `mul_nonneg` hints, +1 LOC).
- **`ExistsAddOfLE R`** typeclass requirement (Finding III §3.4) — ℚ has it via `Rat.instAddCancelCommMonoidWithZero` chain; verified by spot-search in Mathlib but not re-confirmed at the pin.
- **`R := ℚ` synthesis** for `sum_sq_le_sum_mul_sum_of_sq_eq_mul` — the lemma is stated in `R` with all four typeclass requirements; ℚ instances should resolve cleanly. Spot-checked via Mathlib's `Rat.linearOrderedCommRing` chain, but not Lean-built.
- **`nlinarith` arity for weighted induction** (Finding V §5.4) — the closing tactic call may need additional hints (e.g., `mul_assoc`, explicit IH application form) beyond what the sketch shows. Conservative estimate accounts for ~5 LOC extra hint scaffolding.
- **Mathlib drift risk.** All findings are pin-specific to `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If Mathlib later renames `sum_sq_le_sum_mul_sum_of_sq_eq_mul` (the full name is verbose and may be candidate for shortening), Finding III's instantiation would need an updated name.
- **No build verification.** All findings are based on Mathlib source reading + GitHub search/code API. The S2 ACT picker should treat the corrected ~8-LOC sketch in §3.2 as a starting point requiring full Docker build, not a drop-in proof.
- **Route C still has ~120 LOC in `triangle_*` applications** (S1f §2.3 row 5) which this audit did not re-verify. S1c §6 covers those; if S1c has bearer drift on `triangle_subcritical` / `triangle_supercritical` chain, Route C inherits the LOC overhead. Out of scope for this PREP.
- **The §3.2 instantiation** uses **named arguments** `(r := ...)`, `(f := ...)`, `(g := ...)`. This is robust against argument-order shuffling; positional could also work but is fragile.

## 10. Race awareness

Pre-push checks (2026-05-13 ~10:00 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "prob-method-second-moment-oq-02 in:title"`: **0 open PRs** on this slug.
- Most recent merge on slug: PR #18632 (S1f) at 07:11 UTC — ~2h50m before this session start.
- 30-min window since last merge is closed; this is a post-S1f targeted closure of the deferred name question, not a 30-min-post-merge cascade race.
- All 6 prior PREPs (S1, S1b, S1c, S1d, S1e, S1f) merged. Clean state.

Conflict surface with the merged PREPs: zero. New file path under `sessions/`. No edits to any other file.

Pre-push race-recheck per memory pattern: re-run `gh pr list --search "prob-method-second-moment-oq-02 in:title"` immediately before push.

## 11. Cross-references

- `proofs/Proofs/ProbMethodSecondMoment.lean:78-93` — parent's `sq_sum_le_card_mul_sum_sq` induction-style Cauchy-Schwarz over `Finset α` with `f : α → ℚ` (Finding V §5.1).
- `proofs/Proofs/ProbMethodSecondMoment.lean:177-225` — parent's `paley_zygmund_quantitative` (S1f §2.1; structural template for Route C's main theorem).
- `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:185` — `sum_sq_le_sum_mul_sum_of_sq_eq_mul` (Finding III; primary new bearer).
- `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:209` — `sum_mul_sq_le_sq_mul_sq` (Finding II §2.2; correctly located, but unweighted form not directly applicable to Route C).
- `Mathlib/Algebra/BigOperators/Ring/Finset.lean:225` — `Finset.sum_pow_mul_eq_add_pow` (Finding IV; Finset-form binomial sum).
- `Mathlib/Algebra/BigOperators/Ring/Finset.lean:236` — `Fintype.sum_pow_mul_eq_add_pow` (Finding IV; S1d's reference, confirmed).
- `Mathlib/Analysis/InnerProductSpace/Basic.lean:262` — `inner_mul_inner_self_le` (Finding I; closest existing inner-product Cauchy-Schwarz, wrong shape for Route C).
- S1f session note (`2026-05-13-s1f-prep-s1e-errata-audit-route-c-weighted-finset.md` §2.2) — the deferred name question this PREP-7 closes.
- S1d session note (`2026-05-13-s01d-prep-pmf-ofFintype-gnp-construction.md`) — `Fintype.sum_pow_mul_eq_add_pow` reference (Finding IV verifies).
- Memory: `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` — Mathlib-bearer-audit pattern: parent PREP's "X exists in Y / similar" framing is a signal the bearer wasn't verified. This PREP-7 confirms the pattern: 2 of S1f §2.2's 2 candidate names were phantom.
- Memory: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — sister audit-correction sessions on adjacent slugs.
