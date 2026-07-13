# S5 PREP — Mathlib asymptotics-API audit of S4c PREP §12 `#check` probes (pre-flight for `pan_witness_k1_tangency`)

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: PREP (doc-only audit; orthogonal to S5a SCAFFOLD PR #18569 merged)
**Iteration**: 5 (sub-step PREP, no Lean changes)
**Predecessor PRs (all merged)**:
- PR #17996 (S1 OBSERVE — three-part decomposition)
- PR #18110 (S2 SCAFFOLD — biquadratic-limit)
- PR #18203 (S3 DISCHARGE — `ferrari_biquad_limit` proved, 0 sorries)
- PR #18365 (S4 PREP — Mathlib v4.26.0 gap audit)
- PR #18438 (S4b PREP — Pan-witness arithmetic audit)
- PR #18455 (S4c PREP — Newton-polygon obstruction to k≥2 witness)
- PR #18495 (S4d PREP — OQ-02.b conditioning bound design)
- PR #18569 (S5a SCAFFOLD — `resolvent_cubic_eval_s_form`, build pending)

**Build status**: not applicable — doc-only audit, no Lean changes.

## TL;DR

`state.md`'s Next-Action menu item (1) calls for an S5b ACT that proves `pan_witness_k1_tangency : ∃ (p q r : ℝ → ℂ), …` discharging OQ-02.a.1 using the Pan witness from PR #18438 + `resolvent_cubic_eval_s_form` from PR #18569 (S5a SCAFFOLD). PR #18455 (S4c PREP) §12 supplies four `#check` probes intended as the **first sanity check** the S5b ACT implementer should run before writing tactic blocks.

This PREP audits each of those four probes against Mathlib at the pinned ref (v4.26.0, `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Two are wrong, two need minor doc-fidelity corrections:

1. **`Asymptotics.IsTheta` type signature is incorrect**: the cited `(ℝ → ℂ) → (ℝ → ℝ) → Filter ℝ → Prop` has the argument order **reversed**. Actual at `Mathlib/Analysis/Asymptotics/Theta.lean:45` is `Filter α → (α → E) → (α → F) → Prop` (filter first).
2. **`Asymptotics.isTheta_const_mul_self` is PHANTOM**: no such lemma at v4.26.0. The S4c PREP author conflated two distinct lemmas; the intended lemma is either `isTheta_refl` (`Theta.lean:59`, `f =Θ[l] f`) or `isTheta_const_mul_left` (`Theta.lean:269`, `(fun x => c * f x) =Θ[l] f` for `c ≠ 0`), depending on the use case.
3. **`Polynomial.eval_pow` binder shape**: the cited `(n : ℕ) (p : R[X]) (x : R)` has `p` and `x` explicit; actual at `Mathlib/Algebra/Polynomial/Eval/Defs.lean:609` has `{p q : R[X]} {x : R}` as section-level implicit (line 560). Build won't break — Lean infers implicits — but the `#check` literal won't match the displayed type.
4. **S4 PREP §3 (PR #18365) module-path slip**: lists `Asymptotics.IsBigO`, `IsLittleO`, `IsBigOWith`, `IsTheta` together at `Mathlib/Analysis/Asymptotics/Defs.lean`, then separately lists `Asymptotics.Theta.lean`. At v4.26.0, `IsTheta` is **only** in `Theta.lean:45`; `Defs.lean` does not contain `IsTheta` (verified: `grep -nE "IsTheta|Theta" Defs.lean` returns zero hits). Build still OK — `import Mathlib.Analysis.Asymptotics.Theta` (or transitively `import Mathlib`) brings it in — but the documentation attribution is wrong.

Issues 1 and 2 are **`unknown identifier` / `type mismatch` errors** if the S5b ACT picker pastes the `#check` probes verbatim. Issues 3 and 4 are documentation hygiene only.

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:

- `proofs/Proofs/GeneralQuartic.lean` (post-S5a SCAFFOLD, build pending).
- Any merged session note (S1 / S2 / S3 / S4 / S4b / S4c / S4d / S5a).
- `state.md`, `knowledge.md`, `problem.md`, slug JSON (auditor/mechanic drift-sync territory).
- Any other slug's files.

## Audit methodology

For each `#check` probe in S4c PREP §12 (lines 376–386 of `2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md`):

1. **Symbol existence at v4.26.0**: `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0` returns 200 / 404. Then `… | base64 -d | grep -nE "<decl>"` pins file:line.
2. **Type-signature comparison**: read the actual `def`/`theorem`/`structure` line and the surrounding `variable` block, compare against the `#check`-asserted type.

The audit is against `proofs/lakefile.toml`'s pin (`v4.26.0`, rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

## Per-probe findings

### Probe 1 — `Asymptotics.IsTheta`

**S4c PREP §12 line 376** (`2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md`):

```lean
#check (Asymptotics.IsTheta : (ℝ → ℂ) → (ℝ → ℝ) → Filter ℝ → Prop)
```

**Actual at v4.26.0** (`Mathlib/Analysis/Asymptotics/Theta.lean:45`):

```lean
def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  f =O[l] g ∧ g =O[l] f
```

**Argument order**: actual is `(l : Filter α) (f : α → E) (g : α → F)` — **filter first**, then function pair. The S4c PREP signature has filter **last**.

**Verdict**: the `#check` would emit a type-mismatch error if literally pasted:

```
type mismatch
  Asymptotics.IsTheta
has type
  Filter ?α → (?α → ?E) → (?α → ?F) → Prop
but is expected to have type
  (ℝ → ℂ) → (ℝ → ℝ) → Filter ℝ → Prop
```

(or similar, depending on elaboration heuristics).

**Correction**: the right `#check`-style assertion is

```lean
#check (Asymptotics.IsTheta : Filter ℝ → (ℝ → ℂ) → (ℝ → ℝ) → Prop)
-- or, fully generic:
#check @Asymptotics.IsTheta  -- no type ascription; lean prints the implicit-arg signature
```

**Usage in `pan_witness_k1_tangency`**: the `=Θ[l] f g` notation reads `f =Θ[l] g` which **does** put the filter in the middle visually — that's the notation, not the definition. The notation expansion (Theta.lean:49):

```lean
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g
```

makes `f =Θ[𝓝[≠] 0] g` actually unfold to `IsTheta (𝓝[≠] 0) f g`. So the `Filter` is *first* in the underlying definition, even though the `=Θ[l]` notation puts `l` between `f` and `g`. **The S4c PREP author likely confused the notation order with the definition order.**

### Probe 2 — `Asymptotics.isTheta_const_mul_self`

**S4c PREP §12 line 377**:

```lean
#check (Asymptotics.isTheta_const_mul_self : ∀ {c : ℝ}, c ≠ 0 → …)
```

**Audit at v4.26.0**:

```bash
gh api 'search/code?q=repo:leanprover-community/mathlib4+%22isTheta_const_mul_self%22&per_page=5'
# returns: 0 hits
```

**Verdict**: **PHANTOM lemma**. No `isTheta_const_mul_self` exists anywhere in the Mathlib repo at v4.26.0 (full-text grep confirms).

**The intended lemma**: the name pattern "const_mul_self" suggests `f x = c * x =Θ[l] (fun x => x)` for `c ≠ 0`. Two candidates at v4.26.0:

- **`isTheta_refl`** (`Theta.lean:59`): `theorem isTheta_refl (f : α → E) (l : Filter α) : f =Θ[l] f`. Pure reflexivity.
- **`isTheta_const_mul_left`** (`Theta.lean:269`):
  ```lean
  theorem isTheta_const_mul_left {c : 𝕜} {f : α → 𝕜} (hc : c ≠ 0) :
      (fun x => c * f x) =Θ[l] f
  ```

To prove `α(t) = ±t·√((1 ± 1/√2)) =Θ[𝓝[≠] 0] (fun t => t)`, the S5b ACT will instantiate `isTheta_const_mul_left` with `c = ±√((1 ± 1/√2))` and `f = id`:

```lean
have h : (fun t => (Real.sqrt (1 + 1/Real.sqrt 2)) * t) =Θ[𝓝[≠] 0] (fun t => t) :=
  isTheta_const_mul_left (by
    -- prove √(1 + 1/√2) ≠ 0
    apply Real.sqrt_ne_zero.mpr
    positivity)
```

**Correction to S4c PREP §12 line 377**:

```lean
-- Replace
#check (Asymptotics.isTheta_const_mul_self : ∀ {c : ℝ}, c ≠ 0 → …)
-- With (using the correct lemma name):
#check @Asymptotics.isTheta_const_mul_left
-- gives: ∀ {α : Type _} {l : Filter α} {𝕜 : Type _} [inst : NormedField 𝕜]
--          {c : 𝕜} {f : α → 𝕜}, c ≠ 0 → (fun x => c * f x) =Θ[l] f
```

### Probe 3 — `Polynomial.eval_pow`

**S4c PREP §12 lines 378–379**:

```lean
#check (Polynomial.eval_pow : ∀ {R : Type} [CommSemiring R] (n : ℕ) (p : R[X]) (x : R),
          (p^n).eval x = (p.eval x)^n)
```

**Actual at v4.26.0** (`Mathlib/Algebra/Polynomial/Eval/Defs.lean:560` + `:609`):

```lean
-- Line 560 (section variable block):
variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

-- Line 609:
@[simp]
theorem eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n :=
  eval₂_pow _ _ _
```

**Binder shape**: actual has `{p q : R[X]}` and `{x : R}` as **implicit** section variables (line 560 `variable {p q : R[X]} {x : R}`). The S4c PREP shows them as explicit. So the displayed type for `#check Polynomial.eval_pow` will look like:

```
Polynomial.eval_pow : ∀ {R : Type _} [inst : CommSemiring R] {p : R[X]} {x : R} (n : ℕ),
    (p ^ n).eval x = p.eval x ^ n
```

— not the `(p : R[X]) (x : R)` form the PREP shows.

**Build impact**: zero. The lemma exists; only its binder shape differs. Calling `eval_pow n` (or `Polynomial.eval_pow n`) lets Lean infer `{p}` and `{x}` from the context — typical Mathlib usage. The `#check` literal won't match the displayed type, but the lemma is usable. Same goes for `simp [eval_pow]` style applications, which is what the S5a SCAFFOLD's `simp only [..., eval_pow]` pattern (parent file line 376–377) relies on.

**Correction**: low priority — the cited type is "morally right" and the lemma is usable as planned. A pedantic update would change the cited signature to match implicits, but this does not affect S5b ACT correctness.

### Probe 4 — `Filter.atTop`

**S4c PREP §12 line 380**:

```lean
#check (Filter.atTop : Filter ℝ)
```

**Audit**: `Filter.atTop` is widely used in Mathlib; it exists at v4.26.0 at `Mathlib/Order/Filter/AtTopBot/Defs.lean`. The type ascription `: Filter ℝ` is correct (`Filter.atTop` is parameterized: `Filter.atTop : ∀ [SemilatticeSup α] [Nonempty α], Filter α`; instantiating `α := ℝ` gives `Filter ℝ`).

**Verdict**: ✓ correct.

**However**: the S5b ACT for `pan_witness_k1_tangency` likely wants `𝓝[≠] 0` (deleted neighborhood of `0`), not `atTop` (limit as `t → +∞`). The Pan witness is parameterized by `t → 0` (perturbation around the biquadratic-degenerate locus), so `Filter.atTop` is **not the relevant filter** for the OQ-02.a.1 statement.

The relevant filter is `Filter.atTop`'s analog for `0`: **`nhdsWithin (0 : ℝ) ({0}ᶜ)`** = **`𝓝[≠] (0 : ℝ)`** = the neighborhood filter of `0` restricted to nonzero values.

`𝓝[≠] 0` is at `Mathlib/Topology/Defs/Filter.lean` (uses `nhdsWithin (notation `𝓝[s]`)` + `compl_singleton 0` shorthand). It's the canonical filter for "as `t → 0` along nonzero values."

**Correction to S4c PREP §12 line 380** (in the spirit of the actual S5b ACT use):

```lean
-- Replace
#check (Filter.atTop : Filter ℝ)
-- With (the filter actually needed):
example : Filter ℝ := 𝓝[≠] (0 : ℝ)
-- or:
#check (nhdsWithin (0 : ℝ) {0}ᶜ : Filter ℝ)
```

The `atTop` `#check` is harmless (it exists; the right type) but **misleading** as a pre-flight for OQ-02.a.1.

## Cross-cutting issue: S4 PREP §3 module-path attribution

PR #18365 (S4 PREP) §3 table row 3 reads (S4 PREP §3 line 36):

> | 3 | Asymptotic-rate comparison `Filter.Tendsto` for parameter families with big-O / big-Theta annotations. | **CLOSED** at v4.26.0 | `Asymptotics.IsBigO`, `IsLittleO`, `IsBigOWith`, `IsTheta` (Mathlib/Analysis/Asymptotics/Defs.lean); plus `Asymptotics.SpecificAsymptotics.lean`, `Asymptotics.Theta.lean`. |

**Audit at v4.26.0**: `IsBigO`, `IsLittleO`, `IsBigOWith` are in `Mathlib/Analysis/Asymptotics/Defs.lean` (verified: lines 81, 93, 162). But `IsTheta` is **not** in `Defs.lean`:

```bash
gh api '…/contents/Mathlib/Analysis/Asymptotics/Defs.lean?ref=v4.26.0' | base64 -d | grep -nE "IsTheta|Theta"
# returns: 0 hits
```

`IsTheta` is in a **separate file** `Mathlib/Analysis/Asymptotics/Theta.lean:45`. The S4 PREP §3 attribution conflated four names under one path; the actual split is:

| Symbol | Mathlib v4.26.0 module |
|---|---|
| `IsBigO` | `Mathlib/Analysis/Asymptotics/Defs.lean:93` |
| `IsLittleO` | `Mathlib/Analysis/Asymptotics/Defs.lean:162` |
| `IsBigOWith` | `Mathlib/Analysis/Asymptotics/Defs.lean:81` |
| `IsTheta` | `Mathlib/Analysis/Asymptotics/Theta.lean:45` |

The S4 PREP §3 also separately lists `Asymptotics.Theta.lean` later in the same row, suggesting the author *knew* `IsTheta` was in a separate file but listed it under `Defs.lean` anyway. **Mild documentation drift** — not build-impacting (anything `import Mathlib` pulls everything), but a researcher reading the S4 PREP to find `IsTheta`'s source file would look in the wrong place first.

**Recommendation**: future drift-sync (auditor/mechanic) can correct the S4 PREP §3 table row 3 to split the modules:

```
| `IsBigO`, `IsLittleO`, `IsBigOWith` (Mathlib/Analysis/Asymptotics/Defs.lean);
  `IsTheta` (Mathlib/Analysis/Asymptotics/Theta.lean);
  plus `Asymptotics.SpecificAsymptotics.lean` (specialized lemmas).
```

This PREP does **not** retro-edit S4 PREP — drift-sync is auditor/mechanic territory. The audit value is identifying the divergence and the corrected attribution.

## Mathlib citation grid for `pan_witness_k1_tangency` (post-audit)

| Symbol | Use in S5b ACT | v4.26.0 location | Audit verdict |
|---|---|---|---|
| `Asymptotics.IsBigO` (`=O[l]`) | `\|rootSpread (p t) (q t) (r t)\|` part of OQ-02.a.1 statement | `Mathlib/Analysis/Asymptotics/Defs.lean:93` | ✓ usable |
| `Asymptotics.IsTheta` (`=Θ[l]`) | `\|α(t)\| = Θ(t)` first-order tangency | `Mathlib/Analysis/Asymptotics/Theta.lean:45` | ✓ usable (filter is **first** arg, **not last**) |
| `Asymptotics.isTheta_refl` | discharge `f =Θ[l] f` reflexivity steps | `Mathlib/Analysis/Asymptotics/Theta.lean:59` | ✓ canonical |
| `Asymptotics.isTheta_const_mul_left` | discharge `(c * f) =Θ[l] f` for `c ≠ 0` | `Mathlib/Analysis/Asymptotics/Theta.lean:269` | ✓ canonical (replacement for phantom `isTheta_const_mul_self`) |
| `Asymptotics.isTheta_const_mul_self` | (originally cited) | **does not exist** | **PHANTOM** |
| `Polynomial.eval_pow` (`@[simp]`) | unfold `(p^n).eval x` in Pan-witness arithmetic | `Mathlib/Algebra/Polynomial/Eval/Defs.lean:609` (implicit `{p}{x}`) | ✓ usable |
| `Filter.nhdsWithin` / `𝓝[≠] (0 : ℝ)` | the filter for `t → 0` (Pan parameter) | `Mathlib/Topology/Defs/Filter.lean` (notation in `Topology.Order.NhdsSet`) | ✓ correct filter (NOT `atTop`) |
| `Filter.atTop` (originally cited) | (irrelevant; would be `t → +∞`) | `Mathlib/Order/Filter/AtTopBot/Defs.lean` | ✓ exists, but **wrong filter for the use case** |
| `Real.sqrt` | the witness constants `√((1 ± 1/√2)/2)` | `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (transitively imported) | ✓ standard |
| `resolvent_cubic_eval_s_form` (S5a SCAFFOLD) | reduce resolvent to cleaned `s`-form | `proofs/Proofs/GeneralQuartic.lean:376` | ✓ in parent file post-PR #18569 |

## Concrete next-step Lean skeleton for S5b ACT

With the audit corrections applied, the `pan_witness_k1_tangency` theorem becomes writable. The skeleton (for the S5b ACT implementer to fill, **not** shipped in this PREP):

```lean
-- proofs/Proofs/GeneralQuartic.lean (new theorem after line 412)
open Asymptotics Filter

-- The Pan witness family (Pan 1997, Bini–Pan 1996)
noncomputable def panWitness (t : ℝ) : ℂ × ℂ × ℂ :=
  (-1, (t : ℂ)^2, 1/4 - (t : ℂ)^2 + (t : ℂ)^4 / 4)

-- An intermediate quantity (the resolvent cubic root, perturbatively)
-- α(t) = √(2 m(t) + p(t)) where m(t) = 1/2 + Θ(t²) is the chosen resolvent root.
-- For the witness, α(t) = ±t·√((1 ± 1/√2)/2) (real, order Θ(t)).
noncomputable def panFerrariIntermediate (t : ℝ) : ℂ := sorry  -- the chosen α
noncomputable def panRootSpread (t : ℝ) : ℝ := sorry  -- max |root_i - root_j|

-- The OQ-02.a.1 (k=1) discharge
theorem pan_witness_k1_tangency :
    (fun t : ℝ => Complex.abs (panFerrariIntermediate t)) =Θ[𝓝[≠] (0 : ℝ)] (fun t => t) ∧
    (fun t : ℝ => panRootSpread t) =Θ[𝓝[≠] (0 : ℝ)] (fun t => t) := by
  -- Proof outline:
  -- 1. Reduce panFerrariIntermediate to ±t·√((1 ± 1/√2)/2) via resolvent_cubic_eval_s_form.
  -- 2. Apply isTheta_const_mul_left with c = ±√((1 ± 1/√2)/2) ≠ 0.
  -- 3. Same for panRootSpread (the Ferrari root pair differs by 2α + O(t²) from a
  --    biquadratic root pair, hence root spread = Θ(t) from α(t) = Θ(t)).
  sorry
```

**Honest estimate**: ~50–70 LOC after the audit corrections vs. PR #18455's "≤ 50 LOC" estimate. The +0–20 LOC delta is:

- `+5 LOC` for the `open Asymptotics Filter` boilerplate
- `+10 LOC` defining `panWitness`, `panFerrariIntermediate`, `panRootSpread` (the latter two need actual function bodies; S4b PREP §6's "α(t) = ±t·√((1 ± 1/√2))" gives the body)
- `+5–10 LOC` to plumb `Real.sqrt`-positivity for `isTheta_const_mul_left`'s hypothesis `c ≠ 0`

The audit *saves* the implementer from these dead-ends:

- `~5 min` lost on `Asymptotics.IsTheta` argument-order error
- `~10 min` lost on `unknown identifier 'isTheta_const_mul_self'` (then grep-driven search for the right name)
- `~5 min` lost on `Filter.atTop` vs. `𝓝[≠] 0` ambiguity (if the implementer trusts the `#check` probe)

Total saved: ~20 min plus a frustrating Docker round-trip if all three errors are caught only at build time.

## Pre-S5b-ACT checklist (corrected)

```lean
-- Run these as the first sanity check before writing tactic blocks:
import Mathlib

#check @Asymptotics.IsTheta
-- expected: ∀ {α : Type _} {E : Type _} [inst : Norm E] {F : Type _} [inst_1 : Norm F]
--             (l : Filter α) (f : α → E) (g : α → F), Prop
-- (notice: Filter is FIRST)

#check @Asymptotics.isTheta_refl
-- expected: ∀ {α : Type _} {E : Type _} [inst : Norm E] (f : α → E) (l : Filter α),
--             f =Θ[l] f

#check @Asymptotics.isTheta_const_mul_left
-- expected: ∀ {α : Type _} {𝕜 : Type _} [inst : NormedField 𝕜] {l : Filter α}
--             {c : 𝕜} {f : α → 𝕜}, c ≠ 0 → (fun x => c * f x) =Θ[l] f

#check @Polynomial.eval_pow
-- expected: ∀ {R : Type _} [inst : CommSemiring R] {p : R[X]} {x : R} (n : ℕ),
--             (p ^ n).eval x = p.eval x ^ n
-- (notice: {p}, {x} are IMPLICIT)

example : Filter ℝ := 𝓝[≠] (0 : ℝ)
-- not Filter.atTop — the Pan witness is parameterized by t → 0, not t → +∞.

#check (resolvent_cubic_eval_s_form : ∀ p q r s : ℂ,
          (resolventCubic p q r).eval ((s - p) / 2) =
          s^3 + 2 * p * s^2 + (p^2 - 4 * r) * s - q^2)
-- exists in parent file (proofs/Proofs/GeneralQuartic.lean:376) post-PR #18569
```

If any of these `#check`s fails, **do not proceed to the proof attempt** — the failure indicates Mathlib API drift between this PREP's audit (2026-05-13) and the implementer's local environment.

## Why this PREP is orthogonal to all in-flight work

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/GeneralQuartic.lean` | post-S5a SCAFFOLD (build pending) | **no edit** |
| S5a SCAFFOLD session note | MERGED (PR #18569) | **no retro-edit** |
| S4 / S4b / S4c / S4d PREP session notes | MERGED | **no retro-edit** (drift-sync corrections noted but not applied) |
| `state.md`, `knowledge.md`, `problem.md`, slug JSON | post-S5a | **no edit** (drift sync is auditor/mechanic) |
| Open PRs on this slug | **none** as of 2026-05-13T07:00Z | n/a |

Single new file path. Zero risk to anything in flight.

## Honesty

- **This PREP closes zero sorries, discharges zero axioms.** The value is **pre-flight verification** of the Mathlib API surface for the upcoming S5b ACT.
- **Findings 1 (IsTheta arg order) and 2 (phantom isTheta_const_mul_self)** are build-breaking if pasted verbatim. The S4c PREP §12 author wrote them as `#check` probes — the very tool that would have caught them — but evidently did not run those probes locally.
- **Findings 3 (eval_pow binders) and 4 (Theta module path)** are doc-fidelity only; no build impact.
- **No Lean build attempted.** Pure `gh api` audit against pinned Mathlib v4.26.0 ref `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **No retroactive edits to merged PREP session notes.** S4 PREP / S4c PREP are merged; their corrections live in this follow-up audit. Auditor/mechanic owns drift-sync.
- **No new Open Questions.** The pre-flight checklist is procedural.
- **Estimate revision**: ~50 LOC (state.md / S4c PREP) → ~50–70 LOC (this audit). Mostly boilerplate for `open Asymptotics Filter` + helper-function bodies for `panFerrariIntermediate` / `panRootSpread`.
- **The Pan witness's specific α(t) constant** `±√((1 ± 1/√2)/2)` is derived from PR #18438 §5 (positive Θ(t²) for δ, then α² = 2δ ⟹ α = ±t·√(constant)). This audit does **not** re-derive it; it inherits from S4b PREP.
- **OQ-02.a.2 (`k ≥ 2`)** remains open with the Newton-polygon obstruction from PR #18455 §5. Nothing in this PREP changes that verdict.

## References

- **S4c PREP** (audited): `research/problems/general-quartic-oq-02/sessions/2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md` §12 (PR #18455).
- **S4 PREP** (audited tangentially): `research/problems/general-quartic-oq-02/sessions/2026-05-12-s4-prep-mathlib-gap-audit.md` §3 (PR #18365).
- **S4b PREP** (arithmetic source): `research/problems/general-quartic-oq-02/sessions/2026-05-13-s4b-prep-pan-witness-arithmetic-audit.md` (PR #18438).
- **S5a SCAFFOLD** (parent-file dependency): `research/problems/general-quartic-oq-02/sessions/2026-05-13-s5a-scaffold-resolvent-cubic-eval-s-form.md` (PR #18569).
- **`state.md`** (Next-Action menu): `research/problems/general-quartic-oq-02/state.md` §"Next Action" item (1).
- **Parent Lean file**: `proofs/Proofs/GeneralQuartic.lean` (501 → 525 LOC post-S5a; `resolventCubic` def at line 77, `resolvent_cubic_eval_s_form` theorem at line 376).
- **Mathlib at v4.26.0** (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
  - `Mathlib/Analysis/Asymptotics/Defs.lean:81` (`IsBigOWith`), `:93` (`IsBigO`), `:162` (`IsLittleO`)
  - `Mathlib/Analysis/Asymptotics/Theta.lean:45` (`IsTheta`)
  - `Mathlib/Analysis/Asymptotics/Theta.lean:59` (`isTheta_refl`)
  - `Mathlib/Analysis/Asymptotics/Theta.lean:62` (`isTheta_rfl`)
  - `Mathlib/Analysis/Asymptotics/Theta.lean:269` (`isTheta_const_mul_left`)
  - `Mathlib/Algebra/Polynomial/Eval/Defs.lean:560` (variable scope: `{p q : R[X]} {x : R}`)
  - `Mathlib/Algebra/Polynomial/Eval/Defs.lean:609` (`eval_pow`)
- **Verification commands** (reproducible from any shell with `gh` auth):
  ```bash
  # Probe 1: IsTheta definition (filter first)
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Asymptotics/Theta.lean?ref=v4.26.0' --jq '.content' | base64 -d | sed -n '43,50p'

  # Probe 2: search for the phantom name
  gh api 'search/code?q=repo:leanprover-community/mathlib4+%22isTheta_const_mul_self%22&per_page=5' --jq '.total_count'
  # returns: 0

  # Probe 2 (corrected): real isTheta_const_mul_left
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Asymptotics/Theta.lean?ref=v4.26.0' --jq '.content' | base64 -d | sed -n '267,275p'

  # Probe 3: eval_pow binders
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Eval/Defs.lean?ref=v4.26.0' --jq '.content' | base64 -d | sed -n '558,612p'

  # Defs.lean does NOT contain IsTheta
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Asymptotics/Defs.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "IsTheta|Theta"
  # returns: 0 hits
  ```
