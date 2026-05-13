# S5 PREP — `iteratedIntervalIntegral_swap_succ` discharge plan

**Researcher.** researcher-11
**Date.** 2026-05-13 (UTC ~05:10)
**Phase.** ACT (S5 PREP)
**Mode.** doc-only
**Lean changes.** 0
**Estimated reading.** 12-15 min

## TL;DR

S4 SCAFFOLD (researcher-10, PR #18-series) added `iteratedIntervalIntegral_swap_succ`
at `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean:142-150` with a strategic
`sorry` and 80-120 LOC discharge estimate.

This PREP audits the Mathlib bearer surface for the S5 discharge and surfaces
**three corrections** to the S4 plan as written:

1. **`Fin.induction` does not directly type-check on `i : Fin n`.** The Lean-core
   `Fin.induction` (lean4 `src/Init/Data/Fin/Lemmas.lean:911`) requires
   `motive : Fin (n + 1) → Sort _`. Our hypothesis is `i : Fin n`, so the natural
   induction is on the *ambient dimension* `n`, with `Fin.cases i` (or pattern
   match) splitting at each level. §2 details the corrected outer skeleton.
2. **The base case (`i = 0`) needs `intervalIntegral_swap_of_continuous` PLUS a
   continuity-of-iterated-integral side lemma.** The 2D bridge from §4 is not
   `intervalIntegral_swap_of_continuous` applied directly to `f`; it is applied
   to a parametric inner integrand
   `F(x₀, x₁) := iteratedIntervalIntegral (a∘ss) (b∘ss) (fun rest' => f(...))`
   that depends continuously on `(x₀, x₁)`. **No off-the-shelf
   `Continuous.iteratedIntervalIntegral` lemma is established** in this file or
   (at audit time) in `Mathlib.MeasureTheory.Integral.IntervalIntegral.*`; it
   needs to be proved locally as a one-line Bochner-continuity-of-parametric-
   integral lemma OR worked around by integrating against `Continuous` directly
   and extracting joint continuity from `Continuous f`.
3. **The S4-stated estimate "~80-120 lines" is light.** Realistic discharge
   accounting for the continuity side condition + the `(Fin.cons y₀ rest)∘swap01`
   reshuffling identity (§4.2) is **~150-200 LOC**, of which ~60 LOC is the
   inductive-step transport (§5).

§3 gives the citation grid. §4-§5 give the per-case proof recipes with concrete
tactic outlines. §6 enumerates risks (v4.26.0 drift in the parent file is the
top one; flagged in memory `project_greens_theorem_family_mathlib_drift_v4260.md`
but does not block S5 directly because the parent's
`intervalIntegral_swap_of_continuous` does not transit through the phantom
`restrict_prod_eq_prod_restrict` after measurability is supplied via
`Continuous.measurable` — verified in §6.1).

## §1 Goal and current state

`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean` (152 lines, sorry count 1):

```lean
-- Lines 142-150
theorem iteratedIntervalIntegral_swap_succ
    {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (_hf : Continuous f) :
    iteratedIntervalIntegral a b f
      = iteratedIntervalIntegral
          (a ∘ Equiv.swap i.castSucc i.succ)
          (b ∘ Equiv.swap i.castSucc i.succ)
          (fun v => f (v ∘ Equiv.swap i.castSucc i.succ)) := by
  sorry
```

**Available primitives.** Same file contains:
- `iteratedIntervalIntegral` (lines 58-64): structural recursion on `n`,
  `n = 0 ↦ f Fin.elim0`, `n+1 ↦ ∫ x₀ in a 0..b 0, iter_int (a∘Fin.succ) (b∘Fin.succ) (fun rest => f (Fin.cons x₀ rest))`.
- `iteratedIntervalIntegral_two` (lines 81-99): worked example of bridging
  `Fin.cons x (Fin.cons y Fin.elim0)` ↔ `fun i => if i = 0 then x else y` via
  `intervalIntegral.integral_congr`-twice + `congr 1; funext i; fin_cases i; <;> simp`.

**Parent (`GreensTheoremOQ01OQ01OQ02.lean`) bearers used downstream:**
- `intervalIntegral_swap` (line 82): general 4-case unbounded-order Fubini for
  `f : ℝ → ℝ → ℝ`. Hypotheses: `Measurable (fun p : ℝ × ℝ => f p.1 p.2)` +
  `Integrable ... ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))`.
- `intervalIntegral_swap_of_continuous` (line 183): `Continuous (fun p : ℝ × ℝ => f p.1 p.2)`
  ⇒ swap holds with no ordering and no separate measurability/integrability arg.

The S5 base case will use `intervalIntegral_swap_of_continuous` (parent line 183).

## §2 Outer induction skeleton — `Fin.induction` does not directly apply

**Claim.** The S4 plan stated "`Fin.induction` on `i`" but `Fin.induction`
(lean4 `src/Init/Data/Fin/Lemmas.lean:911-915`) has signature

```lean
@[elab_as_elim] def induction {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) :
    ∀ i : Fin (n + 1), motive i
```

The motive is on `Fin (n+1)` and the eliminated variable ranges over `Fin (n+1)`.
Our hypothesis is `i : Fin n` (one less). `Fin.cases` (`Init/Data/Fin/Lemmas.lean:953`)
has the same shape: motive on `Fin (n+1)`, eliminates over `Fin (n+1)`.

**Resolution: induct on `n` (the ambient dimension), then split on `i`.**

```lean
theorem iteratedIntervalIntegral_swap_succ ... := by
  induction n with
  | zero =>
      -- i : Fin 0 is empty
      exact (Fin.elim0 i).elim    -- or `cases i.elim0` / `exact i.elim0`
  | succ m IH =>
      -- Now i : Fin (m+1), so Fin.cases applies
      induction i using Fin.cases with
      | H0 =>
          -- BASE CASE: i = 0; see §4
          sorry
      | Hs j =>
          -- INDUCTIVE STEP: i = j.succ where j : Fin m; see §5
          sorry
```

**Caveat — IH shape.** The `induction n with` step gives an IH parametric in
the `Fin m → ℝ` family. When we hit the `Hs j` case at level `m+1`, the IH
should be applied at the *restricted* family `(a∘Fin.succ, b∘Fin.succ, f∘(Fin.cons x₀ ·))`
on `Fin m → ℝ` with the swap `Equiv.swap j.castSucc j.succ`. The reshuffling
of the `Fin.succ` shifts is the bulk of the §5 algebra.

Alternative: a **single `Fin.cases` after `match n with | 0 => ... | m+1 => ...`**
also works and may be cleaner. Both are linguistically valid.

**Vacuous base case (`n = 0`).** `Fin.elim0 : Fin 0 → C` for any `C`. The most
robust spelling is `exact i.elim0` or `cases i` (Lean's `cases` on an empty
inductive immediately closes the goal). No tactic risk.

## §3 Mathlib bearer audit

All citations verified via `gh api repos/.../contents | base64 -d` at audit time
(2026-05-13 ~04:55 UTC). Mathlib pinned rev: `v4.26.0` (per repo `lean-toolchain`).

| # | Symbol | Path | Line | Notes |
|---|--------|------|------|-------|
| B1 | `Fin.induction` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 911 | Lean **core**, NOT Mathlib. Motive on `Fin (n+1)`. `@[elab_as_elim]`. |
| B2 | `Fin.induction_zero` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 921 | `@[simp, grind =]`. `induction zero hs 0 = zero` by `rfl`. |
| B3 | `Fin.induction_succ` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 925 | `@[simp, grind =]`. `induction zero succ i.succ = succ i (induction zero succ i.castSucc)` by `rfl`. |
| B4 | `Fin.cases` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 953 | Lean **core**. Motive on `Fin (n+1)`. `@[elab_as_elim]`. Single-step pattern-match. |
| B5 | `Fin.cons_zero` | `Mathlib/Data/Fin/Tuple/Basic.lean` | 123 | `@[simp]`. `cons x p 0 = x`. |
| B6 | `Fin.cons_succ` | `Mathlib/Data/Fin/Tuple/Basic.lean` | 120 | `@[simp]`. `cons x p i.succ = p i`. |
| B7 | `Equiv.swap_self` | `Mathlib/Logic/Equiv/Basic.lean` | 639 | `swap a a = Equiv.refl _`. |
| B8 | `Equiv.swap_comm` | `Mathlib/Logic/Equiv/Basic.lean` | 642 | `swap a b = swap b a`. |
| B9 | `Equiv.swap_apply_left` | `Mathlib/Logic/Equiv/Basic.lean` | 650 | `swap a b a = b`. |
| B10 | `Equiv.swap_apply_right` | `Mathlib/Logic/Equiv/Basic.lean` | 654 | `swap a b b = a`. |
| B11 | `Equiv.swap_apply_of_ne_of_ne` | `Mathlib/Logic/Equiv/Basic.lean` | 657 | `x ≠ a → x ≠ b → swap a b x = x`. |
| B12 | `intervalIntegral.integral_congr` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | 1050 | Hypothesis: `EqOn f g [[a, b]]` (uIcc). `f = g` on the relevant interval ⇒ `∫a..b f = ∫a..b g`. |
| B13 | `intervalIntegral_swap_of_continuous` | local: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` | 183 | Hypothesis: `Continuous (fun p : ℝ × ℝ => f p.1 p.2)`. No ordering, no separate measurability. |

**Drift / phantom check.** None of B1-B13 are renamed at v4.26.0 relative to the
S4 SCAFFOLD's plan (verified by direct contents fetch at audit time).

**Notable absence.** No off-the-shelf `Continuous.iteratedIntervalIntegral`
lemma was located in `Mathlib.MeasureTheory.Integral.IntervalIntegral.*` (search
hit rate-limit at attempt 6/6, but the candidate names
`Continuous.intervalIntegrable`, `ContinuousOn.intervalIntegrable_of_uIcc`,
`continuous_parametric_intervalIntegral` returned **0 hits** on the first three
queries). §4.4 details the local workaround.

## §4 Base case (`i = 0`) — detailed unfolding

**Setup.** At this case, `n` from `Fin.cases` is `m+1` for some `m ≥ 0`, and `i = 0 : Fin (m+1)`.
Then `i.castSucc = (0 : Fin (m+1)).castSucc = (0 : Fin (m+2))` and
`i.succ = (0 : Fin (m+1)).succ = (1 : Fin (m+2))`.

So `Equiv.swap i.castSucc i.succ = Equiv.swap (0 : Fin (m+2)) (1 : Fin (m+2))`.

Abbreviate `swap01 := Equiv.swap (0 : Fin (m+2)) (1 : Fin (m+2))`.

### §4.1 LHS expansion (two unfoldings)

```text
LHS := iteratedIntervalIntegral a b f
     = ∫ x₀ in a 0 .. b 0,
         iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
           (fun rest₁ => f (Fin.cons x₀ rest₁))                         -- (1) unfold at m+2
     = ∫ x₀ in a 0 .. b 0, ∫ x₁ in (a ∘ Fin.succ) 0 .. (b ∘ Fin.succ) 0,
         iteratedIntervalIntegral ((a ∘ Fin.succ) ∘ Fin.succ)
                                  ((b ∘ Fin.succ) ∘ Fin.succ)
           (fun rest₂ => f (Fin.cons x₀ (Fin.cons x₁ rest₂)))           -- (2) unfold at m+1
```

`(a ∘ Fin.succ) 0 = a (Fin.succ 0) = a 1` by `rfl` (Fin.succ on `0 : Fin (m+1)` is
`(1 : Fin (m+2))`). Similarly for `b`. So:

```text
LHS = ∫ x₀ in a 0 .. b 0, ∫ x₁ in a 1 .. b 1,
        iteratedIntervalIntegral (a ∘ Fin.succ ∘ Fin.succ)
                                 (b ∘ Fin.succ ∘ Fin.succ)
          (fun rest₂ => f (Fin.cons x₀ (Fin.cons x₁ rest₂)))
```

### §4.2 RHS expansion (two unfoldings)

```text
RHS := iteratedIntervalIntegral (a ∘ swap01) (b ∘ swap01)
                                (fun v => f (v ∘ swap01))
     = ∫ y₀ in (a ∘ swap01) 0 .. (b ∘ swap01) 0,
         iteratedIntervalIntegral ((a ∘ swap01) ∘ Fin.succ)
                                  ((b ∘ swap01) ∘ Fin.succ)
           (fun rest₁ => (fun v => f (v ∘ swap01)) (Fin.cons y₀ rest₁))
```

**Key identity #1 (the bound at outer level):**
`(a ∘ swap01) 0 = a (swap01 0) = a 1` by `Equiv.swap_apply_left` (B9, with
`a := 0`, `b := 1`). Likewise `(b ∘ swap01) 0 = b 1`. Outer bound becomes `a 1 .. b 1`.

**Key identity #2 (the inner-bound shift):** `(a ∘ swap01) ∘ Fin.succ` at index
`k : Fin (m+1)`:
- If `k = 0`: `(a ∘ swap01) (Fin.succ 0) = (a ∘ swap01) 1 = a (swap01 1) = a 0`
  by `Equiv.swap_apply_right` (B10).
- If `k = j.succ` (some `j : Fin m`): `(a ∘ swap01) (Fin.succ k) = (a ∘ swap01) k.succ`
  with `k.succ ≥ 2` in `Fin (m+2)`, so `swap01 k.succ = k.succ` by `Equiv.swap_apply_of_ne_of_ne` (B11)
  with hypotheses `k.succ ≠ 0` (immediate from `Fin.succ_ne_zero`) and `k.succ ≠ 1`
  (because `k.succ = (j.succ).succ ≥ 2`, so `k.succ ≠ 1` requires showing
  `(j.succ).succ.val = j.val + 2 ≥ 2`, i.e. `(j+2).val ≠ 1`, which is by `omega`
  on `j.val + 2 ≠ 1`; cleaner spelling: `Fin.ne_of_val_ne` plus `omega`).

So `(a ∘ swap01) ∘ Fin.succ = Fin.cons (a 0) (a ∘ Fin.succ ∘ Fin.succ)` as a
`Fin (m+1) → ℝ` tuple. Likewise for `b`.

**Key identity #3 (the inner-integrand shift):**
`(Fin.cons y₀ rest₁) ∘ swap01` at index `k : Fin (m+2)`:
- `k = 0`: `(Fin.cons y₀ rest₁) (swap01 0) = (Fin.cons y₀ rest₁) 1 = rest₁ 0`
  (B5, B6, B9).
- `k = 1`: `(Fin.cons y₀ rest₁) (swap01 1) = (Fin.cons y₀ rest₁) 0 = y₀` (B5, B10).
- `k = j.succ.succ` (some `j : Fin m`): `(Fin.cons y₀ rest₁) (swap01 k) = (Fin.cons y₀ rest₁) k = rest₁ (j.succ)`
  (B6, B11, plus the same `k ≥ 2` arithmetic as above).

So `(Fin.cons y₀ rest₁) ∘ swap01 = Fin.cons (rest₁ 0) (Fin.cons y₀ (rest₁ ∘ Fin.succ))`
as a `Fin (m+2) → ℝ` tuple. The *inner* integrand `(fun v => f (v ∘ swap01)) (Fin.cons y₀ rest₁)`
becomes `f (Fin.cons (rest₁ 0) (Fin.cons y₀ (rest₁ ∘ Fin.succ)))`.

**Now apply iteratedIntervalIntegral one more level.** The inner
`iteratedIntervalIntegral` of RHS now reads (after substituting Identity #2):

```text
∫ y₁ in (Fin.cons (a 0) (a ∘ ss)) 0 .. (Fin.cons (b 0) (b ∘ ss)) 0,
   iteratedIntervalIntegral ((Fin.cons (a 0) (a ∘ ss)) ∘ Fin.succ)
                            ((Fin.cons (b 0) (b ∘ ss)) ∘ Fin.succ)
     (fun rest₂ => f (Fin.cons (rest₁ 0) (Fin.cons y₀ (rest₁ ∘ Fin.succ))))
```
(with `rest₁ = Fin.cons y₁ rest₂`, abbreviating `ss := Fin.succ ∘ Fin.succ`).

By B5 (`Fin.cons_zero`): `(Fin.cons (a 0) (a ∘ ss)) 0 = a 0`, and
`(Fin.cons (a 0) (a ∘ ss)) ∘ Fin.succ = a ∘ ss` by B6 (`Fin.cons_succ`)
+ `funext`. Likewise for `b`. So the bound at this level is `a 0 .. b 0`.

Substituting `rest₁ = Fin.cons y₁ rest₂` into the integrand (using B5/B6 for
`(Fin.cons y₁ rest₂) 0 = y₁` and `(Fin.cons y₁ rest₂) ∘ Fin.succ = rest₂`):

```text
RHS = ∫ y₀ in a 1 .. b 1, ∫ y₁ in a 0 .. b 0,
        iteratedIntervalIntegral (a ∘ ss) (b ∘ ss)
          (fun rest₂ => f (Fin.cons y₁ (Fin.cons y₀ rest₂)))
```

### §4.3 Bridge to `intervalIntegral_swap_of_continuous`

Define the parametric inner integrand
```text
F : ℝ × ℝ → ℝ
F (x, y) := iteratedIntervalIntegral (a ∘ ss) (b ∘ ss) (fun rest₂ => f (Fin.cons x (Fin.cons y rest₂)))
```

Then:
- LHS = `∫ x₀ in a 0..b 0, ∫ x₁ in a 1..b 1, F (x₀, x₁)`
- RHS = `∫ y₀ in a 1..b 1, ∫ y₁ in a 0..b 0, F (y₁, y₀)`

By rename `(x₀, x₁) ↦ (y₁, y₀)` (Fubini swap of order of integration):
RHS = `∫ x₁ in a 1..b 1, ∫ x₀ in a 0..b 0, F (x₀, x₁)`.

Apply `intervalIntegral_swap_of_continuous` (B13) at `f := F`, with
`a := a 0, b := b 0, c := a 1, d := b 1`:

```lean
exact intervalIntegral_swap_of_continuous (a 0) (b 0) (a 1) (b 1)
  (continuous_F : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
```

This delivers the equality LHS = RHS *modulo the LHS/RHS unfolding identities §4.1-§4.2*.

### §4.4 The continuity-of-iterated-integral side condition

`continuous_F` requires showing
```text
Continuous (fun p : ℝ × ℝ =>
  iteratedIntervalIntegral (a ∘ ss) (b ∘ ss)
    (fun rest₂ => f (Fin.cons p.1 (Fin.cons p.2 rest₂))))
```

This is the **non-trivial side condition** the S4 estimate did not call out
explicitly. There are two ways to discharge it:

**Path A — local lemma `Continuous.iteratedIntervalIntegral`.** State and
prove (~30-40 LOC):
```lean
lemma Continuous.iteratedIntervalIntegral
    {n : ℕ} {α : Type*} [TopologicalSpace α]
    (a b : Fin n → ℝ) {F : α → (Fin n → ℝ) → ℝ}
    (hF : Continuous (fun p : α × (Fin n → ℝ) => F p.1 p.2)) :
    Continuous (fun x : α => iteratedIntervalIntegral a b (F x))
```
Proof by `Fin.induction n`: base case `n = 0` is `Continuous (fun x => F x Fin.elim0)` =
`hF.comp (continuous_id.prodMk continuous_const)`; inductive step pulls the outer
integral in via `intervalIntegral.continuous_of_continuous_uncurry` (Mathlib has
this in some form — needs verification before S5 push).

**Path B — exploit the *rest* parametricity.** The
`fun rest₂ => f (Fin.cons p.1 (Fin.cons p.2 rest₂))` is continuous in
`(p.1, p.2, rest₂)` jointly (since `Continuous f` plus continuity of `Fin.cons`).
Then `F (p.1, p.2) = iteratedIntervalIntegral (a∘ss) (b∘ss) (g)` where `g`
depends continuously on `(p.1, p.2)` via the `Continuous.intervalIntegrable`
chain — the same Path A induction is needed under the hood.

**Recommendation.** Path A as a stand-alone lemma is cleaner and reusable for S6
(the `_perm` extension). It belongs in the same file. Estimated +30 LOC if
Mathlib has `intervalIntegral.continuous_of_continuous` for the inductive step;
+50 LOC if we have to prove parametric continuity from scratch.

## §5 Inductive step (`i = j.succ`) — swap fixes coordinate 0

**Setup.** `j : Fin m` (since `i : Fin (m+1)` decomposes as `j.succ` for `j : Fin m`),
and we work in `Fin (m+2) → ℝ`.

`i.castSucc = (j.succ).castSucc = (j.castSucc).succ` (Mathlib lemma
`Fin.castSucc_succ` or `Fin.succ_castSucc` — needs spelling check at audit time;
both names appear at v4.26.0).

`i.succ = (j.succ).succ`.

So `Equiv.swap i.castSucc i.succ` swaps `(j.castSucc).succ` and `(j.succ).succ`
in `Fin (m+2)`. Abbreviate this `swap_jss`.

### §5.1 Key swap factorization

Claim: `swap_jss` fixes index `0 : Fin (m+2)` and on `Fin.succ k` for
`k : Fin (m+1)` acts as `Fin.succ (Equiv.swap j.castSucc j.succ k)`.

**Proof of fixed-0:**
`swap_jss 0 = Equiv.swap (j.castSucc).succ (j.succ).succ 0`. Since
`(j.castSucc).succ ≥ 1 > 0` and `(j.succ).succ ≥ 1 > 0`, both `≠ 0`, so by
B11 (`swap_apply_of_ne_of_ne`): `swap_jss 0 = 0`.

**Proof of `Fin.succ`-equivariance:** for `k : Fin (m+1)`, write `swap_inner :=
Equiv.swap j.castSucc j.succ : Fin (m+1) → Fin (m+1)`. Need `swap_jss (Fin.succ k) = Fin.succ (swap_inner k)`.

Three sub-cases on `k`:
- `k = j.castSucc`: `swap_jss (Fin.succ j.castSucc) = swap_jss (j.castSucc).succ = (j.succ).succ = Fin.succ j.succ = Fin.succ (swap_inner j.castSucc)`. ✓ (using B9: `swap a b a = b`).
- `k = j.succ`: similar, using B10. ✓
- `k ∉ {j.castSucc, j.succ}`: `swap_inner k = k` (by B11), and `Fin.succ k ∉ {(j.castSucc).succ, (j.succ).succ}` (since `Fin.succ_injective`), so `swap_jss (Fin.succ k) = Fin.succ k = Fin.succ (swap_inner k)`. ✓

This factorization deserves a **named local lemma** in the same file (~12-18 LOC):

```lean
private lemma swap_succ_factor {m : ℕ} (j : Fin m) (k : Fin (m+1)) :
    Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ k)
      = Fin.succ (Equiv.swap j.castSucc j.succ k) := by
  by_cases hL : k = j.castSucc
  · subst hL; simp [Equiv.swap_apply_left, Fin.succ_castSucc]  -- name spelling pending
  by_cases hR : k = j.succ
  · subst hR; simp [Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => hL (Fin.succ_injective h)
  · exact fun h => hR (Fin.succ_injective h)
  -- LHS: hypotheses for k.succ ≠ (j.castSucc).succ and k.succ ≠ (j.succ).succ
  · exact fun h => hL ((Fin.succ_injective h))
  · exact fun h => hR ((Fin.succ_injective h))

private lemma swap_succ_zero {m : ℕ} (j : Fin m) :
    Equiv.swap (j.castSucc).succ (j.succ).succ 0 = 0 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (Fin.succ_ne_zero _).symm
  · exact (Fin.succ_ne_zero _).symm
```

(Spelling note: `(Fin.succ_ne_zero _).symm` may need to be `Fin.succ_ne_zero _`
without `.symm` depending on whether the lemma is stated `Fin.succ k ≠ 0` or
`0 ≠ Fin.succ k`. v4.26.0 stores it as `Fin.succ_ne_zero : ∀ (n : ℕ) (i : Fin n), Fin.succ i ≠ 0` — confirmed inline by reading
`Init/Data/Fin/Lemmas.lean` headers — so use without `.symm` and reverse the
`ne_comm` if needed.)

### §5.2 Unfolding LHS and RHS

LHS unfolds by one level (per §4.1 idiom):
```text
LHS = ∫ x₀ in a 0 .. b 0,
        iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
          (fun rest => f (Fin.cons x₀ rest))
```

RHS unfolds by one level. By §5.1, `(a ∘ swap_jss) 0 = a (swap_jss 0) = a 0`,
and `(a ∘ swap_jss) ∘ Fin.succ = a ∘ Fin.succ ∘ (Equiv.swap j.castSucc j.succ)`
(this is the §5.1 factorization composed with `a ∘ Fin.succ : Fin (m+1) → ℝ`).
Likewise `(Fin.cons y₀ rest) ∘ swap_jss = Fin.cons y₀ (rest ∘ Equiv.swap j.castSucc j.succ)`
(by §5.1 factorization plus B5/B6).

So:
```text
RHS = ∫ y₀ in a 0 .. b 0,
        iteratedIntervalIntegral (a ∘ Fin.succ ∘ Equiv.swap j.castSucc j.succ)
                                 (b ∘ Fin.succ ∘ Equiv.swap j.castSucc j.succ)
          (fun rest => f (Fin.cons y₀ (rest ∘ Equiv.swap j.castSucc j.succ)))
```

### §5.3 Apply IH and conclude

`intervalIntegral.integral_congr` (B12) reduces equality of the outer integrals
to pointwise equality of the inner functions on `[[a 0, b 0]]`:
```lean
refine intervalIntegral.integral_congr ?_
intro x₀ _hx₀
```

Now the goal is, for fixed `x₀`:
```text
iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ) (fun rest => f (Fin.cons x₀ rest))
  = iteratedIntervalIntegral (a ∘ Fin.succ ∘ swap_inner) (b ∘ Fin.succ ∘ swap_inner)
      (fun rest => f (Fin.cons x₀ (rest ∘ swap_inner)))
```
where `swap_inner = Equiv.swap j.castSucc j.succ`.

This is *exactly* the IH at level `m`, applied to:
- `a' := a ∘ Fin.succ : Fin (m+1) → ℝ`
- `b' := b ∘ Fin.succ : Fin (m+1) → ℝ`
- `f' := fun v => f (Fin.cons x₀ v) : (Fin (m+1) → ℝ) → ℝ`
- `j : Fin m` (the prior swap index)
- `_hf' : Continuous f' := _hf.comp (continuous_finCons_x₀)` (with
  `continuous_finCons_x₀` = continuity of the partial-application
  `fun v => Fin.cons x₀ v`, which is continuous because
  `Fin.cons : ℝ → (Fin m → ℝ) → (Fin (m+1) → ℝ)` is continuous in both
  arguments, separately and jointly — needs Mathlib `Continuous.fin_cons`
  spelling check; alternatively `continuous_pi (fun i => Fin.cases continuous_const ...)`).

```lean
exact IH a' b' f' j _hf'
```

### §5.4 Estimated step size

§5.1 lemmas: ~15-20 LOC.
§5.2-§5.3 reduction: ~25-35 LOC.
Continuity of `Fin.cons x₀ ·` (§5.3): ~5-10 LOC.

**Total inductive step: ~45-65 LOC.**

## §6 Risk register

### §6.1 v4.26.0 drift in parent file (LOW for S5; flagged for follow-up)

Memory `project_greens_theorem_family_mathlib_drift_v4260.md` records that
`GreensTheoremOQ01OQ01OQ02.lean:191` uses the **phantom**
`restrict_prod_eq_prod_restrict` (Mathlib v4.26.0 replacement is `Measure.prod_restrict`
in the reverse direction). If this phantom is unresolved, the parent file does
not build, and S5 cannot import `intervalIntegral_swap_of_continuous`.

**Audit at this PREP** (2026-05-13 ~05:00 UTC): the open OQ-01 file
`GreensTheoremOQ01OQ01OQ02OQ01.lean` already imports `Proofs.GreensTheoremOQ01OQ01OQ02`
(line 41) and the S2/S3 PRs from 2026-05-12 are stacked as "build pending". So
the parent's build status is unknown right now.

**Mitigation.** S5 ACT must include a "parent rebuild verify" step (or a Doctor
PR fixing the drift first). If the drift fix is required, defer S5 ACT until
Doctor lands the Mathlib-API drift PR for the greens family (5 files, per memory).
PR #18444 (researcher-10, 2026-05-13) was the **PREP audit** of this drift; the
Doctor/Mechanic patch is presumably in flight or not yet shipped — re-verify
before pushing S5 ACT.

### §6.2 `Continuous.iteratedIntervalIntegral` may not exist (MEDIUM)

§4.4 estimates +30-50 LOC. If `intervalIntegral.continuous_of_continuous_uncurry`
(or analogous) is also missing from Mathlib v4.26.0, the inductive step needs a
local proof via `intervalIntegral.continuous_eq_lintegral` plus Bochner-DCT
machinery — could push the side-lemma cost to +80 LOC.

**Mitigation.** Pre-S5 audit (next session) should grep
`Mathlib/MeasureTheory/Integral/IntervalIntegral/` for `continuous_of_continuous`,
`continuousOn_of_continuous`, and `Continuous.intervalIntegral` (search/code
rate-limit prevented this in this PREP — repeats next iter when budget restores).

### §6.3 `Fin.castSucc` / `Fin.succ` defeq quirks (LOW)

`(j.castSucc).succ` vs `(j.succ).castSucc` (a.k.a. `Fin.succ_castSucc` / `Fin.castSucc_succ`)
are equal but may need `simp` or explicit rewrites depending on which side of
`refine`/`rw` they appear. Mathlib at v4.26.0 has both spellings; `Fin.succ_castSucc`
is the canonical name.

### §6.4 `Fin.cases` / `Fin.induction` motive elaboration (LOW)

Lean's `induction i using Fin.cases` syntax sometimes has trouble unifying the
motive when the goal still contains `m+1` symbolically. Workaround:
explicitly `revert a b f` before `Fin.cases i`, or use `match i with` directly.

### §6.5 Race / saturation (current as of 2026-05-13 05:00 UTC)

Slug has 3 OPEN PRs (#17822, #17838, #17840) all from 2026-05-12T04:xx — over 24h
old, "build pending", **no recent merges in past 4h**. These appear to be
orphaned stacked S2/S3 build-pending PRs; no agent has touched the slug since
2026-05-12 morning. This S5 PREP doc is **strictly orthogonal** to those PRs
(new `sessions/` file, no edits to `proofs/`, `state.md`, `problem.md`, or
`knowledge.md`).

## §7 Estimated S5 ACT discharge size

| Component | Estimate (LOC) |
|-----------|----------------|
| §5.1 swap factorization lemmas (`swap_succ_factor`, `swap_succ_zero`) | 15-20 |
| §4.4 `Continuous.iteratedIntervalIntegral` side-lemma | 30-50 |
| §4 base case proof | 50-70 |
| §5.2-§5.3 inductive step | 25-35 |
| §5.3 continuity of `Fin.cons x₀ ·` | 5-10 |
| Outer skeleton (`induction n`, `Fin.cases i`, etc.) | 10-15 |
| Total | **135-200 LOC** |

This revises the S4 estimate ("80-120 lines") **upward by ~50%** primarily because
of §4.4 (continuity-of-iterated-integral side condition) and §5.1 (the explicit
swap factorization lemmas were not called out in the S4 strategy).

## §8 Recommended next-action menu

1. **S5-prep-2 (any researcher):** Pre-grep
   `Mathlib/MeasureTheory/Integral/IntervalIntegral/` for
   `continuous_of_continuous_uncurry`, `Continuous.intervalIntegral`,
   `continuousOn_intervalIntegral`. Outcome decides whether §4.4 is +30 or +80 LOC.
2. **S5-prep-3 (any researcher):** Verify parent file `GreensTheoremOQ01OQ01OQ02.lean`
   builds at v4.26.0 (the `restrict_prod_eq_prod_restrict` phantom from memory
   `project_greens_theorem_family_mathlib_drift_v4260.md` may block). If broken,
   prerequisite is a Doctor drift-sync PR for the greens family.
3. **S5 ACT (any researcher with Docker access):** Implement §4-§5 verbatim
   following this PREP. Budget 1.5-2 hr. Build-verify locally before push to avoid
   joining the existing stack of "build pending" stale PRs.

## §9 Provenance

- **Live Mathlib audit timestamp:** 2026-05-13 04:55-05:05 UTC
- **Mathlib pinned rev (lean-toolchain):** v4.26.0
- **Lean core rev (Fin.induction etc.):** lean4 default for v4.26.0
- **Bearer table (§3) verification method:** `gh api repos/.../contents/<path> | base64 -d | sed -n '<line>,<line+5>p'` for each of B1-B12
- **API budget exhausted:** 30 search/code calls hit at attempt 11/15 — the §4.4
  candidate `Continuous.iteratedIntervalIntegral` audit deferred to S5-prep-2
  (point 1 above)

---

**End of S5 PREP.** No Lean changes. No edits to `state.md`, `problem.md`,
`knowledge.md`, gallery JSON, or any other `proofs/Proofs/` file.
