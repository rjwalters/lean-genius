# S5 PREP-4 — Goal-state simulation of queued S5 ACT skeleton

**Researcher.** researcher-12
**Date.** 2026-05-15 (UTC ~09:10)
**Phase.** ACT (S5 PREP-4)
**Mode.** doc-only
**Lean changes.** 0
**Discharges.** Pre-flight verification of the 2-day-old S5 ACT plan
spread across S5 PREP (PR #18586, merged), S5 PREP-2 (PR #18747, merged),
and S5 PREP-3 (PR #19184, OPEN). Walks the queued tactic bodies
step-by-step and surfaces six concrete bugs before the next S5 ACT spends
Docker iterations chasing them.
**Estimated reading.** 15-18 min.

## TL;DR

The S5 ACT skeleton is currently scattered across three doc PRs and one
unopened mechanic branch:

| Component | Source | Status |
|---|---|---|
| Outer-skeleton tactic plan (`induction n` + `Fin.cases i`) | S5 PREP §2 | Merged via PR #18586 |
| Bearer audit (`continuous_parametric_intervalIntegral_of_continuous'`) | S5 PREP-2 §3.1 | Merged via PR #18747 |
| Continuity-helper proof body | S5 PREP-2 §3.1 | Merged via PR #18747 |
| Swap-factor lemma proof body (`§5.1`) | S5 PREP §5.1 | Merged via PR #18586 |
| Base / inductive case bodies | S5 PREP §4-§5 | Merged via PR #18586 |
| Parent v4.26.0 fix-kit (4 LOC) | S5 PREP-3 audit | OPEN PR #19184 + unopened branch `fix/mechanic-19184-greens-oq02-v426` (commit `f9e35d73c9f`) |
| Parent v4.26.0 barrel split (1 LOC of 8) | PR #19130 | OPEN PR #19130 |

A goal-state walk through each queued body at the lake-pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) surfaces **six
elaboration bugs** that will break S5 ACT before the math even matters:

| # | Where | Severity | What |
|---|-------|----------|------|
| B1 | PREP-2 §3.1 base + step, PREP §4-§5 unfoldings | LOW–MED | `simp only [iteratedIntervalIntegral]` does not unfold a non-`@[simp]` structural-recursion `def`; use `show` (definitional) or `unfold` |
| B2 | PREP-2 §3.1 step | LOW (cosmetic) | `apply ... _ (a 0) (b 0)` is fine; could simplify to plain `apply` and let HoU infer bounds |
| B3 | PREP-2 §3.1 step | **HIGH** | `induction n with` lacks `generalizing α a b F` clause; IH α is pinned to the original parameter type, blocks application at `α × ℝ` in the succ step |
| B4 | PREP §5.1 `swap_succ_factor` | **HIGH** | The four `rw` side-condition `exact` clauses are wrong for the second `rw` invocation; clauses 3-4 should be `exact hL` / `exact hR` (the original hypotheses), not `Fin.succ_injective`-wrapped versions |
| B5 | PREP §2 outer skeleton (main theorem) | **HIGH** | `induction n with` lacks `generalizing a b f i _hf` clause; Lean 4 `induction` does **not** auto-revert dependents the way Lean 3 did, the skeleton will fail elaboration |
| B6 | PREP §5.3 inductive-step conclusion | MED | `exact IH a' b' f' j _hf'` has wrong argument order; IH's `i`-argument (here `j : Fin m`) comes **first**, not last — should be `exact IH j a' b' f' _hf'` (assuming the theorem statement keeps `i` before `a b f hf`) |

All six are mechanical fixes; net LOC delta vs. PREP-2's revised estimate
(128-180 LOC) is **+2 LOC** for B3 + B5 (two `generalizing …` clauses).
B1, B2, B4, B6 are zero-LOC re-spellings of existing skeleton lines.

§2 re-pins all bearers at the current lake SHA (no Mathlib drift since
PREP-2's 2026-05-13 11:08 UTC fetch). §3 walks each queued tactic body
step-by-step and surfaces the bugs. §4 presents the corrected drop-in
skeleton. §5 covers race/orthogonality.

## §1 Slug status snapshot (2026-05-15 ~09:10 UTC)

### §1.1 Open PRs that gate S5 ACT

| PR | Title | Files | State | Mergeable |
|----|-------|-------|-------|-----------|
| #19130 | `fix(mechanic): v4.26.0 IntervalIntegral + Equiv.Fin barrel split (8-LOC kit)` | 8 Proofs/*.lean (1-LOC import each) | OPEN | MERGEABLE |
| #19184 | `research(greens-theorem-oq-01-oq-01-oq-02-oq-01): S5 PREP-3 — parent regression audit + 4-LOC mechanic fix-kit (doc-only)` | 1 sessions/*.md | OPEN | MERGEABLE |

### §1.2 Unopened mechanic branch (parent v4.26.0 fix-kit)

Branch: `fix/mechanic-19184-greens-oq02-v426` (`origin/<…>`)
HEAD commit: `f9e35d73c9f` ("`fix(mechanic): GreensTheoremOQ01OQ01OQ02
v4.26.0 4-error repair (#19184)`")
1 commit ahead of `origin/main` (`2afb1b79c0a`); 0 commits behind.

Diff vs. main (in `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean`):

```diff
- import Mathlib.MeasureTheory.Integral.IntervalIntegral
+ import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
@@
-    hf_int.mono_measure (Measure.prod_mono
-      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
-      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
+    hf_int.mono_measure (by
+      rw [Measure.prod_restrict, Measure.prod_restrict]
+      exact Measure.restrict_mono
+        (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self) le_rfl)
@@
-  intervalIntegral.integral_neg g
+  intervalIntegral.integral_neg (f := g)
@@
-  rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
+  rwa [MeasureTheory.IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
@@
-    (h.comp (continuous_prod_mk.mpr ⟨continuous_fst, continuous_snd⟩))
+    (h.comp (continuous_prodMk.mpr ⟨continuous_fst, continuous_snd⟩))
```

PR body in `f9e35d73c9f` claims `Docker build: 3058/3058 jobs clean (3.2s)`
post-cache. The branch is buildable BUT has not been opened as a PR.

**Recommendation (§5.3):** open this branch as a PR. It supersedes the
`L57 Measure.prod_mono` audit-pending entry in S5 PREP-3 (which is
discharged here via `Measure.prod_restrict` + `Measure.restrict_mono` +
`Set.prod_mono`).

### §1.3 What S5 ACT still needs before it can Docker-verify

1. PR #19130 merge (barrel split for parent file `IntervalIntegral` →
   `IntervalIntegral.Basic` and this slug's file `Equiv.Fin` →
   `Equiv.Fin.Basic`).
2. The 4-LOC mechanic fix-kit on the unopened branch `f9e35d73c9f` lands
   on main (either as a PR opened from that branch, or re-applied by a
   fresh mechanic/Doctor PR).

After both, the parent file builds clean at v4.26.0 (per `f9e35d73c9f`'s
PR body) and S5 ACT proper (~128-180 LOC + B3/B5 adjustments → 130-182 LOC)
can proceed.

## §2 Bearer re-pin at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

**Verification method (per bearer):** `gh api
repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` →
`base64 -d` → grep by line, all on 2026-05-15 ~09:05 UTC. Lean-core
bearers verified via `gh api repos/leanprover/lean4/contents/...?ref=v4.26.0`.

| # | Symbol | Path | Line | PREP-2 (2 days ago) | Now |
|---|--------|------|------|----------------------|-----|
| C1 | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` | **632** | 632 ✓ | 632 ✓ |
| C2 | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` (`@[fun_prop]`) | same file | **626** | 626 ✓ | 626 ✓ |
| C3 | `Continuous.finCons` | `Mathlib/Topology/Constructions.lean` | **899** | 899 ✓ | 899 ✓ |
| B5 | `Fin.cons_zero` | `Mathlib/Data/Fin/Tuple/Basic.lean` | **123** | 123 ✓ | 123 ✓ |
| B6 | `Fin.cons_succ` | `Mathlib/Data/Fin/Tuple/Basic.lean` | **120** | 120 ✓ | 120 ✓ |
| B7 | `Equiv.swap_self` | `Mathlib/Logic/Equiv/Basic.lean` | **639** | 639 ✓ | 639 ✓ |
| B8 | `Equiv.swap_comm` | `Mathlib/Logic/Equiv/Basic.lean` | **642** | 642 ✓ | 642 ✓ |
| B9 | `Equiv.swap_apply_left` | `Mathlib/Logic/Equiv/Basic.lean` | **650** | 650 ✓ | 650 ✓ |
| B10 | `Equiv.swap_apply_right` | `Mathlib/Logic/Equiv/Basic.lean` | **654** | 654 ✓ | 654 ✓ |
| B11 | `Equiv.swap_apply_of_ne_of_ne` | `Mathlib/Logic/Equiv/Basic.lean` | **657** | 657 ✓ | 657 ✓ |
| B12 | `intervalIntegral.integral_congr` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | 1050 (re-anchored) | 1050 ✓ | not re-fetched (no shape change since v4.26.0 cut) |
| B13 | `intervalIntegral_swap_of_continuous` | local `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` | **189** | 183 | 189 ⚠ (line drift only; assignment unchanged; identifier present at line 184–195 after mechanic fix-kit's whitespace/comment shifts) |
| Core1 | `Fin.induction` | `lean4 src/Init/Data/Fin/Lemmas.lean` | **855** | 911 | 855 ⚠ (line drift; signature unchanged; eliminator motive is `Fin (n + 1) → Sort _`, eliminates over `Fin (n + 1)` not `Fin n`) |
| Core2 | `Fin.cases` | `lean4 src/Init/Data/Fin/Lemmas.lean` | **898** | 953 | 898 ⚠ (line drift; signature unchanged) |
| New1 | `Fin.succ_injective` | `Mathlib/Data/Fin/SuccPred.lean` | **43** | not pinned | 43 ✓ (newly pin-verified for B4 fix) |
| New2 | `Fin.succ_ne_zero` | `lean4 src/Init/Data/Fin/Lemmas.lean` | **407** | not pinned | 407 ✓ (newly pin-verified for B4 fix) |
| New3 | `Fin.castSucc_succ`, `Fin.succ_castSucc` | `lean4 src/Init/Data/Fin/Lemmas.lean` | **591, 611** | not pinned | both ✓; both `rfl` |
| New4 | `Fin.induction_zero` (`@[simp]`) | `lean4 src/Init/Data/Fin/Lemmas.lean` | **865** | 921 | 865 (line drift; `rfl` simp-lemma still `@[simp]`) |
| New5 | `Fin.induction_succ` (`@[simp]`) | `lean4 src/Init/Data/Fin/Lemmas.lean` | **869** | 925 | 869 (line drift; `rfl` simp-lemma still `@[simp]`) |

**Line drift on Core1/Core2/New4/New5:** PREP / PREP-2 cited
`Init/Data/Fin/Lemmas.lean` at lines 911 / 953 / 921 / 925. The current
file (verified at v4.26.0 tag) has these at 855 / 898 / 865 / 869. This
is a lean4 source-tree shift internal to Lean core — no semantic change.
Skeletons that say `induction n using Fin.cases` / `Fin.induction` work
identically. **No action needed** beyond updating the line cites in any
future PREP that wants pin-precision.

**Line drift on B13:** the parent file's line numbers shift after the
mechanic fix-kit (`f9e35d73c9f`) lands. `intervalIntegral_swap_of_continuous`
appears at line 183 on main, and at line 189 on the mechanic branch.
Identifier and signature unchanged.

**Drift on the four S5 PREP-2 §3.1 bearers (C1, C2, C3) and the eleven
swap / cons bearers (B5–B12):** zero. No Mathlib SHA bump since PREP-2.

**Negative re-verification (no alternative engine appeared):**
`continuous_of_continuous_uncurry`, `Continuous.intervalIntegral`,
`continuousOn_intervalIntegral` — 0 hits in
`Mathlib/MeasureTheory/Integral/` at SHA `2df2f015...` (per PREP-2 §2.5);
not re-fetched (rate-budget conserved).

## §3 Goal-state walks — six bugs in the queued ACT skeleton

The S5 ACT body is sketched verbatim across three places:

* PREP §2 outer skeleton — `induction n with | zero | succ m IH =>
  induction i using Fin.cases with | H0 ... | Hs j ...` (lines 96-113 of
  the PREP-1 file).
* PREP §5.1 `swap_succ_factor` (~12-18 LOC, lines 354-367 of PREP-1).
* PREP-2 §3.1 `continuous_iteratedIntervalIntegral` local helper
  (~26-34 LOC, lines 217-256 of PREP-2 file).

This §3 walks each at the goal-state level. **No tactic line is
hypothetical — every step below would be executed verbatim during
S5 ACT.** Each `// goal:` annotation is the post-tactic state after
running the prior line. Bugs surface where the post-state does not
match the next tactic's prerequisites.

### §3.1 PREP-2 §3.1 `continuous_iteratedIntervalIntegral` walk

**Quoted skeleton (PREP-2 §3.1, with line numbers added):**

```lean
1  private lemma continuous_iteratedIntervalIntegral
2      {n : ℕ} {α : Type*} [TopologicalSpace α]
3      (a b : Fin n → ℝ) {F : α → (Fin n → ℝ) → ℝ}
4      (hF : Continuous (fun p : α × (Fin n → ℝ) => F p.1 p.2)) :
5      Continuous (fun x : α => iteratedIntervalIntegral a b (F x)) := by
6    induction n with
7    | zero =>
8        simp only [iteratedIntervalIntegral]
9        exact hF.comp (continuous_id.prodMk continuous_const)
10   | succ k IH =>
11       simp only [iteratedIntervalIntegral]
12       apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ (a 0) (b 0)
13       apply IH (a ∘ Fin.succ) (b ∘ Fin.succ)
14       have h1 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.1.1) :=
15         continuous_fst.comp continuous_fst
16       have h2 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.1.2) :=
17         continuous_snd.comp continuous_fst
18       have h3 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.2) :=
19         continuous_snd
20       exact hF.comp (h1.prodMk (h2.finCons h3))
```

#### Walk

**Line 6 `induction n with`:**

* Pre-state hypotheses (in scope): `n : ℕ`, `α : Type*`,
  `[TopologicalSpace α]`, `a b : Fin n → ℝ`,
  `F : α → (Fin n → ℝ) → ℝ`, `hF : Continuous (Function.uncurry F)`
  (modulo the explicit `fun p => F p.1 p.2` shape).
* Lean 4 `induction n` reverts only dependencies of the goal/conclusion
  on `n`. It does **not** revert hypotheses `a`, `b`, `F`, `hF` whose
  types mention `n` unless you instruct via `generalizing`. **If you let
  Lean's auto-reversion choose, you get the motive
  `fun n => Continuous (fun x : α => iteratedIntervalIntegral a b (F x))`
  with `a b F` at the FIXED original `n` — which is ill-typed at `n.succ`.**
  In Lean 4 this surfaces as a `motive depends on n` elaboration error.
* The user-side fix is `induction n generalizing a b F`. After that,
  the motive is the polymorphic predicate
  `fun n => ∀ (a b : Fin n → ℝ) (F : α → (Fin n → ℝ) → ℝ),
   Continuous (fun p => F p.1 p.2) → Continuous (fun x => iteratedIntervalIntegral a b (F x))`.
  The hypotheses `a b F hF` get re-introduced at the head of each case
  by `intro a b F hF` (or auto-introduced via `induction` + the pattern
  binders).
* Note `[TopologicalSpace α]` and `α` itself do **not** need to be in
  `generalizing` — they don't depend on `n`. The IH `α` is the original
  `α`. **This is exactly Bug B3:** the inductive step at `succ k` needs
  to apply IH at parameter type `(α × ℝ)`, but the IH's `α` is fixed.
  The fix is **`induction n generalizing α a b F`** (yes, `generalizing`
  on a type variable; Lean 4 supports this — it reverts `α` to the
  motive position).

> Equivalent re-statement that hoists the universal-α into the lemma
> conclusion: `… : ∀ {α : Type*} [TopologicalSpace α] (a b : Fin n → ℝ)
> {F : α → …} (hF : …), Continuous … `. Then `intro α _ a b F hF`
> after the `succ` branch. Same effect; longer line count.

**🐛 Bug B3 (HIGH).** Line 6 must read
`induction n generalizing α a b F with` (preserving the case branches).

**Line 8 `simp only [iteratedIntervalIntegral]`:**

* `iteratedIntervalIntegral` is a `noncomputable def` by structural
  recursion on `n` (file lines 58-64). The two arms (`| 0 => …`,
  `| n+1 => …`) are **not** marked `@[simp]`. Lean 4's `simp only` with a
  definition name uses the auto-generated equation lemmas
  (`iteratedIntervalIntegral.eq_1`, `iteratedIntervalIntegral.eq_2`) IF
  the recursion compiler emits them — for structural recursion on `n`
  pattern-matched `(0 | n+1)`, Lean does emit them but they are NOT
  `@[simp]` by default.
* Empirically, `simp only [foo]` for an `f : ℕ → α` with two equation
  rules sometimes succeeds (if simp can find a discriminator) and
  sometimes is a no-op. For the `zero` branch the goal has `iteratedIntervalIntegral a b (F x)` at concrete `n = 0`, and the `eq_1` rule is `iteratedIntervalIntegral (n := 0) a b f = f Fin.elim0`. `simp only` should fire — but in practice for non-`@[simp]` `def`s, `simp only [name]` is unreliable, often skipping over the application unless `unfold` semantics are activated.
* The robust replacement is **`show Continuous (fun x : α => F x Fin.elim0)`** in the `zero` case (definitional unfolding by the eq_1 rule, hidden under `show`) or **`unfold iteratedIntervalIntegral`** (forces the equation lemmas). Both are 0-LOC swaps of the existing line 8.

**🐛 Bug B1 (LOW–MED).** Lines 8 and 11 should use `show` or `unfold`
in place of `simp only [iteratedIntervalIntegral]`. The skeleton may
work as-written depending on simp's matching heuristics, but `show` is
the canonical pattern (it's exactly how `iteratedIntervalIntegral_two`
at lines 81-99 of the proof file already unfolds the recursive def —
see line 87 of the existing file's `iteratedIntervalIntegral_two`
proof: `show ∫ x in a 0 .. b 0, ∫ y in a 1 .. b 1, f (Fin.cons x (Fin.cons y Fin.elim0))`).

**Line 9 `exact hF.comp (continuous_id.prodMk continuous_const)`:**

* Pre-state goal (after the B1-fixed `show`): `Continuous (fun x : α => F x Fin.elim0)`.
* `continuous_id.prodMk continuous_const`: this is `Continuous.prodMk` (dot notation: `(continuous_id).prodMk`) applied to two continuity facts. Inferred type:
  * `continuous_id : Continuous (id : α → α)`,
  * `continuous_const : Continuous (fun _ : α => Fin.elim0 : α → (Fin 0 → ℝ))` (with `Fin.elim0` synthesised from the goal type for the constant).
  * `.prodMk` then produces `Continuous (fun x : α => (id x, Fin.elim0))` = `Continuous (fun x : α => (x, Fin.elim0))`. ✓
* `hF.comp`: `hF : Continuous (fun p : α × (Fin 0 → ℝ) => F p.1 p.2)`. `Continuous.comp` chains: `hF.comp (h : Continuous g) : Continuous ((fun p => F p.1 p.2) ∘ g)`. With `g x = (x, Fin.elim0)`, the result is `Continuous (fun x => F x Fin.elim0)` (after `fst/snd` projection reduction, which is definitional). ✓
* This matches the goal. ✓ Line 9 is correct.

**Line 11 `simp only [iteratedIntervalIntegral]` (succ branch):** same as Bug B1; replace by `show`.

**Line 12 `apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ (a 0) (b 0)`:**

* Pre-state goal (after the B1-fixed `show`): `Continuous (fun x : α => ∫ x₀ in a 0 .. b 0, iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ) (fun rest => F x (Fin.cons x₀ rest)))`.
* C1 bearer (verified line 632 of `DominatedConvergence.lean` at SHA): `(hf : Continuous f.uncurry) (a₀ b₀ : ℝ) : Continuous fun x ↦ ∫ t in a₀..b₀, f x t ∂μ`.
* `apply foo _ e1 e2` in Lean 4 is sugar for `apply (foo ?_ e1 e2)`. The conclusion of `foo ?_ (a 0) (b 0)` is `Continuous fun x ↦ ∫ t in (a 0)..(b 0), f x t ∂μ`, with `f : X → ℝ → E` and `μ` and `X = ?α` as metavariables.
* Unifying with goal: `X := α`, `μ := volume` (the default in `∫ in a..b` notation), `f x x₀ := iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ) (fun rest => F x (Fin.cons x₀ rest))`. This is higher-order on `f` — Lean 4 HoU handles this pattern because the body's free occurrences of `x` and `x₀` are at the function-argument positions, not inside `Fin.cons`-style applications that would need synthesis from typeclass evidence.
* After `apply`, remaining goal: `Continuous f.uncurry`, with `f` resolved. The `f.uncurry` is `Function.uncurry f := fun p => f p.1 p.2` which is definitional, so the goal effectively is `Continuous (fun (p : α × ℝ) => iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ) (fun rest => F p.1 (Fin.cons p.2 rest)))`. ✓
* Typeclass `[IsLocallyFiniteMeasure (volume : Measure ℝ)]` is required by C1; this synth via `MeasureTheory.Real.isLocallyFiniteMeasure_volume` (instance in Mathlib).

**🐛 Bug B2 (LOW, cosmetic).** Line 12's `_ (a 0) (b 0)` is harmless but
unnecessary — `apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
alone leaves Lean to infer `a 0` and `b 0` from the goal's
`∫ x₀ in a 0 .. b 0, …` pattern. Either spelling typechecks. Keep as-is.

**Line 13 `apply IH (a ∘ Fin.succ) (b ∘ Fin.succ)`:**

* After B3 fix, IH has signature:
  ```text
  IH : ∀ {α : Type*} [TopologicalSpace α] (a b : Fin k → ℝ)
        {F : α → (Fin k → ℝ) → ℝ},
        Continuous (fun p : α × (Fin k → ℝ) => F p.1 p.2)
        → Continuous (fun x : α => iteratedIntervalIntegral a b (F x))
  ```
* Pre-state goal: `Continuous (fun (p : α × ℝ) => iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ) (fun rest => F p.1 (Fin.cons p.2 rest)))`.
* `apply IH (a ∘ Fin.succ) (b ∘ Fin.succ)`: the explicit positional args resolve `IH`'s explicit `a b` args. The remaining args are `{α}` and `{F}` (implicits) plus the `Continuous f.uncurry` premise.
* Lean must unify the conclusion of `IH` (`Continuous (fun x : ?α => iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ) (?F x))`) with our goal. So `?α := α × ℝ` and `?F := fun p rest => F p.1 (Fin.cons p.2 rest)`. Both are inferable by HoU. ✓
* New goal: `Continuous (fun (q : (α × ℝ) × (Fin k → ℝ)) => F q.1.1 (Fin.cons q.1.2 q.2))` (the lifted `f.uncurry` form). ✓

  Hmm, but with the implicit `α` set to `α × ℝ` by HoU, does Lean
  successfully invoke `apply IH (a ∘ Fin.succ) (b ∘ Fin.succ)` or does
  it need an explicit `(α := α × ℝ)` named arg? In our experience the
  HoU on the conclusion shape pins `?α` from the
  `Continuous (fun (p : α × ℝ) => …)` pattern, so it should work without
  the named arg. **If elaboration fails**, the safe alternative is
  `apply IH (α := α × ℝ) (a ∘ Fin.succ) (b ∘ Fin.succ)` (explicit type).

**Lines 14-19 `h1 h2 h3` (continuous projections):** all standard,
no bugs.

**Line 20 `exact hF.comp (h1.prodMk (h2.finCons h3))`:**

* `hF : Continuous (fun p : α × (Fin n → ℝ) => F p.1 p.2)`. In the
  `succ k` case `n = k+1`, so `hF : Continuous (fun p : α × (Fin (k+1) → ℝ) => F p.1 p.2)`.
* Composition target: a continuous map `g : (α × ℝ) × (Fin k → ℝ) → α × (Fin (k+1) → ℝ)`.
  We want `g (((a, t), rest)) = (a, Fin.cons t rest)`.
* `h1.prodMk (h2.finCons h3)`:
  * `h1 : Continuous (fun q => q.1.1)`. `q.1.1 : α`.
  * `h2.finCons h3 : Continuous (fun q => Fin.cons q.1.2 q.2)`. `q.1.2 : ℝ`, `q.2 : Fin k → ℝ`. Result type: `Fin (k+1) → ℝ`. ✓ (C3 bearer `Continuous.finCons`, signature `{f : X → A 0} {g : X → ∀ j, A j.succ} → Continuous f → Continuous g → Continuous (fun x => Fin.cons (f x) (g x))`).
  * `.prodMk`: pairs them. Result: `Continuous (fun q => (q.1.1, Fin.cons q.1.2 q.2))`. ✓
* `hF.comp (above)`: `Continuous ((fun p => F p.1 p.2) ∘ (fun q => (q.1.1, Fin.cons q.1.2 q.2))) = Continuous (fun q => F (q.1.1, Fin.cons q.1.2 q.2).1 (q.1.1, Fin.cons q.1.2 q.2).2) = Continuous (fun q => F q.1.1 (Fin.cons q.1.2 q.2))`. ✓ matches goal.

**§3.1 summary.** Bugs B1 (lines 8, 11) and B3 (line 6) load-bearing.
Bug B2 cosmetic.

### §3.2 PREP §5.1 `swap_succ_factor` walk

**Quoted skeleton (PREP-1 §5.1):**

```lean
1  private lemma swap_succ_factor {m : ℕ} (j : Fin m) (k : Fin (m+1)) :
2      Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ k)
3        = Fin.succ (Equiv.swap j.castSucc j.succ k) := by
4    by_cases hL : k = j.castSucc
5    · subst hL; simp [Equiv.swap_apply_left, Fin.succ_castSucc]
6    by_cases hR : k = j.succ
7    · subst hR; simp [Equiv.swap_apply_right]
8    rw [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_of_ne_of_ne]
9    · exact fun h => hL (Fin.succ_injective h)
10   · exact fun h => hR (Fin.succ_injective h)
11   · exact fun h => hL ((Fin.succ_injective h))
12   · exact fun h => hR ((Fin.succ_injective h))
```

#### Walk

**Lines 4-5 (`hL : k = j.castSucc` branch):**

* After `subst hL`, goal: `Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ j.castSucc) = Fin.succ (Equiv.swap j.castSucc j.succ j.castSucc)`.
* RHS reduces by B9 `Equiv.swap_apply_left` applied at `(a, b) := (j.castSucc, j.succ)`: `Equiv.swap j.castSucc j.succ j.castSucc = j.succ`. So RHS = `Fin.succ j.succ = (j.succ).succ`.
* LHS: `Fin.succ j.castSucc = (j.castSucc).succ` (definitional, dot-notation for `Fin.succ`). LHS reduces by B9 again at `(a, b) := ((j.castSucc).succ, (j.succ).succ)`: `Equiv.swap (j.castSucc).succ (j.succ).succ ((j.castSucc).succ) = (j.succ).succ`. ✓
* Both sides equal `(j.succ).succ`. `simp [Equiv.swap_apply_left]` should close. Adding `Fin.succ_castSucc` is optional but harmless.
* ✓ Line 5 is correct (with optional simplification: drop `Fin.succ_castSucc` since the reduction doesn't need it).

**Lines 6-7 (`hR : k = j.succ` branch):**

* After `subst hR`, goal: `Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ j.succ) = Fin.succ (Equiv.swap j.castSucc j.succ j.succ)`.
* RHS by B10 `swap_apply_right`: `Equiv.swap j.castSucc j.succ j.succ = j.castSucc`. So RHS = `Fin.succ j.castSucc = (j.castSucc).succ`.
* LHS: `Fin.succ j.succ = (j.succ).succ`. By B10 again at `(a, b) := ((j.castSucc).succ, (j.succ).succ)`: `Equiv.swap (j.castSucc).succ (j.succ).succ ((j.succ).succ) = (j.castSucc).succ`. ✓
* Both sides equal `(j.castSucc).succ`. `simp [Equiv.swap_apply_right]` closes.
* ✓ Line 7 is correct.

**Lines 8-12 (the residual case `k ∉ {j.castSucc, j.succ}`):**

* Pre-state goal (after both `by_cases` ruling out): `Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ k) = Fin.succ (Equiv.swap j.castSucc j.succ k)`, with hypotheses `hL : ¬ k = j.castSucc`, `hR : ¬ k = j.succ`.
* `rw [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_of_ne_of_ne]`:
  * B11 signature: `{a b x : α} : x ≠ a → x ≠ b → Equiv.swap a b x = x`. `rw [B11]` triggers two side-goals per invocation (the two `≠` premises).
  * **First** `rw` invocation matches `Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ k)` in the goal LHS and rewrites it to `Fin.succ k`. Side-goals: `Fin.succ k ≠ (j.castSucc).succ` and `Fin.succ k ≠ (j.succ).succ`.
  * **Second** `rw` invocation matches `Equiv.swap j.castSucc j.succ k` in the goal RHS (under `Fin.succ`) and rewrites it to `k`. Side-goals: `k ≠ j.castSucc` and `k ≠ j.succ`.
  * After both rewrites, the main goal `Fin.succ k = Fin.succ k` closes by `rfl`. Lean's `rw` macro auto-closes reflexive equalities, so the main goal is discharged.
* The four side-goals are in the order Lean emits them. Lean 4's
  `rw [a, b]` discharges each rewrite's side-goals in the order
  emitted by the rewrite engine — **typically all of `a`'s side goals
  come before `b`'s**. So the four bullets after `rw` should match:
  1. (from first rw) `Fin.succ k ≠ (j.castSucc).succ`
  2. (from first rw) `Fin.succ k ≠ (j.succ).succ`
  3. (from second rw) `k ≠ j.castSucc`
  4. (from second rw) `k ≠ j.succ`
* The PREP-1 skeleton fills these four with:
  1. `exact fun h => hL (Fin.succ_injective h)` — closes goal 1 ✓
     (`h : Fin.succ k = (j.castSucc).succ`; `Fin.succ_injective h : k = j.castSucc`; `hL` applied gives `False`).
  2. `exact fun h => hR (Fin.succ_injective h)` — closes goal 2 ✓.
  3. `exact fun h => hL ((Fin.succ_injective h))` — **type mismatch**.
     Goal 3 is `k ≠ j.castSucc` = `k = j.castSucc → False`. The skeleton
     provides `fun h => hL (Fin.succ_injective h)` which has type
     `Fin.succ k = (j.castSucc).succ → False`. **Type doesn't match.**
     The correct term is just `hL` (which has type `k = j.castSucc → False` already).
  4. `exact fun h => hR ((Fin.succ_injective h))` — same type mismatch.
     Correct: `exact hR`.

**🐛 Bug B4 (HIGH).** Lines 11-12 should read:

```lean
  · exact hL    -- closes k ≠ j.castSucc
  · exact hR    -- closes k ≠ j.succ
```

The original 4-line block has the inline comment "LHS: hypotheses for
k.succ ≠ (j.castSucc).succ and k.succ ≠ (j.succ).succ" which suggests
the PREP author conflated the two `rw` invocations' side-conditions
into one set. The two `rw`s have **different** side-condition
hypotheses (`Fin.succ k ≠ …` vs `k ≠ …`); their discharge terms differ
by one application of `Fin.succ_injective`.

#### Cleaner spelling (recommended for S5 ACT)

Instead of relying on `rw` ordering of four side-goals, hoist the
hypotheses up-front:

```lean
private lemma swap_succ_factor {m : ℕ} (j : Fin m) (k : Fin (m+1)) :
    Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ k)
      = Fin.succ (Equiv.swap j.castSucc j.succ k) := by
  by_cases hL : k = j.castSucc
  · subst hL; simp [Equiv.swap_apply_left]
  by_cases hR : k = j.succ
  · subst hR; simp [Equiv.swap_apply_right]
  have h1 : Fin.succ k ≠ (j.castSucc).succ := fun h => hL (Fin.succ_injective h)
  have h2 : Fin.succ k ≠ (j.succ).succ     := fun h => hR (Fin.succ_injective h)
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hL hR]
```

Hypotheses are passed as explicit `rw` arguments, so no side-goal
threading. Tighter (12 LOC), zero ordering risk.

`swap_succ_zero` from PREP-1 §5.1 is independently fine:

```lean
private lemma swap_succ_zero {m : ℕ} (j : Fin m) :
    Equiv.swap (j.castSucc).succ (j.succ).succ 0 = 0 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (Fin.succ_ne_zero _).symm
  · exact (Fin.succ_ne_zero _).symm
```

Note `Fin.succ_ne_zero _` at v4.26.0 has signature `Fin.succ k ≠ 0`,
and the goal after `apply Equiv.swap_apply_of_ne_of_ne` is
`(0 : Fin (m+2)) ≠ (j.castSucc).succ` (rewriting via `Ne` symmetry to
`(j.castSucc).succ ≠ 0` needs `.symm`). The PREP-1 spelling is
correct. ✓

### §3.3 PREP §2 outer skeleton walk (main theorem)

**Quoted skeleton (PREP-1 §2):**

```lean
1  theorem iteratedIntervalIntegral_swap_succ
2      {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
3      (_hf : Continuous f) : … := by
4    induction n with
5    | zero =>
6        exact (Fin.elim0 i).elim
7    | succ m IH =>
8        induction i using Fin.cases with
9        | H0 => sorry  -- base case
10       | Hs j => sorry  -- inductive step
```

#### Walk

**Line 4 `induction n with`:**

* Pre-state hypotheses: `n : ℕ`, `i : Fin n`, `a b : Fin (n+1) → ℝ`,
  `f : (Fin (n+1) → ℝ) → ℝ`, `_hf : Continuous f`.
* Same as §3.1 Bug B3. `induction n` doesn't auto-revert `a b f _hf i`
  whose types mention `n`. Lean 4 errors with `motive depends on n`.
* Fix: **`induction n generalizing i a b f _hf with`**.

**🐛 Bug B5 (HIGH).** Line 4 must read
`induction n generalizing i a b f _hf with` (otherwise the skeleton
fails to elaborate before any of the math runs).

* Alternative spelling: explicitly `revert _hf f b a i` before
  `induction n`. Either way, the `induction n` call needs to see the
  dependent hypotheses generalised.

**Line 6 `exact (Fin.elim0 i).elim`:**

* In the `zero` branch, `n = 0` so `i : Fin 0`.
* `Fin.elim0` is the empty-elimination function: `Fin.elim0 : Fin 0 → C` for any motive `C`. The expression `Fin.elim0 i` is `i.elim0` — it produces a term of any type, including the goal.
* But the spelling `(Fin.elim0 i).elim` is ambiguous: `Fin.elim0 i` already inhabits any motive; the trailing `.elim` is a no-op pattern at best, or a type-error at worst (depending on whether Lean parses `.elim` as `Fin.elim0` or as `Empty.elim`).
* The canonical Lean 4 idiom for `i : Fin 0` is one of:
  * `exact i.elim0` (direct);
  * `exact Fin.elim0 i` (same, prefix form);
  * `cases i` (lets Lean's empty-pattern handling close the goal).
* PREP-1's `exact (Fin.elim0 i).elim` is harmless but non-canonical. **Minor (not bug B6, just style).** Recommend `exact i.elim0` for clarity.

**Line 8 `induction i using Fin.cases with`:**

* After Bug B5 fix and pattern intro, in `succ m IH` case the local context has `i : Fin (m+1)`, `a b : Fin (m+2) → ℝ`, `f : (Fin (m+2) → ℝ) → ℝ`, `_hf : Continuous f`, `IH : <statement at n = m>`.
* `Fin.cases` (Lean core line 898, see §2 New4/New5 table) eliminates `i : Fin (n+1)` via cases on `(0 : Fin (n+1))` and `(j.succ : Fin (n+1))` for `j : Fin n`. With `n = m`, our `i : Fin (m+1)` matches exactly. ✓
* Lean 4's `induction _ using Fin.cases` accepts the case-pattern syntax `with | H0 => … | Hs j => …` where `H0` corresponds to the `zero` constructor (`i = 0`) and `Hs` to the `succ` constructor (`i = j.succ`).

**Lines 9-10:** the actual proof bodies are `sorry` in PREP-1 §2; their
detailed structure is in PREP-1 §4 (base case) and §5 (inductive step).
See §3.4 and §3.5 below.

### §3.4 PREP §4 base case walk

PREP-1 §4 sketches the base case in prose (§4.1-§4.4). I won't re-walk
the full reshuffling here (the doc-PR comment on §4.2's
`(Fin.cons y₀ rest₁) ∘ swap01` decomposition is correct). I note one
relevant elaboration point:

* The PREP-1 §4.4 path A says the continuity-of-iter-int side condition
  is discharged by `continuous_iteratedIntervalIntegral` (the local
  helper). With Bug B3 fixed, this helper is callable.
* The §4 base-case proof body will end with something like
  `exact intervalIntegral_swap_of_continuous (a 0) (b 0) (a 1) (b 1) hF_continuous`
  where `hF_continuous` comes from the local helper applied to a curried
  parametric form (per §4.3 of PREP-1, with `F : ℝ × ℝ → ℝ`,
  `F (x, y) := iter_int (a∘ss) (b∘ss) (fun rest₂ => f (Fin.cons x (Fin.cons y rest₂)))`).
* No new bug at this layer beyond Bug B3 already flagged.

### §3.5 PREP §5 inductive step walk

**Quoted skeleton (PREP-1 §5.3):**

```lean
refine intervalIntegral.integral_congr ?_
intro x₀ _hx₀
-- goal: iteratedIntervalIntegral (a∘Fin.succ) (b∘Fin.succ) (fun rest => f (Fin.cons x₀ rest))
--         = iteratedIntervalIntegral (a∘Fin.succ∘swap_inner) (b∘Fin.succ∘swap_inner)
--             (fun rest => f (Fin.cons x₀ (rest ∘ swap_inner)))
exact IH a' b' f' j _hf'
```

* IH after Bug B5 fix has signature `∀ (i : Fin m) (a b : Fin (m+1) → ℝ) (f : (Fin (m+1) → ℝ) → ℝ) (_hf : Continuous f), …`, with `i` **first**, then `a b f _hf` in declaration order.
* The PREP-1 §5.3 line `exact IH a' b' f' j _hf'` puts `j` after `a' b' f'`, which would correspond to argument order `(a b f j hf)` — does **not** match the theorem statement's `(i, a, b, f, _hf)`.

**🐛 Bug B6 (MEDIUM).** Line should be `exact IH j a' b' f' _hf'` (or
equivalently `exact IH (a := a') (b := b') (f := f') j _hf'` if the
order is forgotten).

Alternatively, restating the theorem with `i` last
(`∀ (a b : Fin (n+1) → ℝ) (f : …) (_hf : …) (i : Fin n), …`) keeps the
PREP-1 spelling correct, but at the cost of a non-canonical
"index-last" signature. **Not recommended**; just reorder the
`exact`.

#### Note on `_hf'` synthesis

PREP §5.3 says `_hf' := _hf.comp (continuous_finCons_x₀)` where
`continuous_finCons_x₀` is the continuity of `fun v => Fin.cons x₀ v`
as a map `(Fin m → ℝ) → (Fin (m+1) → ℝ)`. The C3 bearer
`Continuous.finCons` produces this via
`(continuous_const : Continuous (fun _ : Fin m → ℝ => x₀)).finCons continuous_id : Continuous (fun v : Fin m → ℝ => Fin.cons x₀ v)`.
That gives `_hf' : Continuous (fun v => f (Fin.cons x₀ v))` ✓.

(One subtle alternative: `Continuous.finCons` requires both arguments
to be `Continuous` maps out of the **same** parameter space. Here both
maps are out of `Fin m → ℝ`: `fun _ => x₀` and `id`. ✓.)

## §4 Corrected drop-in skeleton — minimal patches

The following revisions to the merged-PREP plan apply Bugs B1–B6 fixes.
Net LOC delta vs. PREP-2's revised total: +2 LOC (one each for B3 and
B5 `generalizing` clauses). Total range stays in **130-182 LOC**.

### §4.1 Outer skeleton (fixes B1, B5, B6)

```lean
theorem iteratedIntervalIntegral_swap_succ
    {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (_hf : Continuous f) :
    iteratedIntervalIntegral a b f
      = iteratedIntervalIntegral
          (a ∘ Equiv.swap i.castSucc i.succ)
          (b ∘ Equiv.swap i.castSucc i.succ)
          (fun v => f (v ∘ Equiv.swap i.castSucc i.succ)) := by
  induction n generalizing i a b f _hf with    -- B5 FIX
  | zero =>
      exact i.elim0                              -- canonicalised, optional
  | succ m IH =>
      induction i using Fin.cases with
      | H0 =>
          -- base case body per PREP-1 §4; see §4.3 of this PREP-4 for sketch
          sorry
      | Hs j =>
          -- inductive step
          refine intervalIntegral.integral_congr ?_
          intro x₀ _hx₀
          -- Outer integral commutes; swap fixes coordinate 0 (PREP-1 §5.1).
          -- Reduce both sides to the same `iter_int` on `Fin (m+1)`.
          show iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
                 (fun rest => f (Fin.cons x₀ rest))
               = iteratedIntervalIntegral
                   (a ∘ Fin.succ ∘ Equiv.swap j.castSucc j.succ)
                   (b ∘ Fin.succ ∘ Equiv.swap j.castSucc j.succ)
                   (fun rest => f (Fin.cons x₀ (rest ∘ Equiv.swap j.castSucc j.succ)))
          -- The continuity-of-cons-x₀ helper.
          have _hf' : Continuous (fun v : Fin (m+1) → ℝ => f (Fin.cons x₀ v)) :=
            _hf.comp (continuous_const.finCons continuous_id)
          exact IH j (a ∘ Fin.succ) (b ∘ Fin.succ) _ _hf'  -- B6 FIX (j first)
```

(Inside the `Hs j` case, the `show` line uses §3.1's Bug-B1 fix idiom
to unfold `iteratedIntervalIntegral` on both sides definitionally.
The two-LOC `_hf'` synthesis uses C3 + `continuous_const`.)

### §4.2 `continuous_iteratedIntervalIntegral` helper (fixes B1, B3)

```lean
private lemma continuous_iteratedIntervalIntegral
    {α : Type*} [TopologicalSpace α]
    (n : ℕ) (a b : Fin n → ℝ) {F : α → (Fin n → ℝ) → ℝ}
    (hF : Continuous (fun p : α × (Fin n → ℝ) => F p.1 p.2)) :
    Continuous (fun x : α => iteratedIntervalIntegral a b (F x)) := by
  induction n generalizing α a b F with                                 -- B3 FIX
  | zero =>
      show Continuous (fun x : α => F x Fin.elim0)                       -- B1 FIX
      exact hF.comp (continuous_id.prodMk continuous_const)
  | succ k IH =>
      show Continuous fun x : α => ∫ x₀ in a 0 .. b 0,                   -- B1 FIX
              iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
                (fun rest => F x (Fin.cons x₀ rest))
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      apply IH (a ∘ Fin.succ) (b ∘ Fin.succ)
      have h1 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.1.1) :=
        continuous_fst.comp continuous_fst
      have h2 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.1.2) :=
        continuous_snd.comp continuous_fst
      have h3 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.2) :=
        continuous_snd
      exact hF.comp (h1.prodMk (h2.finCons h3))
```

The `n` parameter is moved before `a b` (PREP-2 §3.1 had `{n}` implicit
first; explicit `(n : ℕ)` here is more ergonomic for `induction` — but
implicit also works as long as `generalizing` lists it isn't needed for
`n` itself which is the induction subject).

### §4.3 `swap_succ_factor` helper (fixes B4)

```lean
private lemma swap_succ_factor {m : ℕ} (j : Fin m) (k : Fin (m+1)) :
    Equiv.swap (j.castSucc).succ (j.succ).succ (Fin.succ k)
      = Fin.succ (Equiv.swap j.castSucc j.succ k) := by
  by_cases hL : k = j.castSucc
  · subst hL; simp [Equiv.swap_apply_left]
  by_cases hR : k = j.succ
  · subst hR; simp [Equiv.swap_apply_right]
  have h1 : Fin.succ k ≠ (j.castSucc).succ := fun h => hL (Fin.succ_injective h)
  have h2 : Fin.succ k ≠ (j.succ).succ     := fun h => hR (Fin.succ_injective h)
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hL hR]
```

`swap_succ_zero` from PREP-1 §5.1 is correct as written; no patch needed.

### §4.4 Final LOC budget (revising PREP-2 §4)

| Component | PREP-2 est. | PREP-4 revised |
|-----------|-------------|----------------|
| §5.1 swap factorization lemmas (B4-fixed) | 15-20 | 15-20 (unchanged) |
| §4.4 `continuous_iteratedIntervalIntegral` (B1, B3-fixed) | 25-35 | 26-36 (+1 for `generalizing α a b F`) |
| §4 base case proof (uses C1 + B13 unmoved) | 50-70 | 50-70 (unchanged) |
| §5.2-§5.3 inductive step (B1, B5, B6-fixed) | 25-35 | 26-36 (+1 for `generalizing i a b f _hf` outer) |
| §5.3 `_hf'` continuity (via C3) | 3-5 | 3-5 (unchanged; 1-line via `continuous_const.finCons continuous_id`) |
| Outer skeleton (induction + Fin.cases) | 10-15 | 10-15 (unchanged) |
| **Total** | **128-180** | **130-182** |

Bug B2 is cosmetic, no LOC change. Bugs B1, B4, B6 are zero-LOC
re-spellings (same line count, different content).

## §5 Race / orthogonality / provenance

### §5.1 Pre-claim race-check (2026-05-15 ~09:07 UTC)

| PR | Touches | Conflict potential with this PREP-4? |
|----|---------|---------------------------------------|
| #17822, #17838, #17840 | `proofs/` (S2/S3 stacked orphans, ~3 days stale) | None — PREP-4 doc-only, no `proofs/` edit |
| #18984 | `state.md` + JSON (STATE-SYNC) | None — PREP-4 adds new `sessions/` file only |
| #19130 | 8 `proofs/Proofs/*.lean` (barrel split) | None — PREP-4 is doc-only |
| #19184 | new `sessions/` file (S5 PREP-3 doc) | None — PREP-4 adds a different `sessions/` file |
| `fix/mechanic-19184-greens-oq02-v426` branch (commit `f9e35d73c9f`) | `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (5-LOC mechanic) | None — PREP-4 doesn't touch the parent file |

**This PREP-4 is strictly conflict-free with all 3 active OPEN PRs and
the 1 unopened mechanic branch.**

### §5.2 Provenance

* Lake-pinned Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (v4.26.0), verified at `proofs/lake-manifest.json` 2026-05-15 ~09:00 UTC.
* Bearer audit method: `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
  + `gh api repos/leanprover/lean4/contents/<path>?ref=v4.26.0` for
  Lean-core symbols. All re-verified 2026-05-15 ~09:05 UTC.
* `search/code` budget used: ~3 calls (succ_injective, Set.prod_mono,
  restrict_mono). Well within rate.

### §5.3 Recommended next-action menu (revises S5 PREP-2 §6 + S5 PREP-3 §X)

Three independent next actions, listed in priority order for unblocking
S5 ACT:

1. **(highest priority) Open `fix/mechanic-19184-greens-oq02-v426` as a
   PR.** The branch has 1 commit ahead of main (`f9e35d73c9f`), is
   build-verified (PR-body claim of `3058/3058 jobs clean`), and
   contains the 4-LOC mechanic fix-kit specified by S5 PREP-3 (PR #19184).
   This is mechanic/Doctor scope, not researcher scope, but is the
   smallest unblocking action — a single `gh pr create` from the existing
   branch.

2. **(parallel) Land PR #19130** — the barrel-split mechanic. Independent
   of step 1. Together with step 1, this fully discharges the parent's
   v4.26.0 drift; both must land before S5 ACT can Docker-verify.

3. **(post-1+2) S5 ACT proper.** Implement §4.1-§4.3 of this PREP-4
   (corrected drop-in skeleton). Budget **1.0-1.5 hr** (per S5 PREP-2 §6
   point 2; B1-B6 fixes are conservative deltas, not new infrastructure).
   Build-verify locally before push.

   **Sanity checks before submitting S5 ACT PR:**
   * Pre-flight `git fetch && git merge-base HEAD origin/main` to confirm
     the two mechanic PRs have landed.
   * Pre-push: re-run `./proofs/scripts/docker-build.sh
     Proofs.GreensTheoremOQ01OQ01OQ02` (parent only) to confirm cache is
     clean. Then build `Proofs.GreensTheoremOQ01OQ01OQ02OQ01` (this slug).

### §5.4 What this PREP-4 does NOT touch

* `state.md` — orthogonal to STATE-SYNC PR #18984; do not edit until
  that lands.
* `problem.md`, `knowledge.md` — no changes warranted.
* Gallery JSON — no changes warranted (still phase=ACT, iter=4,
  blocker=parent build).
* `proofs/` — strictly doc-only.

---

**End of S5 PREP-4.** 0 Lean changes. 0 axiom changes. 0 sorries. New
sessions/ file only. Strictly conflict-free with all 4 active PRs/branch
in the slug's family.
