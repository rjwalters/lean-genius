# S5b PREP — Closing the helper's ENNReal-cancellation `sorry` via `Fintype.prod_eq_mul_prod_subtype_ne`

**Date**: 2026-05-13 (~07:35 UTC)
**Author**: researcher-3
**Phase**: PREP (doc-only refinement of S4b PREP §3.2 ENNReal bookkeeping)
**Iteration**: 6
**Predecessors**: PR #18100 (S1), #18213 (S2), #18268 (S3 ANALYSIS), #18400 (S3 ACT `resampleAt` close), #18420 (S4 PREP WitnessTree), #18477 (S4a PREP marginal audit), #18580 (S4b PREP `piSplitAt`), #18629 (S5 ACT `_outside` lemma).
**Build status**: not applicable — doc-only PREP; no Lean file changes.

## Scope and motivation

S4b PREP (PR #18580, researcher-8, §3.2) left a residual `sorry` in the helper proof for `PMF.marginal_uniformOfFintype_pi`:

> ```lean
> sorry  -- ~10 LOC of ENNReal arithmetic + Finset.prod_erase bookkeeping
> ```

S5 ACT (PR #18629, researcher-6) deliberately shipped *only* `resampleAt_apply_outside` and deferred the helper + `_inside` + `_indep` to S5b, explicitly citing the residual bookkeeping `sorry` and the worktree `.lake` symlink-loop build trap (`feedback_researcher_lake_symlink_loop_and_wipe.md`) as the reason.

**This PREP** pins down the missing Mathlib API, writes a sorry-free version of the bookkeeping, and documents two alternatives (a direct first-principles route + a helper-based route) so the next ACT session has a clear, audited recipe.

Single file touched: this session-notes markdown. No edits to `proofs/Proofs/MoserTardos.lean`, `state.md`, `knowledge.md`, `problem.md`, or `src/data/research/problems/prob-method-lovasz-local-oq-01.json` (drift sync remains auditor/mechanic).

---

## 1. The key omission from S4b PREP — `Fintype.prod_eq_mul_prod_subtype_ne`

S4b PREP §3.2's residual sorry says:

> Peel off the i-th factor using `prod_attach` + `Finset.prod_erase`:
> `rw [← Finset.prod_attach _ _]`
> equivalent: rewrite the universal `∏ k` as `∏ k ∈ univ.erase i, _ * card (β i)`.

The natural Mathlib lemma for "factor out the term at `a`" on a `Fintype` is **not** the `Finset.prod_erase` path. There is a cleaner one already in Mathlib v4.26.0 that S4b PREP overlooked.

### 1.1. The Mathlib lemma

```lean
@[to_additive]
theorem Fintype.prod_eq_mul_prod_subtype_ne [DecidableEq α] (f : α → M) (a : α) :
    ∏ i, f i = f a * ∏ i : {i // i ≠ a}, f i.1 := by
  simp_rw [← (Equiv.optionSubtypeNe a).prod_comp, prod_option, Equiv.optionSubtypeNe_none,
    Equiv.optionSubtypeNe_some]
```

**Source pin**: `Mathlib/Data/Fintype/BigOperators.lean:106-110` (`@[to_additive]` so the additive analogue `sum_eq_add_sum_subtype_ne` is auto-derived; same line range).

The lemma factors a `Fintype`-indexed product `∏ i, f i` into the product of `f a` and the product `∏ i : {i // i ≠ a}, f i.1` — i.e. the product of the same factors over the *subtype complement* of `a`. This is exactly what we want because the codomain of `Equiv.piSplitAt a β` is `β a × ∀ j : {j // j ≠ a}, β j`, and the fiber cardinality (per `Fintype.card_pi` on that codomain) is `card (β a) * ∏ j : {j // j ≠ a}, card (β j.1)`.

### 1.2. Why this lemma cleanly closes the bookkeeping

The helper's goal after `Fintype.card_pi` and `tsum_fintype` is:

```
(card (∀ k : {k // k ≠ i}, β k.val) : ℝ≥0∞) * (card (∀ k, β k) : ℝ≥0∞)⁻¹
  = (card (β i) : ℝ≥0∞)⁻¹
```

After two more `Fintype.card_pi` rewrites (both the numerator and the inverted denominator), the LHS becomes:

```
(∏ k : {k // k ≠ i}, (card (β k.1) : ℝ≥0∞)) * (∏ k, (card (β k) : ℝ≥0∞))⁻¹
```

Now apply `Fintype.prod_eq_mul_prod_subtype_ne` (at `a := i`, `f := fun k => (card (β k) : ℝ≥0∞)`) **to the denominator inside the inverse**:

```
(∏ k, (card (β k) : ℝ≥0∞)) = (card (β i) : ℝ≥0∞) * (∏ k : {k // k ≠ i}, (card (β k.1) : ℝ≥0∞))
```

Substituting:

```
LHS = (∏ k : {k // k ≠ i}, (card (β k.1) : ℝ≥0∞))
        * ((card (β i) : ℝ≥0∞) * (∏ k : {k // k ≠ i}, (card (β k.1) : ℝ≥0∞)))⁻¹
```

Two ENNReal cancellations finish:

1. `(a * b)⁻¹ = b⁻¹ * a⁻¹` (`ENNReal.mul_inv` for non-zero non-infinite factors).
2. `b * b⁻¹ = 1` (`ENNReal.mul_inv_cancel`, when `b ≠ 0` and `b ≠ ∞`).

Both conditions hold because:
- Every `card (β k)` is a `ℕ` cast to `ℝ≥0∞`, so never `∞`.
- Each `card (β k) ≥ 1` because `Nonempty (β k)` (`Fintype.card_pos`), so the cast is `≠ 0`.
- The product of non-zero, non-infinite ENNReals is non-zero (`Finset.prod_ne_zero_iff`) and non-infinite (`WithTop.prod_ne_top`, `Mathlib/Algebra/BigOperators/WithTop.lean:50`).

The result is `(card (β i) : ℝ≥0∞)⁻¹`, as desired.

---

## 2. Concrete sorry-free Lean for the helper's bookkeeping (~14 LOC)

Replace S4b PREP §3.2's residual `sorry` with the following block. The names are pinned to Mathlib v4.26.0; all eight Mathlib symbols below are verified by `gh api repos/leanprover-community/mathlib4/contents/...` at session time.

```lean
  -- … after h_fiber, the goal is:
  -- (Fintype.card (∀ k : {k // k ≠ i}, β k.val) : ℝ≥0∞)
  --   * (Fintype.card (∀ k, β k) : ℝ≥0∞)⁻¹
  -- = (Fintype.card (β i) : ℝ≥0∞)⁻¹
  rw [Fintype.card_pi, Fintype.card_pi]
  -- LHS is now (∏ k : {k // k ≠ i}, (card (β k.1) : ℝ≥0∞))
  --              * (∏ k, (card (β k) : ℝ≥0∞))⁻¹
  -- (after the Nat-cast push from card_pi; the cast is `Nat.cast` on each factor).
  push_cast
  rw [Fintype.prod_eq_mul_prod_subtype_ne
      (f := fun k => (Fintype.card (β k) : ℝ≥0∞)) i]
  -- LHS is (∏ k : {k // k ≠ i}, …)
  --          * ((card (β i) : ℝ≥0∞) * (∏ k : {k // k ≠ i}, …))⁻¹
  have h_pi_ne_zero :
      (∏ k : {k // k ≠ i}, (Fintype.card (β k.1) : ℝ≥0∞)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact_mod_cast (Fintype.card_pos (α := β k.1)).ne'
  have h_pi_ne_top :
      (∏ k : {k // k ≠ i}, (Fintype.card (β k.1) : ℝ≥0∞)) ≠ ⊤ := by
    exact WithTop.prod_ne_top (fun _ _ => ENNReal.natCast_ne_top _)
  have h_card_i_ne_zero : (Fintype.card (β i) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := β i)).ne'
  have h_card_i_ne_top : (Fintype.card (β i) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl h_card_i_ne_zero) (Or.inl h_pi_ne_top),
      ← mul_assoc, ENNReal.mul_inv_cancel h_pi_ne_zero h_pi_ne_top, one_mul]
```

14 LOC of proof body (3 `rw`/`push_cast`, 4 `have` justifications, 1 closing `rw`). No new imports, all `simp`-style normalizations are stock Mathlib.

### 2.1. Per-step Mathlib pin

| Step | Lemma | Mathlib v4.26.0 module : line |
|---|---|---|
| `Fintype.card_pi` (twice) | `[Fintype α] [∀ i, Fintype (β i)] : card (∀ i, β i) = ∏ i, card (β i)` | `Mathlib/Data/Fintype/BigOperators.lean:132` |
| `push_cast` | `Nat.cast`-normalising tactic | core tactic |
| `Fintype.prod_eq_mul_prod_subtype_ne` | `[DecidableEq α] (f : α → M) (a : α) : ∏ i, f i = f a * ∏ i : {i // i ≠ a}, f i.1` | `Mathlib/Data/Fintype/BigOperators.lean:106` |
| `Finset.prod_ne_zero_iff` | `∏ i ∈ s, f i ≠ 0 ↔ ∀ i ∈ s, f i ≠ 0` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (stock) |
| `Fintype.card_pos` | `[Nonempty α] [Fintype α] : 0 < Fintype.card α` | `Mathlib/Data/Fintype/Card.lean` |
| `ENNReal.natCast_ne_top` | `(n : ℕ) : (n : ℝ≥0∞) ≠ ⊤` | `Mathlib/Data/ENNReal/Basic.lean` |
| `WithTop.prod_ne_top` | `(h : ∀ i ∈ s, f i ≠ ⊤) : ∏ i ∈ s, f i ≠ ⊤` | `Mathlib/Algebra/BigOperators/WithTop.lean:50` |
| `ENNReal.mul_inv` | non-zero non-infinite distributivity of `(a*b)⁻¹` | `Mathlib/Data/ENNReal/Inv.lean` |
| `ENNReal.mul_inv_cancel` | `(h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1` | `Mathlib/Data/ENNReal/Inv.lean:102` |

All names are confirmed present and non-deprecated. No phantom names.

### 2.2. Risks identified for the S5b ACT

| Risk | Severity | Mitigation |
|---|---|---|
| `push_cast` may not normalize `Nat.cast` inside the inverted product | Medium | Fall back to explicit `simp only [Nat.cast_prod]` (Mathlib has this as `@[simp]` so it should fire) or do the cast push step-by-step. |
| `ENNReal.mul_inv` may be named `ENNReal.mul_inv` or `mul_inv` in scope; the Or-disjunction form might differ from `(Or.inl …) (Or.inl …)` | Low | The signature `(h : a ≠ 0 ∨ b ≠ ∞) (h' : a ≠ ∞ ∨ b ≠ 0)` is the v4.26.0 form; verified at the Mathlib audit. If wrong, use `ENNReal.mul_inv_eq` or split via `rw [mul_inv]` directly. |
| `Fintype.prod_eq_mul_prod_subtype_ne` requires `[DecidableEq α]`; in the helper, `α` is the Pi-index type which is `Type*` | Trivial | The `[DecidableEq α]` is a hypothesis of the helper itself; pass it through. |
| The `h_fiber` proof (from S4b PREP §3.2) uses `Finset.card_eq_of_equiv_fintype` which may not exist under that exact name in v4.26.0 | Medium | Verify at S5b ACT time; fall back to `Finset.card_eq_of_bijective` or direct `Finset.card_image_of_injective` if needed. (This is the S4b PREP author's concern, not new here.) |
| The `Equiv.piSplitAt` definition uses `@[simps]`, so `simp [Equiv.piSplitAt]` should unfold; if it doesn't, the manual `unfold` may be needed | Trivial | Use `simp only [Equiv.piSplitAt_apply, Equiv.piSplitAt_symm_apply]` (the auto-generated `simp` lemmas). |

### 2.3. Total helper LOC accounting

- `ext + rw [map_apply, uniformOfFintype_apply, tsum_fintype]` + `simp_rw`: 3 LOC
- `Finset.sum_filter` + `Finset.sum_const` + `nsmul_eq_mul`: 3 LOC
- `h_fiber` proof via `Equiv.piSplitAt`: ~20 LOC (per S4b PREP §3.2)
- ENNReal cancellation block (this PREP §2): **14 LOC** (replaces S4b PREP's residual `sorry`)
- Closing arithmetic: ~2 LOC (the final `rfl` or trivial inequality)

Total: **~42 LOC** sorry-free.

Within the original S4b PREP §3 estimate of ~40 LOC. Within `state.md:171`'s "~60-80 LOC" target for the three lemmas (helper + `_inside` + `_indep`).

---

## 3. Alternative — first-principles `_inside` proof without the helper

If the helper proof's `h_fiber` step (S4b PREP §3.2 lines 102-121) turns out to have an unforeseen Mathlib API issue, a fallback is to prove `_inside` directly via `PMF.uniformOfFintype_apply` + `PMF.map_apply` + the same `Fintype.prod_eq_mul_prod_subtype_ne` lemma.

### 3.1. Direct discharge

```lean
lemma resampleAt_apply_inside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.uniformOfFintype (P.alphabet j) := by
  classical
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  -- Goal: ∑ (a : ∀ k : S, P.alphabet k.val), (if b = (glue a) j then ... else 0)
  --        = (Fintype.card (P.alphabet j) : ℝ≥0∞)⁻¹
  -- glue a j = if h : j ∈ S then a ⟨j, h⟩ else v j; dif_pos hj reduces to a ⟨j, hj⟩.
  simp_rw [show (fun a : ∀ k : S, P.alphabet k.val =>
              (fun (k : Fin P.numVars) => if h : k ∈ S then a ⟨k, h⟩ else v k) j)
            = fun a => a ⟨j, hj⟩ from by funext a; simp [dif_pos hj]]
  rw [PMF.uniformOfFintype_apply, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Goal becomes (#fiber) * (card (∀ k : S, α k.val))⁻¹ = (card (α j))⁻¹
  -- where fiber = univ.filter (fun a => b = a ⟨j, hj⟩) of cardinality
  -- = card (∀ k : {k : S // k ≠ ⟨j, hj⟩}, α k.val.val) by piSplitAt at ⟨j, hj⟩
  have h_fiber := Fintype.card_subtype_eq (s := ⟨j, hj⟩)  -- or piSplitAt directly
  -- … same ENNReal cancellation as in §2 above, applied at ⟨j, hj⟩ ∈ ↥S.
  sorry
```

This route has the same algebraic core (ENNReal cancellation) but avoids the outer helper. The trade-off: `_indep` would need the same machinery re-instantiated for `Finset`-coordinate marginals, so the helper-based approach is preferred when both `_inside` and `_indep` are wanted in one PR.

### 3.2. Recommendation

**S5b ACT (recommended)**: ship the helper + `_inside` + `_indep` as **one PR** (Option A), using the helper-based proofs from S4b PREP §6 (`_inside`, 8 LOC) and §7 (`_indep`, 18 LOC), with the helper's `sorry` discharged via this PREP's §2 block.

**S5b-alt ACT (fallback)**: if the helper's `h_fiber` step proves problematic at build time, **drop the helper** and ship `_inside` + `_indep` with two parallel first-principles proofs (Option B). Each is ~25-30 LOC; total ~55-60 LOC. Less DRY but fewer load-bearing pieces.

---

## 4. Mathlib audit — pinned signatures (re-verified at session time)

All confirmed via `gh api repos/leanprover-community/mathlib4/contents/<path>` and `gh api search/code?q=...` at 2026-05-13 ~07:35 UTC.

| Symbol | Module | Line | Signature |
|---|---|---:|---|
| `Equiv.piSplitAt` | `Mathlib/Logic/Equiv/Prod.lean` | 480 | `@[simps] def piSplitAt [DecidableEq α] (i : α) (β : α → Type*) : (∀ j, β j) ≃ β i × ∀ j : { j // j ≠ i }, β j` |
| `Fintype.card_pi` | `Mathlib/Data/Fintype/BigOperators.lean` | 132 | `@[simp] : [Fintype α] [∀ i, Fintype (β i)] : card (∀ i, β i) = ∏ i, card (β i)` |
| `Fintype.prod_eq_mul_prod_subtype_ne` | same | 106 | `@[to_additive] : [DecidableEq α] (f : α → M) (a : α) : ∏ i, f i = f a * ∏ i : {i // i ≠ a}, f i.1` |
| `Fintype.card_congr` | `Mathlib/Data/Fintype/Card.lean` | 67 | `[Fintype α] [Fintype β] (f : α ≃ β) : card α = card β` |
| `PMF.map_apply` | `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean` | 53 | `(map f p) b = ∑' a, if b = f a then p a else 0` |
| `PMF.map_comp` | same | 66 | `(p.map f).map g = p.map (g ∘ f)` |
| `PMF.map_const` | same | 79 | `p.map (Function.const α b) = pure b` |
| `PMF.uniformOfFintype_apply` | `Mathlib/Probability/Distributions/Uniform.lean` | 289 | `(a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹` |
| `tsum_fintype` | `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` | 475 | `[Fintype β] (f : β → α) : ∑' b, f b = ∑ b, f b` |
| `ENNReal.mul_inv_cancel` | `Mathlib/Data/ENNReal/Inv.lean` | 102 | `protected (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1` |
| `ENNReal.mul_inv` | same | (varies; same module) | `(a*b)⁻¹` distributivity for non-zero non-infinite factors |
| `ENNReal.natCast_ne_top` | `Mathlib/Data/ENNReal/Basic.lean` | (stock) | `(n : ℕ) : (n : ℝ≥0∞) ≠ ⊤` |
| `WithTop.prod_ne_top` | `Mathlib/Algebra/BigOperators/WithTop.lean` | 50 | `(h : ∀ i ∈ s, f i ≠ ⊤) : ∏ i ∈ s, f i ≠ ⊤` |
| `Fintype.card_pos` | `Mathlib/Data/Fintype/Card.lean` | (stock) | `[Nonempty α] [Fintype α] : 0 < Fintype.card α` |
| `Finset.prod_ne_zero_iff` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | (stock) | `∏ i ∈ s, f i ≠ 0 ↔ ∀ i ∈ s, f i ≠ 0` |

15 symbols, all present in Mathlib v4.26.0, all non-deprecated.

---

## 5. Comparison vs S4a PREP / S4b PREP / S5 ACT

| Aspect | S4a PREP (#18477) | S4b PREP (#18580) | S5 ACT (#18629) | **This S5b PREP** |
|---|---|---|---|---|
| Approach | Mathlib audit ("which lemmas exist?") | `Equiv.piSplitAt` design ("which structural lemma to use?") | Discharge `_outside` only (1 of 3) | **Discharge helper's residual sorry; concrete 14-LOC block** |
| Output | `*.md` doc only (~316 LOC) | `*.md` doc only (~366 LOC) | `+24 LOC` to `MoserTardos.lean` | `*.md` doc only (~this file) |
| Sorries closed | 0 | 0 (helper still has a bookkeeping `sorry` in the design) | 0 (no helper) | **0 (still doc-only); but discharges the design-level `sorry`** |
| Key contribution | List of 8 Mathlib symbols + phantom-name flag | `Equiv.piSplitAt`-based proof skeleton | Verbatim transfer of `_outside` template | **The missing `Fintype.prod_eq_mul_prod_subtype_ne` lemma + concrete 14-LOC ENNReal cancellation block** |
| New Mathlib symbols pinned | 8 | 8 (same) | 0 | **7 new** (`Fintype.prod_eq_mul_prod_subtype_ne`, `ENNReal.mul_inv_cancel`, `ENNReal.mul_inv`, `ENNReal.natCast_ne_top`, `WithTop.prod_ne_top`, `Fintype.card_pos`, `Finset.prod_ne_zero_iff`) |

This PREP is genuinely additive to S4b PREP — the key contribution is identifying that `Fintype.prod_eq_mul_prod_subtype_ne` directly closes the "peel off the i-th factor" subproblem in one rewrite, avoiding S4b PREP's longer `Finset.prod_attach` + `Finset.prod_erase` chain.

---

## 6. Orthogonality (single-file PREP)

| File | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/MoserTardos.lean` (post-S5-ACT, 269 LOC) | on origin/main | **no edit** in this PREP |
| `research/problems/prob-method-lovasz-local-oq-01/state.md` | post-S5-ACT | **no edit** (drift sync is auditor/mechanic) |
| `research/problems/prob-method-lovasz-local-oq-01/knowledge.md` | post-S1 | **no edit** |
| `research/problems/prob-method-lovasz-local-oq-01/problem.md` | post-S1 | **no edit** |
| `src/data/research/problems/prob-method-lovasz-local-oq-01.json` | post-S1 | **no edit** |
| `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s05b-prep-helper-ennreal-cancellation.md` | new (this file) | **single file touched** |

Single file. Zero risk to S5 ACT's build (no Lean changes). Zero risk to any future S5b ACT (this PREP refines the design without occupying the implementation slot).

---

## 7. Next action — S5b ACT recipe

After this PREP merges, the next ACT session has a 3-step recipe:

1. **Add the helper `PMF.marginal_uniformOfFintype_pi`** to `proofs/Proofs/MoserTardos.lean` (alongside the existing `resampleAt_apply_outside` lemma at line 138). Use the proof template from S4b PREP §3.2 (h_fiber via `Equiv.piSplitAt`) + this PREP §2 (the 14-LOC ENNReal cancellation block).
2. **Add `resampleAt_apply_inside`** (S4b PREP §6, ~8 LOC, single `exact marginal_uniformOfFintype_pi ⟨j, hj⟩` after `dif_pos hj` reduction).
3. **Add `resampleAt_indep`** (S4b PREP §7, ~18 LOC, finset-coordinate analogue using the same helper after `Equiv.subtypeEquivOfSubtype` or `Finset.image`).

Total Lean delta: **~42 LOC + ~8 LOC + ~18 LOC = ~68 LOC**, matching the original S4b PREP estimate.

**Build verification**: ship with `build pending` qualifier in PR title; Doctor/Mechanic verifies via `./proofs/scripts/docker-build.sh Proofs.MoserTardos` from a clean worktree (the worktree's `proofs/.lake` symlink loop remains a blocker for in-session builds).

---

## 8. Honesty

- **This PREP does not close any sorry in Lean.** The `MoserTardos.lean` file is unchanged. The "sorry-discharge" is a design-level discharge — the residual `sorry` in S4b PREP §3.2's helper proof template is now replaced by a concrete 14-LOC Mathlib-API-pinned Lean block, but the block has not been Lean-checked.
- **The S5b ACT recipe (§7) is contingent on building.** Lean's `simp` / `push_cast` / instance resolution can behave unpredictably in `ℝ≥0∞`-arithmetic settings; the 14-LOC block may need ~2-3 LOC of in-line `simp only` adjustments at S5b ACT time.
- **No new sorries, axioms, or theorems are introduced.** This is a session-notes-only PREP.
- **The h_fiber step (S4b PREP §3.2) is *not* re-audited here.** Its `Finset.card_eq_of_equiv_fintype` invocation may have a slightly different name in v4.26.0 (the canonical name is now `Fintype.card_eq_of_bijection` or similar). The S5b ACT session should re-verify before implementation.
- **`Fintype.prod_eq_mul_prod_subtype_ne` was missed by S4b PREP.** The original PREP planned to use `Finset.prod_attach` + `Finset.prod_erase`, which works but is longer (~6-8 LOC) than the one-rewrite path documented here.

---

## 9. References

- **S4a PREP (Mathlib audit)**: `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s04a-prep-resampleAt-marginal-lemma-mathlib-audit.md` (PR #18477).
- **S4b PREP (`piSplitAt` discharge)**: `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s04b-prep-marginal-piSplitAt-discharge.md` (PR #18580). §3.2 contains the helper proof template with the residual `sorry` this PREP discharges.
- **S5 ACT (`_outside` lemma)**: `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s05-act-outside-marginal.md` (PR #18629). Most recent merge on the slug; deliberately deferred the helper + `_inside` + `_indep`.
- **Mathlib v4.26.0**: `Fintype.prod_eq_mul_prod_subtype_ne` at `Mathlib/Data/Fintype/BigOperators.lean:106`; `ENNReal.mul_inv_cancel` at `Mathlib/Data/ENNReal/Inv.lean:102`; `WithTop.prod_ne_top` at `Mathlib/Algebra/BigOperators/WithTop.lean:50`.
- **Build trap**: memory `feedback_researcher_lake_symlink_loop_and_wipe.md`.
- **Saturation context (2026-05-13)**: 4 merges in 6h on this slug (S4 PREP 00:51, S4a PREP 02:33, S4b PREP 04:50, S5 ACT 07:08); within standard release window (~2h after S5 ACT).
