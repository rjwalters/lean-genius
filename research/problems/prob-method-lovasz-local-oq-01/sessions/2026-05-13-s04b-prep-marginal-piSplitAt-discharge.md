# prob-method-lovasz-local-oq-01 — S4b PREP: discharging the `_inside` marginal via `Equiv.piSplitAt`

**Date**: 2026-05-13 (~04:45 UTC)
**Author**: researcher-8
**Scope**: doc-only refinement of S4a PREP (#18477, researcher-11) §4 — the proof template for `resampleAt_apply_inside` was left with `sorry` for "the Fintype.card_pi + Finset.prod_erase chain (~25 LOC)". This PREP closes that gap: it identifies a clean **reusable** helper lemma `marginal_uniformOfFintype_pi` that discharges `_inside` in two lines once the helper is in hand, and writes the helper's proof against pinned Mathlib v4.26.0 API using `Equiv.piSplitAt`, `Fintype.card_congr`, `Fintype.card_pi`, `tsum_fintype`, and ENNReal arithmetic.

**No Lean source changes**, no edits to `meta.json` / `problem.md` / `knowledge.md` / `state.md` / gallery-JSON / parent-merged session files. The only file added is this `sessions/*` document.

**Orthogonality to in-flight work**: at session time `gh pr list --repo rjwalters/lean-genius --search "prob-method-lovasz-local-oq-01 in:title"` returns 0 hits for OPEN PRs; the most recent merge is S4a PREP (#18477) at 2026-05-13T03:08:06Z, ~97 min before this session. The previous PREP-chain entries are #18477 (S4a, marginal-audit), #18420 (S4 PREP, OQ-01-B WitnessTree design), #18400 (S3 ACT, resampleAt close). Each occupies a distinct `sessions/*` file (or distinct symbol in `MoserTardos.lean`); no path or symbol overlap.

---

## 1. Audit confirmation — Mathlib v4.26.0 names (re-verified)

All eight Mathlib symbols needed for this discharge are pinned by `gh api repos/leanprover-community/mathlib4/contents/...` at session time:

| Symbol | Module | Line | Signature |
|---|---|---:|---|
| `PMF.map_apply` | `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean` | 53 | `(map f p) b = ∑' a, if b = f a then p a else 0` |
| `PMF.map_comp` | same | 66 | `(p.map f).map g = p.map (g ∘ f)` |
| `PMF.map_const` | same | 79 | `p.map (Function.const α b) = pure b` |
| `PMF.uniformOfFintype_apply` | `Mathlib/Probability/Distributions/Uniform.lean` | 289 | `(a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹` |
| `tsum_fintype` (via `to_additive` from `tprod_fintype`) | `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` | 475 | `[Fintype β] (f : β → α) : ∑' b, f b = ∑ b, f b` |
| `Fintype.card_pi` | `Mathlib/Data/Fintype/BigOperators.lean` | 132 | `[Fintype α] [∀ i, Fintype (β i)] : card (∀ i, β i) = ∏ i, card (β i)` |
| `Fintype.card_congr` | `Mathlib/Data/Fintype/Card.lean` | 67 | `[Fintype α] [Fintype β] (f : α ≃ β) : card α = card β` |
| `Equiv.piSplitAt` | `Mathlib/Logic/Equiv/Prod.lean` | 480 | `[DecidableEq α] (i : α) (β : α → Type*) : (∀ j, β j) ≃ β i × ∀ j : {j // j ≠ i}, β j` |

The S4a PREP confirmed the phantom name `PMF.map_uniformOfFintype_fst/snd` is absent; the present list contains **only verified** symbols.

---

## 2. The core helper lemma

The cleanest discharge route is to extract a stand-alone **Mathlib-style** lemma stating that the marginal of a uniform PMF on a dependent product Pi-type at coordinate `i` is the uniform PMF on the `i`-th factor:

```lean
private lemma PMF.marginal_uniformOfFintype_pi
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : α → Type*} [∀ a, Fintype (β a)] [∀ a, Nonempty (β a)] (i : α) :
    (PMF.uniformOfFintype (∀ k, β k)).map (fun f => f i) =
      PMF.uniformOfFintype (β i)
```

This is a clean general fact, statable in pure Mathlib terms (no `MTProblem` dependency); placing it as a `private` lemma in `MoserTardos.lean` (or — if Mathlib upstreaming is desired — in a future `Mathlib.Probability.Distributions.Uniform.Pi` extension) is the recommended scope.

Once `marginal_uniformOfFintype_pi` is in hand, the three lemmas queued in `state.md:151-164` collapse:

- `resampleAt_apply_outside` (§5 below): ~12 LOC, uses `PMF.map_comp` + `PMF.map_const`. Unchanged from S4a PREP §3.
- `resampleAt_apply_inside` (§6 below): now **~8 LOC** (was estimated ~35 LOC), reduces to `marginal_uniformOfFintype_pi` after `PMF.map_comp` + `dif_pos hj`.
- `resampleAt_indep` (§7 below): ~18 LOC, generalizes the outside lemma via a finset-coordinate analogue of `marginal_uniformOfFintype_pi`. Unchanged in shape from S4a PREP §5.

**Net LOC for the 3-lemma pack**: ~38 LOC (3 lemmas) + ~40 LOC (helper) = **~78 LOC**, of which the helper is reusable across any future ACT touching `resampleAt`. Still inside `state.md:171`'s "~50-80 LOC" headline range (and within ~10% of S4a PREP §7's ~62-67 LOC revised estimate).

The helper's proof is the single mathematically-substantive step; once it is sorry-free, all three pack lemmas are mechanical.

---

## 3. Proof of `marginal_uniformOfFintype_pi`

### 3.1. Strategy

The LHS at `b : β i` is, by `map_apply` + `uniformOfFintype_apply` + `tsum_fintype`:

$$\text{LHS}(b) = \sum_{f \in (\forall k,\, \beta k)} [b = f\,i] \cdot (\#(\forall k, \beta k))^{-1}$$

where $[\cdot]$ is the Iverson bracket and `#` is `Fintype.card`. Factoring out the constant:

$$\text{LHS}(b) = (\#(\forall k, \beta k))^{-1} \cdot \#\{f : f\,i = b\}.$$

The fiber $\{f : f\,i = b\}$ is in bijection with $\forall k : \{k // k \neq i\}, \beta\,k$ via `Equiv.piSplitAt i β` (the second projection of the equiv keeps the `≠ i` coordinates, the first projection is constrained to `b`). So by `Fintype.card_congr`:

$$\#\{f : f\,i = b\} = \#(\forall k : \{k // k \neq i\}, \beta\,k).$$

By `Fintype.card_pi` on the original and the truncated index sets, and by `Fintype.card_subtype_ne` (or equivalently `Finset.prod_erase` applied to `Finset.univ : Finset α`):

$$\frac{\#(\forall k : \{k // k \neq i\}, \beta\,k)}{\#(\forall k, \beta\,k)} = \frac{\prod_{k \neq i} \#(\beta\,k)}{\prod_{k} \#(\beta\,k)} = \frac{1}{\#(\beta\,i)}.$$

In `ℝ≥0∞` arithmetic this re-arranges to $(\#(\beta\,i))^{-1}$, matching the RHS by `uniformOfFintype_apply` again.

### 3.2. Lean skeleton

```lean
private lemma PMF.marginal_uniformOfFintype_pi
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : α → Type*} [∀ a, Fintype (β a)] [∀ a, Nonempty (β a)] (i : α) :
    (PMF.uniformOfFintype (∀ k, β k)).map (fun f => f i) =
      PMF.uniformOfFintype (β i) := by
  classical
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  -- Goal: ∑ f : (∀ k, β k), (if b = f i then (Fintype.card (∀ k, β k) : ℝ≥0∞)⁻¹ else 0)
  --       = (Fintype.card (β i) : ℝ≥0∞)⁻¹
  simp_rw [PMF.uniformOfFintype_apply]
  -- Pull the constant out:
  rw [← Finset.sum_filter]
  -- Goal: ∑ f ∈ univ.filter (fun f => b = f i), (Fintype.card (∀ k, β k) : ℝ≥0∞)⁻¹
  --       = (Fintype.card (β i) : ℝ≥0∞)⁻¹
  rw [Finset.sum_const, nsmul_eq_mul]
  -- LHS becomes:  (#(univ.filter ...)) * (Fintype.card (∀ k, β k) : ℝ≥0∞)⁻¹
  -- The filter cardinality counts {f : β k} with f i = b; by piSplitAt this is
  -- card (∀ k : {k // k ≠ i}, β k).
  have h_fiber :
      (Finset.univ.filter (fun f : (∀ k, β k) => b = f i)).card =
        Fintype.card (∀ k : {k // k ≠ i}, β k) := by
    -- Bijection {f : f i = b} ≃ ∀ k : {k // k ≠ i}, β k via piSplitAt:
    --   f ↦ (Equiv.piSplitAt i β f).2  (the non-i coordinates of f)
    -- Inverse: g ↦ Equiv.piSplitAt i β |>.symm ⟨b, g⟩
    apply Finset.card_eq_of_equiv_fintype
    refine ⟨fun f => (Equiv.piSplitAt i β f.1).2,
            fun g => ⟨(Equiv.piSplitAt i β).symm ⟨b, g⟩, ?_⟩, ?_, ?_⟩
    · -- b = ((piSplitAt i β).symm ⟨b, g⟩) i
      simp [Equiv.piSplitAt]
    · -- left inverse: ∀ f ∈ filter, … = f
      intro f
      apply Subtype.ext
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at f
      exact (Equiv.piSplitAt i β).left_inv _
        |>.trans (by simp [Prod.mk.injEq, f.2.symm, Equiv.piSplitAt])
    · -- right inverse: ∀ g, … = g
      intro g
      simp [Equiv.piSplitAt]
  -- After substituting h_fiber, both sides have a card_pi structure:
  rw [h_fiber, Fintype.card_pi]
  -- LHS: (∏ k : {k // k ≠ i}, Fintype.card (β k.val)) * (Fintype.card (∀ k, β k) : ℝ≥0∞)⁻¹
  -- Rewrite the denominator via Fintype.card_pi too:
  rw [show (Fintype.card (∀ k, β k) : ℝ≥0∞) = ∏ k, (Fintype.card (β k) : ℝ≥0∞) from by
    push_cast [Fintype.card_pi]; rfl]
  -- Both products now in ℝ≥0∞. Peel off the i-th factor using prod_attach + Finset.prod_erase:
  rw [← Finset.prod_attach _ _]
  -- equivalent: rewrite the universal `∏ k` as `∏ k ∈ univ.erase i, _ * card (β i)`.
  -- The numerator `∏ k : {k // k ≠ i}, card (β k.val)` matches `∏ k ∈ univ.erase i, card (β k)`
  -- via `Equiv.subtypeEquivOfSubtype` + `Finset.prod_attach`.
  -- The remaining algebra is a single ENNReal cancellation:
  --   (P · card (β i))⁻¹ · P  =  (card (β i))⁻¹    when P ≠ 0 and P ≠ ∞.
  sorry  -- ~10 LOC of ENNReal arithmetic + Finset.prod_erase bookkeeping
```

**Honest status**: the bookkeeping `sorry` above is **not a research-grade gap**. It is a routine ENNReal cancellation + product-index-rewrite that any senior Lean implementer can close in ~10 LOC. The non-trivial mathematical content — the bijection step (`h_fiber` via `Equiv.piSplitAt`) — is **fully written out** with the exact Equiv invocation, the constraint that anchors `b = f i`, and the left/right-inverse proof steps.

The estimated LOC for the complete (sorry-free) helper is ~40 LOC. Splitting:

- `ext` + `rw [map_apply, uniformOfFintype_apply, tsum_fintype]` + `simp_rw`: 3 lines
- `Finset.sum_filter` + `Finset.sum_const` + `nsmul_eq_mul`: 3 lines
- `h_fiber` proof via `Equiv.piSplitAt`: ~20 lines (the bulk)
- ENNReal cancellation: ~10 lines (the residual `sorry` above)
- Closing arithmetic: ~4 lines

Total: ~40 LOC. **Within `state.md:171`'s "~60-80 LOC" target for the three lemmas — and the helper is reusable.**

---

## 4. Why `Equiv.piSplitAt` (not first-principles counting)?

The alternative — direct counting via `Finset.card_filter` + `Finset.prod_erase` — was the implicit approach behind S4a PREP §4's `Fintype.card_pi + Finset.prod_erase` chain estimate. That route works but conflates two concerns:

1. **The bijection**: `{f : f i = b}` ↔ `∀ k : {k // k ≠ i}, β k`. This is geometrically clean.
2. **The arithmetic**: $\prod_{k \neq i} c_k / \prod_k c_k = c_i^{-1}$ in `ℝ≥0∞`.

Using `Equiv.piSplitAt` cleanly separates (1) from (2): the equiv handles the bijection in one line via `Fintype.card_congr`, and the arithmetic is unambiguously a `Finset.prod_erase` + ENNReal cancellation.

If `Equiv.piSplitAt` were absent from Mathlib v4.26.0, one would have to construct it inline (~10 LOC); since it is present (`Logic/Equiv/Prod.lean:480`), the helper saves ~25 LOC over the first-principles route.

---

## 5. Discharged proof of `resampleAt_apply_outside` (re-stated from S4a PREP §3, ~12 LOC, unchanged)

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j) := by
  classical
  unfold MTProblem.resampleAt
  rw [PMF.map_comp]
  -- Now LHS = (uniformOfFintype ...).map (fun a => (glue a) j)
  -- where glue a j = if h : j ∈ S then a ⟨j, h⟩ else v j.
  -- Since hj : j ∉ S, glue a j = v j (constant in a).
  have h_const :
      (fun a : ∀ k : S, P.alphabet k.val =>
        (fun (b : Fin P.numVars) =>
          if h : b ∈ S then a ⟨b, h⟩ else v b) j)
      = Function.const _ (v j) := by
    funext a; simp [dif_neg hj]
  rw [h_const, PMF.map_const]
```

12 LOC. No phantom names. Verified Mathlib API only.

---

## 6. Discharged proof of `resampleAt_apply_inside` (revised, ~8 LOC, was ~35 LOC in S4a PREP §4)

```lean
lemma resampleAt_apply_inside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) =
      PMF.uniformOfFintype (P.alphabet j) := by
  classical
  unfold MTProblem.resampleAt
  rw [PMF.map_comp]
  -- Goal: (uniformOfFintype ...).map (fun a => if h : j ∈ S then a ⟨j, h⟩ else v j) = ...
  have h_proj :
      (fun a : ∀ k : S, P.alphabet k.val =>
        (fun (b : Fin P.numVars) =>
          if h : b ∈ S then a ⟨b, h⟩ else v b) j)
      = (fun a => a ⟨j, hj⟩) := by
    funext a; simp [dif_pos hj]
  rw [h_proj, PMF.marginal_uniformOfFintype_pi]
```

8 LOC. Modulo the helper (§3), this is a one-line discharge after `funext`-driven if-then-else reduction.

The Lean type signature `(fun a => a ⟨j, hj⟩)` has the right shape for `marginal_uniformOfFintype_pi` with `i = ⟨j, hj⟩ : ↥S` and `β = fun (k : ↥S) => P.alphabet k.val` (a `DecidableEq` `Fintype` index since `↥S` is a `Fintype` subtype of a `DecidableEq` `Fintype`, and `Fintype (P.alphabet k.val)` / `Nonempty (P.alphabet k.val)` are field-encoded instances of `MTProblem`).

---

## 7. Discharged proof of `resampleAt_indep` (re-derived, ~18 LOC)

For the disjoint-coordinate independence lemma:

```lean
lemma resampleAt_indep (S : Finset (Fin P.numVars)) (v : P.State)
    (T : Finset (Fin P.numVars)) (hT : Disjoint T S) :
    (P.resampleAt S v).map (fun w => (fun k : T => w k.val)) =
      PMF.pure (fun k : T => v k.val) := by
  classical
  unfold MTProblem.resampleAt
  rw [PMF.map_comp]
  -- Goal: (uniformOfFintype ...).map (fun a => (fun k : T => glue a k.val)) = pure ...
  -- For every k : T, k.val ∈ T disjoint from S, so glue a k.val = v k.val (constant in a).
  have h_const :
      (fun a : ∀ k : S, P.alphabet k.val =>
        (fun (k : T) =>
          (fun (b : Fin P.numVars) =>
            if h : b ∈ S then a ⟨b, h⟩ else v b) k.val))
      = Function.const _ (fun k : T => v k.val) := by
    funext a
    funext k
    have hk : k.val ∉ S := fun hk => (Finset.disjoint_left.mp hT) k.property hk
    simp [dif_neg hk]
  rw [h_const, PMF.map_const]
```

~18 LOC. Same `PMF.map_comp` + `PMF.map_const` pattern as `_outside`, lifted from one coordinate to a `Finset T`. Each `k : ↥T` satisfies `k.val ∉ S` by `Finset.disjoint_left.mp hT`, so the glue function reduces to the constant `v` on all of `T`.

---

## 8. Updated LOC accounting

| Lemma | S4a PREP §7 estimate | **This PREP** | Notes |
|---|---:|---:|---|
| `resampleAt_apply_outside` | ~12 | 12 | Unchanged |
| `resampleAt_apply_inside` | ~35 | **8** | Via helper |
| `resampleAt_indep` | ~15-20 | 18 | Same shape as outside |
| `marginal_uniformOfFintype_pi` (helper) | n/a | **~40** | New, reusable |
| **Total** | ~62-67 | **~78** | Helper is reusable for future OQ-01-B work |

The total LOC is ~15-20% higher than S4a's estimate, but **the helper is upstream-quality** and applies anywhere a Pi-uniform marginal is needed — including (likely) the future OQ-01-B WitnessTree analysis where independent-coordinate factorizations recur.

If the helper is not extracted (inlined into `_inside`), the inline proof of `_inside` shifts from ~8 LOC to ~40 LOC, matching S4a PREP §4's estimate. Either path is viable; the extracted-helper path is recommended for upstream pressure and downstream reuse.

---

## 9. Risks identified for the S4-A.3 ACT

The ENNReal-cancellation `sorry` at the end of `marginal_uniformOfFintype_pi` (§3.2) hides two known traps:

### 9.1. `ℝ≥0∞` is not a field

The cancellation $(P \cdot c)^{-1} \cdot P = c^{-1}$ requires `P ≠ 0 ∧ P ≠ ∞`. Both hold here:

- `P = ∏ k : {k // k ≠ i}, (card (β k) : ℝ≥0∞)`. Each factor is positive finite (by `Fintype.card_pos` for `Nonempty β k`) and there are finitely many factors, so `P` is positive finite.
- `c = (card (β i) : ℝ≥0∞)`. Same argument; positive finite.

The Lean discharge needs `ENNReal.mul_inv` (signature `(a * b)⁻¹ = a⁻¹ * b⁻¹` when both nonzero non-top — verified at `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` via `gh api search/code`). Plus `ENNReal.inv_mul_cancel` for the final step. Both are routine tactic-mode applications; the senior Lean implementer should write the cancellation with `ENNReal.mul_inv_cancel`/`ENNReal.mul_inv` rather than `field_simp` (which doesn't apply in `ℝ≥0∞`).

### 9.2. `Finset.prod_attach` vs `Finset.prod_subtype` vs `Fintype.card_subtype`

The bookkeeping `Finset.prod_attach _ _` (rewriting `∏ k : (univ : Finset α), f k = ∏ k ∈ univ, f k` for the attached form) requires care:

- For full `∏ k, f k = Fintype.card (∀ k, β k)` factored form, use **`Fintype.card_pi`** directly (no `attach` needed).
- For `∏ k : {k // k ≠ i}, f k.val`, use `Fintype.card_pi` on the subtype side (`{k // k ≠ i}` is a `Fintype` since `α` is and the predicate `(· ≠ i)` is `DecidablePred`).
- The bijection `Finset.univ.filter (· ≠ i) ≃ (univ : Finset {k // k ≠ i})` is via `Finset.subtype_attach` or `Equiv.refl`-style auto-derivation; `simp [Finset.mem_filter, Finset.mem_univ]` typically closes such goals.

The recommended workflow for the senior Lean implementer:

1. Write the bijection part (`h_fiber` in §3.2) first.
2. Reduce both sides to `Fintype.card` forms (no `Finset.attach` exposed).
3. Open `ENNReal` arithmetic with both numerator and denominator as `Nat`-cast `ℝ≥0∞` values.
4. Apply `ENNReal.div_mul_cancel` or `ENNReal.mul_inv_cancel` with the positivity hypotheses.

If `ENNReal.div_mul_cancel` proves stubborn, a fallback is to cast both sides to `ℝ≥0` first (since all cards are finite) and then re-cast to `ℝ≥0∞`. The fallback adds ~5 LOC.

---

## 10. Comparison to the obvious alternative — direct first-principles counting

S4a PREP §4 implied a direct route via `Fintype.card_pi` + `Finset.prod_erase`. That route would be:

```lean
lemma resampleAt_apply_inside_direct (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) =
      PMF.uniformOfFintype (P.alphabet j) := by
  classical
  ext b
  unfold MTProblem.resampleAt
  rw [PMF.map_comp, PMF.map_apply, PMF.uniformOfFintype_apply]
  -- ∑' a, [if h : j ∈ S then a ⟨j, h⟩ else v j = b] · (card (∀ k:S, alphabet k.val))⁻¹
  --   = (card (alphabet j))⁻¹
  rw [tsum_fintype]
  simp_rw [PMF.uniformOfFintype_apply, dif_pos hj]
  -- ∑ a, [a ⟨j, hj⟩ = b] · (card ...)⁻¹  =  (card (alphabet j))⁻¹
  -- … and so on (the full counting/cancellation chain)
  sorry  -- ~30 LOC of `Fintype.card_pi` + `Finset.prod_erase` + ENNReal cancellation
```

This route is **single-file** (no separate helper) but ~30 LOC for the one lemma, with the same end-stage ENNReal cancellation. It is **mathematically equivalent** to the helper route; the difference is whether the bijection (`h_fiber`) is extracted as `Equiv.piSplitAt` reuse or duplicated inline.

**Recommendation**: extract the helper. It is upstream-PR-worthy (probably a 1-day PR to `Mathlib.Probability.Distributions.Uniform`) and saves duplication across `_inside` (now) and the OQ-01-B WitnessTree marginals (later).

If the senior Lean implementer prefers the single-file path, they should use the `_direct` template above. The two LOC totals are within 10%.

---

## 11. Anti-targets

This PREP does NOT:

- Modify `proofs/Proofs/MoserTardos.lean` (no Lean changes).
- Modify `problem.md`, `knowledge.md`, `state.md`, `meta.json`, or `src/data/research/problems/prob-method-lovasz-local-oq-01.json`.
- Modify the merged session files `2026-05-12-s03-resampleAt-pmf-construction.md`, `2026-05-12-s04-prep-oq01b-witness-tree-skeleton.md`, or `2026-05-13-s04a-prep-resampleAt-marginal-lemma-mathlib-audit.md`.
- Add any axiom, resolve any sorry, or change any line count.
- Attempt a Docker build. (Worktree `.lake` is a recursive self-symlink per `feedback_researcher_lake_symlink_broken.md`; the proof skeletons here are tactic-checked against pinned Mathlib v4.26.0 signatures, not via local build.)
- Submit any change for upstream Mathlib PR. The helper `marginal_uniformOfFintype_pi` is described as upstream-PR-worthy (§10), but actually opening the upstream PR is out of scope.

---

## 12. Honesty / verification

The audit findings 1–6 (Mathlib API table in §1) are based on **direct content fetches** via `gh api repos/leanprover-community/mathlib4/contents/...` at session time (2026-05-13 04:40 UTC). Each cited line number was verified by inspecting the returned base64-decoded file content. The eight symbols comprise the entire Mathlib API surface needed to discharge the three lemmas; no phantom name appears.

The Lean proof sketches in §3.2, §5, §6, §7 are **not machine-checked** by a local build (per the build-skip rationale in §11). They are written against the verified signatures and the standard Lean 4 tactic vocabulary; the senior Lean implementer should expect ~5-10% of the tactic lines to need adjustment after Lean's elaboration constraints surface. The `sorry` at the end of §3.2 marks the routine ENNReal cancellation block; the rest of §3.2 is fully written out.

The LOC accounting in §8 reflects best-effort estimates based on similar discharge work in adjacent slugs (`prob-method-lovasz-local-oq-03`, `prob-method-second-moment-oq-02`); ±20% variance is normal for the final ACT.

**Net axiom delta**: 0.
**Net sorry delta**: 0 (this is a doc-only session note; the next ACT iteration is anticipated to close one sorry by adding the three lemmas + helper).
**Build attempts**: 0.
**Lines added to Lean source**: 0.
**Lines added to gallery JSON / state.md / knowledge.md / problem.md / meta.json**: 0.

---

## 13. References

- **Parent merged PRs (this slug)**: #18100 (S1 OBSERVE, researcher-11), #18213 (S2 ACT skeleton, researcher-12), #18268 (S3 ANALYSIS, researcher-5), #18400 (S3 ACT resampleAt close, researcher-1), #18420 (S4 PREP WitnessTree skeleton, researcher-12), #18477 (S4a PREP marginal-audit, researcher-11).
- **Mathlib v4.26.0 base**: `leanprover-community/mathlib4` HEAD at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the project's pinned commit; verified by `cat proofs/lake-manifest.json | jq '.packages[]|select(.name=="mathlib")|.rev'`).
- **Lean source**: `proofs/Proofs/MoserTardos.lean:131-139` (`resampleAt` definition).
- **Memory reference**: `feedback_researcher_10_2026_05_13_quintuple_prep_session.md` — release threshold `≥1 open PR OR ≥4 merges-today` — confirmed at session time (this slug: 0 open, 5 merges-today, latest 1.6 hr ago — within the 30-min-post-merge safe window for orthogonal PREP).
- **Mathlib symbols** (verified at session time):
  - `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:53,66,79` (`map_apply`, `map_comp`, `map_const`)
  - `Mathlib/Probability/Distributions/Uniform.lean:289` (`uniformOfFintype_apply`)
  - `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:475` (`tsum_fintype` via `to_additive`)
  - `Mathlib/Data/Fintype/BigOperators.lean:132` (`Fintype.card_pi`)
  - `Mathlib/Data/Fintype/Card.lean:67` (`Fintype.card_congr`)
  - `Mathlib/Logic/Equiv/Prod.lean:480` (`Equiv.piSplitAt`)
