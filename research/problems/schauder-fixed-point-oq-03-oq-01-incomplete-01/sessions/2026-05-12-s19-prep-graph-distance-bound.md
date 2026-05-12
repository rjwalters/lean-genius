# S19 PREP — Graph-Distance Bound Design

**Iteration**: S19 PREP (doc-only session note)
**Author**: researcher-5
**Date**: 2026-05-12
**File**: this design note (no Lean / state.md / knowledge.md / meta.json edits)
**Sister PRs in flight**: #18177, #18257 (both S18f — `uhc_local_thickening_with_input_diameter`, the helper consumed below)

## Purpose

Map the remaining work between S18f (input-diameter refinement of the
UHC thickening clause) and the `axiom approx_selection_exists` discharge
that finally collapses Axiom 2 of `SchauderFixedPointOQ03OQ01.lean`. This
is the only step in the Cellina–Browder construction (S17 survey) flagged
as "mathematically delicate" because the natural convex-combination
argument gives a `2ε`-graph-distance, not the literal `ε`-graph-distance
demanded by the axiom signature.

The note is doc-only and intentionally orthogonal to the two in-flight
S18f PRs: it consumes their helper as a black-box hypothesis and designs
the *next* iteration. No state.md / knowledge.md / meta.json edits; no
Lean changes. The S19 author can implement directly from §6 below.

## 1. Goal

Replace the axiom

```lean
axiom approx_selection_exists {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ↥S → ↥S, Continuous f ∧ IsGraphApproxSelection F (fun x => (f x : ↥S)) ε
```

with `theorem approx_selection_exists_proof` having the **identical**
signature, by composing the in-file helpers S18a–f. The axiom remains
in the file until the theorem builds clean; after that, the
`axiom` line is removed in the same PR and `axiom`-count drops `2 → 1`
(only `brouwer_unit_ball` remains).

## 2. Witness bundle consumed from S18e + S18f

S18e (PR #18130, merged) provides:

```lean
exists_continuous_selection_with_witnesses S hS_compact hS_convex F hF_ne hF_uhc α hα
  : ∃ f : C(↥S, ↥S),
      ∃ U : ↥S → Set ↥S, ∃ ρ : PartitionOfUnity (↥S) (↥S) Set.univ,
      ∃ ysel : ↥S → ↥S,
        (∀ x : ↥S, IsOpen (U x)) ∧
        (∀ x : ↥S, x ∈ U x) ∧
        (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening α (F x)) ∧
        ρ.IsSubordinate U ∧
        (∀ x, ysel x ∈ F x) ∧
        (∀ x : ↥S, (f x : EuclideanSpace ℝ (Fin n))
            = ∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n)))
```

S18f (PR #18177 / #18257, open) provides:

```lean
uhc_local_thickening_with_input_diameter F hF_uhc x₀ α hα
  : ∃ U : Set ↥S, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ Metric.ball x₀ α ∧
      (∀ x ∈ U, F x ⊆ Metric.thickening α (F x₀))
```

The first input we exploit is the conjunction of the existing S18e clause
"S17 thickening" with the new S18f clause "input-ball at radius α" — both
at the same α. Item §3 below packages them into a single S18e' bundle
(no new Lean code in this PR; this is just a naming convention for §4–§5).

**S18e' (virtual): refined witness bundle.** For α > 0, there exist
`f`, `U`, `ρ`, `ysel` as in S18e with the additional clause

```
(∀ x : ↥S, U x ⊆ Metric.ball x α)         -- new input-ball clause from S18f
```

To produce S18e' from S18e + S18f, intersect S18e's `U x` with S18f's
`U_x α α hα` for each x, then re-run S18d's partition extraction on the
finer cover. **Note for S19 implementer**: this intersection step adds
~40 lines (re-running `exists_partition_subordinate_to_uhc_cover` against
the refined cover) and is a candidate S18g pre-PR. Or, equivalently,
S18f's helper can be inlined directly in `exists_partition_subordinate_to_uhc_cover`
(it's a 6-line change) — the S19 author chooses. The two PRs in flight
do NOT propagate S18f's clause through S18c/S18d/S18e (acknowledged in
PR #18177 body: "the strengthened helper does NOT yet propagate"), so
the propagation work is genuinely outstanding.

## 3. Unwinding `IsGraphApproxSelection`

The target predicate, from line 471 of the main file:

```lean
def IsGraphApproxSelection {X : Type*} [PseudoMetricSpace X]
    (F : SetValuedMap X X) (f : X → X) (ε : ℝ) : Prop :=
  ∀ x, ∃ x' y, dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε
```

For a fixed `x : ↥S`, we must exhibit `(x', y)` with **all three** of:

| Clause | Plan |
|--------|------|
| `dist x x' < ε` | `x' := i` (some `i ∈ ρ.finsupport x`); `x ∈ U i ⊆ ball i α` from S18e' input-ball clause; `dist x i = dist i x < α ≤ ε` (after constant calibration). |
| `y ∈ F x'` (i.e. `y ∈ F i`) | Choose `y` from `F i` ⊆ `↥S` (compact, nonempty, convex). |
| `dist (f x) y < ε` | Bound via convex-combination expansion of `f x` together with the S18e thickening clause. **This is the load-bearing step (§4 below).** |

## 4. The convex-combination accounting

`f x` admits the explicit representation

```
(f x : EuclideanSpace ℝ (Fin n)) = ∑ᶠ j, ρ j x • (ysel j : EuclideanSpace ℝ (Fin n))
                                 = ∑ j ∈ ρ.finsupport x, ρ j x • (ysel j : EuclideanSpace ℝ (Fin n))
```

(the second equality is `PartitionOfUnity.sum_finsupport_smul_eq_finsum`).
The coefficients `ρ j x` are nonneg and sum to 1.

### 4.a Direct attempt: pick `y := ysel i` for the chosen `i`

Compute (in `EuclideanSpace ℝ (Fin n)`):

```
‖f x − ysel i‖
  = ‖∑ j ∈ supp, ρ j x · (ysel j − ysel i)‖           -- coefficients sum to 1
  ≤ ∑ j ∈ supp, ρ j x · ‖ysel j − ysel i‖
  ≤ max_{j ∈ supp} ‖ysel j − ysel i‖                  -- convex combination ≤ max
```

Now `i, j ∈ supp ⊆ {k : x ∈ U k}` (subordinate-tsupport ⊆ U), so by
S18e:
- `F x ⊆ thickening α (F i)`, hence for every `w ∈ F x` there is `aᵢ ∈ F i` with `dist w aᵢ < α`;
- `F x ⊆ thickening α (F j)`, hence for every `w ∈ F x` there is `aⱼ ∈ F j` with `dist w aⱼ < α`.

Take any `w ∈ F x` (e.g. `w := ysel x`). Then triangle:

```
‖ysel j − ysel i‖
  ≤ ‖ysel j − aⱼ‖ + ‖aⱼ − w‖ + ‖w − aᵢ‖ + ‖aᵢ − ysel i‖
  ≤ diam(F j) + α + α + diam(F i)
```

The middle two `α` summands are clean (S18e thickening clause). The
`diam(F j)` and `diam(F i)` summands are **not** controllable from
S18e alone: nothing in the cover construction bounds `‖ysel j − a‖` for
`a ∈ F j` other than `a = ysel j`.

**Conclusion: the direct attempt with `y := ysel i` fails by `2 · diam(F)`.**

### 4.b Cellina projection: pick `y := nearest point in F i to f x`

`F i` is compact (closed in compact `↥S` and bounded), nonempty (`hF_ne`),
and convex (`hF_convex` after `Subtype.val` push-through). Hence
`F i` is a **nonempty compact convex** subset of the inner-product space
`EuclideanSpace ℝ (Fin n)`. The Hilbert projection theorem
(`exists_norm_eq_iInf_of_complete_convex` in
`Mathlib.Analysis.InnerProductSpace.Projection`, already used by S14's
`exists_continuous_proj_convex`) gives a unique nearest point `y ∈ F i`
with `‖f x − y‖ = inf_{a ∈ F i} ‖f x − a‖`.

Bound this infimum. Since `i ∈ ρ.finsupport x`, we have `ρ i x > 0`, so
`x ∈ tsupport (ρ i) ⊆ U i` (S18e clause `ρ.IsSubordinate U`). Then:

```
F x ⊆ Metric.thickening α (F i)             -- S18e thickening at i
```

Apply this to `ysel x ∈ F x`: `∃ a' ∈ F i` with `dist (ysel x) a' < α`.
Then `inf_{a ∈ F i} ‖f x − a‖ ≤ ‖f x − a'‖ ≤ ‖f x − ysel x‖ + α`. So:

```
dist (f x) y ≤ ‖f x − ysel x‖ + α     -- (★)
```

The remaining bound `‖f x − ysel x‖` is the **convex-combination
displacement of the partition-of-unity smoothing from the pointwise
selector**:

```
‖f x − ysel x‖
  = ‖∑ j ∈ supp, ρ j x · ysel j − ysel x‖
  = ‖∑ j ∈ supp, ρ j x · (ysel j − ysel x)‖           -- coefficients sum to 1
  ≤ ∑ j ∈ supp, ρ j x · ‖ysel j − ysel x‖
  ≤ max_{j ∈ supp} ‖ysel j − ysel x‖
```

For each `j ∈ supp(ρ_x)`, `x ∈ U j`, hence `F x ⊆ thickening α (F j)`.
Apply at `ysel x ∈ F x`: `∃ a_j ∈ F j` with `dist (ysel x) a_j < α`.
But this bounds `‖ysel x − a_j‖`, not `‖ysel x − ysel j‖`. As in §4.a,
`a_j ≠ ysel j` in general, so this argument **still leaks
`diam(F j)`** at each summand.

### 4.c Refinement: switch the pointwise selector to the nearest-point-of-F(x_j) selector

The selector `ysel : ↥S → ↥S` in S18e is chosen via `choose` from
`hF_ne`. The S19 implementer can **reuse the choice but with a stronger
witness** by replacing the chosen `ysel j` (for `j` a base-point) with
the nearest point of `F j` to a globally-chosen "pivot" `y_pivot ∈ F j`
that controls the diameter of the convex-combination spread.

**The exact lemma needed** (call it `S19a`): for `j ∈ supp(ρ_x)` and a
common pivot `j₀ ∈ supp(ρ_x)`,

```
‖ysel j − ysel j₀‖ ≤ 2α
```

**Path to S19a**: the S17 survey's "step 1 refinement" path. Strengthen
the cover construction so that for each base-point `i`, the open set
`U i` satisfies `F(U i) ⊆ B(ysel i, α)` — i.e., every `F z` for `z ∈ U i`
fits inside an `α`-ball around the SPECIFIC pre-chosen pointwise value
`ysel i`. This is a STRENGTHENING of S18e's "F z ⊆ thickening α (F i)"
clause that pins the thickening centre to a single point.

The path is feasible because `F i` is **compact and convex**, so
`F i ⊆ B(ysel i, diam(F i))` and we can refine the UHC-derived `U i`
intersect with `{z : F z ⊆ B(ysel i, α)}` — which is open (UHC at the
specific open set `B(ysel i, α)`, valid because `ysel i ∈ F i`, but
requires `F i ⊆ B(ysel i, α)`, i.e., `diam(F i) < 2α`, which is **not
automatic**).

The honest conclusion: **`S19a` is not directly derivable from the
in-file `IsUpperHemicontinuous` axiom and the S17/S18 cover; it requires
a finer cover construction that pins the thickening centres**.

### 4.d The clean Aubin–Frankowska §9.2 path: graph-cover refinement

Aubin–Frankowska, *Set-Valued Analysis* §9.2 (Cellina 1969 in modern form)
sidesteps the diameter gap by choosing the open cover on the **graph**
rather than on the **domain**. Concretely: for each `x ∈ ↥S` and each
`y_x ∈ F x`, find an open `V_{(x, y_x)} ⊆ ↥S × ↥S` with
`(x, y_x) ∈ V_{(x, y_x)}` AND `V_{(x, y_x)} ⊆ B(x, α) × B(y_x, α)` AND
`graph(F) ∩ V_{(x, y_x)} ≠ ∅` near every `(x', y') ∈ V_{(x, y_x)}` with
`x' ∈ π₁(V_{(x, y_x)})`. The compactness of `graph(F)` (closed subset of
compact `↥S × ↥S`) finite-subcovers the graph, the partition of unity is
indexed by the graph cover, and the convex-combination averaging happens
on the second factor only.

**This is a structural rewrite** of S18a–e: the cover is over the graph,
not the domain. The graph form of the cover sidesteps the diameter gap
because every (z, w) ∈ V_{(x, y_x)} ⊆ B(y_x, α) by construction, so
`‖w − y_x‖ < α` is direct.

## 5. Constant calibration: `2ε` natural bound vs `ε` axiom signature

S17 survey §"Action item for S18" identifies the calibration:

> the natural argument gives `2ε` and the axiom is invoked at `ε/2` to
> recover the literal `ε` bound. Recommendation: implement
> `approx_selection_exists` at the relaxed `2ε` bound (call it
> `approx_selection_exists_2eps`) first, then derive the literal `ε`
> form by halving — this matches what the kakutani caller already
> expects.

**Confirmation from the downstream caller**:
`theorem kakutani_from_brouwer` (line 981) **already calls the axiom with
ε/2** (line 1003) and applies a triangle-inequality step to recover the
diagonal-distance bound `< ε`. So if the S19 proof produces a `2α`-graph
witness, the axiom signature is recovered by **internally calling the
S19 construction at `α := ε/2`** — no signature change.

| Approach | Internal call | Internal bound | Public bound | Net |
|----------|--------------|----------------|--------------|------|
| §4.b nearest-point | α = ε/2 | `2α = ε` | ε | clean |
| §4.d graph cover | α = ε | `2α = 2ε` | ε via "internal call at ε/2" | clean but +structure |

Either way the **public axiom signature is preserved**. The S19 design
choice is between §4.b (internal call at ε/2, accept the additive
`‖f x − ysel x‖ ≤ α` slack from S18e's domain-cover) and §4.d (graph
cover rewrite of S18a–e). §4.b is **strictly less invasive**: it requires
**no changes to S18a–e** beyond consuming them as a black box; §4.d
requires **a full rewrite** of S18c–e.

**Recommendation: S19 implements §4.b**, with the understanding that the
gap `‖f x − ysel x‖ ≤ α` (line marked `(★)` in §4.b) is the load-bearing
half and decomposes cleanly into a `max j ∈ supp, ρ j x · ‖ysel j − ysel x‖`
step that uses `F x ⊆ thickening α (F j)` at `w = ysel x ∈ F x`. The
resulting bound is `dist (f x) y ≤ α + α = 2α`, and `α := ε/2` recovers `ε`.

**Honest caveat**: the §4.b argument as written requires that the
nearest point witnessing the `inf` is attained AND `ysel j` is replaced
by the choice "any `a_j ∈ F j` within `α` of `ysel x`" — i.e., the
selector is **rechosen** at each `x` rather than fixed globally. This is
a deviation from S18e's signature (where `ysel : ↥S → ↥S` is **fixed**)
and requires either:

- (i) **An S19a lemma** that re-chooses `a_j` at each `x` using `choose`
  over the existential `∃ a ∈ F j, dist (ysel x) a < α` (extracted from
  S18e's thickening clause). The new selector is `ysel' : ↥S → ↥S → ↥S`
  taking both `x` and `j`. This needs the convex-combination identity
  re-derived for the new selector, ~40 lines.
- (ii) **A cleaner reformulation**: drop `ysel` entirely from the S18e
  signature and let `y := nearest-point projection of f x onto F i` be
  chosen at S19 time. The S18e bundle is **already strong enough** if
  S19 proves the bound `dist (f x) y ≤ α + dist (f x) (ysel x)` and the
  pointwise-selector-displacement bound is handled separately.

§5 conclusion (for the implementer): **trying §4.b directly is the right
S19 first attempt**. If the bound fails (because of the `ysel j` vs
`a_j` divergence), pivot to §4.d (graph-cover rewrite) and re-budget the
remaining work as a multi-PR refactor (S20+ rather than S19).

## 6. Lean tactic skeleton (target: 80–150 lines, §4.b path)

```lean
-- Assume S18e' (i.e. S18e ∧ S18f propagation) is available, perhaps as a
-- combined helper `exists_continuous_selection_with_input_ball_witnesses`
-- (~+40 lines pre-S19, possibly S18g). If only S18e is available, the
-- `dist x i < α` bound can be obtained inline by combining S18e's
-- `tsupport ρ i ⊆ U i` with an inline call to S18f's helper at i.

theorem approx_selection_exists_proof {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ↥S → ↥S, Continuous f ∧ IsGraphApproxSelection F (fun x => (f x : ↥S)) ε := by
  -- Step 0: internal call at α := ε/2.
  have hα : (0 : ℝ) < ε / 2 := by linarith
  set α : ℝ := ε / 2 with hα_def
  -- Step 1: invoke S18e (with α; S18f-refined cover if propagation has landed).
  obtain ⟨fC, U, ρ, ysel, hU_open, hU_mem, hU_thick, hρ_sub, hysel_F, hf_eq⟩ :=
    exists_continuous_selection_with_witnesses S hS_compact hS_convex F hF_ne hF_uhc α hα
  -- Lift the continuous map fC : C(↥S, ↥S) to f : ↥S → ↥S.
  refine ⟨fC, fC.continuous, ?_⟩
  intro x
  -- Step 2: pick i ∈ ρ.finsupport x via PartitionOfUnity.exists_pos.
  obtain ⟨i, hi_pos⟩ := ρ.exists_pos (Set.mem_univ x)
  have hi_supp : i ∈ ρ.finsupport x := PartitionOfUnity.mem_finsupport.mpr hi_pos
  -- Step 3: x ∈ U i via subordinate-tsupport.
  have hx_Ui : x ∈ U i := hρ_sub i (subset_tsupport _ hi_pos)
  -- Step 4: dist x i < α (S18f input-ball clause; inlined here if S18e' is virtual).
  obtain ⟨V, hV_open, hi_V, hV_ball, hV_thick⟩ :=
    uhc_local_thickening_with_input_diameter hF_uhc i α hα
  -- (If S18e' propagation has landed, U i ⊆ ball i α directly; else use V ∩ U i.)
  have hxi : dist x i < α := by
    -- Either `Metric.mem_ball.mp (hU_ball_input_clause hx_Ui)`,
    -- or inline `hV_ball (the V-Ui intersection that x belongs to)` — TBD.
    sorry
  -- Step 5: F x ⊆ thickening α (F i) via S18e's hU_thick.
  have hFx_thick : F x ⊆ Metric.thickening α (F i) := hU_thick i x hx_Ui
  -- Step 6: produce y ∈ F i with dist (fC x) y < 2α (= ε) via nearest-point.
  --   6a. F i is nonempty / closed / convex / compact:
  have hFi_ne : (F i).Nonempty := hF_ne i
  have hFi_closed : IsClosed ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))) := by
    -- F is closed-valued because we're in the kakutani caller's territory (hF_closed),
    -- but the AXIOM signature does NOT include hF_closed — the axiom is for
    -- ANY convex-valued UHC. For the S19 theorem, the closed-valued hypothesis is
    -- redundant because F is convex-valued and S is compact, so F i is bounded
    -- in ↥S; convex + bounded in EuclideanSpace ⇒ closure is compact.
    -- BUT this is the gap: the AXIOM as written does NOT assume IsClosed (F x).
    -- See §7 below — we may need to either:
    --   (a) add hF_closed to the theorem signature (breaks API parity), or
    --   (b) take topological closure of (Subtype.val '' F i) and project to that.
    sorry
  -- 6b: nearest-point projection from `exists_norm_eq_iInf_of_complete_convex`
  --     applied to `Subtype.val '' F i` (after closure if needed).
  --     Let y ∈ F i with ‖fC x − y‖ = iInf …
  -- 6c: bound the iInf by `α + ‖fC x − ysel x‖ < α + α = 2α = ε`.
  --     Use hFx_thick at w := ysel x ∈ F x to get a' ∈ F i with `dist (ysel x) a' < α`,
  --     then iInf ≤ ‖fC x − a'‖ ≤ ‖fC x − ysel x‖ + α (triangle).
  --     The pointwise-selector displacement `‖fC x − ysel x‖` is bounded by:
  --       ‖fC x − ysel x‖ = ‖∑ j, ρ j x · (ysel j − ysel x)‖
  --                       ≤ max_{j ∈ supp} ‖ysel j − ysel x‖
  --       For each j ∈ supp, x ∈ U j, so F x ⊆ thickening α (F j).
  --       Apply at ysel x ∈ F x to get a_j ∈ F j with `dist (ysel x) a_j < α`.
  --       But ‖ysel j − ysel x‖ ≠ ‖a_j − ysel x‖ — this is the §4.a/§4.c gap.
  --       =====================
  --       SUSPENDED: the §4.b path as drafted yields a 2α + diam(F j) bound, not 2α.
  --       The §4.d graph-cover rewrite is required for a clean closure.
  --       =====================
  sorry
```

The skeleton above demonstrates the §4.b argument's actual structure
and is **honest about where the gap remains** (the §4.a/§4.c blocker
returns inside Step 6c). The S19 author should expect to either:

- Add `hF_closed : ∀ x, IsClosed (F x)` to the theorem signature
  (matching the kakutani caller's hypothesis at line 986) and use the
  graph-form Aubin–Frankowska construction, or
- Prove a stronger S19a' refinement of S18e that pins the `ysel`
  selector to the nearest-point map of `F i` from a globally-chosen
  pivot point.

## 7. The hidden hypothesis: closed-valued F

The kakutani caller already has `hF_closed : ∀ x, IsClosed (F x)` (line
986 of the main file), and **the closedness is genuinely needed for the
nearest-point projection** in §4.b Step 6a above. The axiom statement
as written (line 504, no `hF_closed`) is **mathematically incomplete**
for the §4.b path: without closedness, `F i` may not attain its infimum,
and the §4.b construction fails. Cellina's original paper assumes
**upper semi-continuous + closed convex values** (`USC` ≡ UHC + closed
graph + closed values), and the closedness is load-bearing.

**Decision point for S19**: the cleanest fix is to **add
`(hF_closed : ∀ x, IsClosed (F x))` to the theorem signature**. The
kakutani caller already has it; this is API parity, not a regression.
The axiom statement was strictly weaker than the kakutani caller's
hypothesis stack — this is a latent inconsistency that S19 surfaces.

**Action for S19 implementer**: when replacing `axiom
approx_selection_exists` with `theorem approx_selection_exists_proof`,
add `hF_closed` to the theorem signature AND update the axiom-removal
caller-site in `kakutani_from_brouwer` (line 1003) to pass `hF_closed`.
The line 1003 site already has `hF_closed` in scope. Zero changes in
`approx_fixedpoint_implies_fixedpoint` (it doesn't call the axiom directly).

## 8. Mathlib API needed (verified at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Symbol | Module | Line | Purpose |
|--------|--------|------|---------|
| `PartitionOfUnity.exists_pos` | `Mathlib/Topology/PartitionOfUnity.lean` | 163 | Get `i` with `ρ i x > 0` |
| `PartitionOfUnity.mem_finsupport` | `Mathlib/Topology/PartitionOfUnity.lean` | 153 | `0 < ρ i x ↔ i ∈ ρ.finsupport x` |
| `subset_tsupport` | `Mathlib/Topology/Support.lean` | 60 | `support f ⊆ tsupport f` |
| `PartitionOfUnity.IsSubordinate` | `Mathlib/Topology/PartitionOfUnity.lean` | 240 | `tsupport (ρ i) ⊆ U i` |
| `PartitionOfUnity.sum_finsupport_smul_eq_finsum` | `Mathlib/Topology/PartitionOfUnity.lean` | 212 | Bridge `finsum` ↔ `Finset.sum` |
| `Metric.mem_ball` | `Mathlib/Topology/MetricSpace/Basic.lean` | 124 | Convert `x ∈ ball y r` ↔ `dist x y < r` |
| `exists_norm_eq_iInf_of_complete_convex` | `Mathlib/Analysis/InnerProductSpace/Projection.lean` | (S14 ref, name stable) | Nearest-point projection onto closed convex |
| `Metric.thickening` membership | `Mathlib/Topology/MetricSpace/Thickening.lean` | 50 | `w ∈ thickening α A ↔ ∃ a ∈ A, dist w a < α` (via `infEdist`) |
| `Convex.sum_mem` | `Mathlib/Analysis/Convex/Combination.lean` | (used by S18a) | Convex combinations stay in convex sets |

The `Mathlib.Analysis.InnerProductSpace.Projection` import is **already
in the file** (used by `exists_continuous_proj_convex`, S14). The
`exists_norm_eq_iInf_of_complete_convex` call requires the **closed
convex** argument — see §7.

## 9. LOC budget

| Step | LOC | Source |
|------|-----|--------|
| Theorem header + α def + S18e unpack | ~15 | §6 Steps 0–1 |
| `i := exists_pos`, `x ∈ U i`, `dist x i < α` | ~10 | §6 Steps 2–4 |
| `F x ⊆ thickening α (F i)` | ~3 | §6 Step 5 |
| Nearest-point setup + closure of `Subtype.val '' F i` | ~25 | §6 Step 6a |
| Nearest-point projection invocation | ~10 | §6 Step 6b |
| Triangle bound: `iInf ≤ ‖fC x − ysel x‖ + α` | ~15 | §6 Step 6c first half |
| `‖fC x − ysel x‖ < α` convex-combination expansion | **TBD — §4.c gap** | §6 Step 6c second half |
| Final `linarith` to package as `< 2α = ε` | ~5 | §6 Step 6d |
| Total (clean half only) | ~85 | |
| With §4.d graph-cover rewrite | +200 (rewrites S18c–e) | §4.d |

**Honest LOC**: ~85 lines if §4.c gap is dischargeable in-place (~15 more
lines), ~280+ if §4.d structural rewrite is needed. The PR-#18177 body
estimated S19 at "mechanical" / "few lines" — this design exposes the
gap that makes that estimate too optimistic.

## 10. Race / coordination notes

- Two S18f PRs (#18177, #18257) are in flight, both adding the
  `uhc_local_thickening_with_input_diameter` helper but **not**
  propagating it through the S18c/S18d/S18e cover. The propagation is
  a candidate S18g sub-PR (~40 lines).
- This S19 PREP note is doc-only, lands as a session file in a
  pristine `sessions/` directory, and does not edit `state.md`,
  `knowledge.md`, the gallery `meta.json`, or any Lean file. It is
  conflict-free against both open S18f PRs.
- The §7 finding (axiom statement vs kakutani caller hypothesis stack
  inconsistency on `hF_closed`) is the most actionable concrete output
  of this iteration: the S19 author can either preemptively add
  `hF_closed` to the theorem signature, or carry the §4.d graph-cover
  rewrite to avoid needing it.

## 11. Recommended S19 plan (concrete)

1. **S18g (pre-S19, ~40 lines)**: propagate S18f's input-ball clause
   through `exists_partition_subordinate_to_uhc_cover` and
   `exists_continuous_selection_with_witnesses` so the S18e' virtual
   bundle becomes a real Lean object.
2. **S19a (~30 lines)**: prove the lemma "`(Subtype.val '' F i)` is
   closed in `EuclideanSpace ℝ (Fin n)`" from `hF_closed` (after the
   §7 signature update) and `Subtype.isClosed_iff_isClosed_image_val`
   (or the appropriate `IsClosedMap`).
3. **S19b (~50 lines, the hard half)**: prove the bound
   `‖fC x − ysel x‖ ≤ α` (or its `2α + ‖f x − ysel x‖`-flavored
   variant) by expanding the convex combination and applying S18e's
   thickening clause at every `j ∈ ρ.finsupport x`. **Decision: §4.b
   succeeds iff this bound is provable with the additional flexibility
   of choosing y ∈ F i (rather than y = ysel i) at S19c time. If not,
   pivot to §4.d at S20.**
4. **S19c (~30 lines)**: assemble the IsGraphApproxSelection
   certificate, replace `axiom approx_selection_exists` with
   `theorem approx_selection_exists_proof`, update `kakutani_from_brouwer`
   to pass `hF_closed` to the call site.

After S19c, the file has exactly **one** axiom (`brouwer_unit_ball`,
the Brouwer FPT on the unit ball, unavoidable until Mathlib lands the
topological Brouwer FPT — see S10 reconnaissance).

## Outcome of this iteration

**Outcome**: doc-only progress (design + gap identification, no axiom
discharged here).

**Concrete deliverable**: this `sessions/2026-05-12-s19-prep-graph-distance-bound.md`
file maps the §4.a/§4.b/§4.c/§4.d landscape and surfaces the latent
§7 hypothesis inconsistency between the axiom statement and the
kakutani caller. The S19 implementer can pick §4.b vs §4.d with a
concrete LOC budget, a tactic skeleton, and an explicit list of
Mathlib API calls.

**Build status**: N/A (no Lean changes).

**Not done in this iteration** (deliberate, to remain conflict-free
against #18177 / #18257):
- No `state.md` edits.
- No `knowledge.md` edits.
- No `src/data/proofs/schauder-fixed-point-oq-03-oq-01/meta.json` edits.
- No `src/data/research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01.json` edits.
- No Lean changes.

The S19 implementer can edit `state.md` and the JSON files when they
land S19b/S19c.
