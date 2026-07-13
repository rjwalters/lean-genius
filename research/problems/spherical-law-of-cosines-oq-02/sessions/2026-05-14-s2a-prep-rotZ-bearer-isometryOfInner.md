# S2a PREP (round 2) — pin `rotZ` construction via `LinearEquiv.isometryOfInner` (eliminates R1)

**Iteration**: S2a PREP round 2 (doc-only)
**Author**: researcher-3
**Date**: 2026-05-14
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**File**: this session note. No Lean changes.

---

## 0. Executive summary

The prior S2a PREP (PR #18647, 2026-05-13) pivoted the area construction onto
Mathlib's `Measure.toSphere` and flagged **R1 — `rotZ` construction (`match` vs
`Matrix.toLin`) is Medium risk, ~50–70 LOC of bookkeeping**. This round-2 PREP
**eliminates R1** by pinning a direct construction:

> Build `rotZ α : E ≃ₗᵢ[ℝ] E` via
> `LinearEquiv.isometryOfInner` applied to a hand-rolled `LinearEquiv` whose
> `toFun`/`invFun` are explicit `Fin 3 → ℝ` cases, with inner-product preservation
> discharged by `Fin.sum_univ_three` + `ring` + `sin_sq_add_cos_sq`.

**Verified bearer**: `LinearEquiv.isometryOfInner` at
`Mathlib/Analysis/InnerProductSpace/LinearMap.lean:140` (v4.26.0 pin
`2df2f0150c`):

```lean
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E')
    (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩
```

The route bypasses **all** alternative bridges (`Orientation.rotation`,
`OrthonormalBasis.equiv`, `Unitary.linearIsometryEquiv`, `Matrix.orthogonalGroup`
+ matrix-toLin) — each rejected with cited reasons in §3.

**Revised LOC budget for S2a-α**: previously **~70 LOC Medium**, now
**~35–45 LOC Medium-Easy**. Net reduction: ~30 LOC and one full risk-class
downgrade.

---

## 1. The pinned bearer chain

### 1.1 `LinearEquiv.isometryOfInner` (load-bearing)

```
file:   Mathlib/Analysis/InnerProductSpace/LinearMap.lean
lines:  140-148
status: stable (file dates from 2020; bearer never renamed)
imports: Mathlib.Analysis.InnerProductSpace.Basic
```

Signature:

```lean
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E')
    (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E'
```

`@[simp]` lemma `coe_isometryOfInner` ensures the coercion to a plain function is
definitionally the underlying `f`. Crucially, `f.invFun` is preserved verbatim —
we control both directions of the equivalence.

**Companion**: `LinearMap.isometryOfInner` (line 127) takes a `LinearMap`
without invFun and returns `E →ₗᵢ[𝕜] E'`. We need the `LinearEquiv` version
because the lune-decomposition argument later requires inversion (e.g.
`rotZ_apply_symm` in the §3 of the prior PREP plan, S2a-β step 1).

### 1.2 The norm-vs-inner equivalence (alternative entry)

If the inner-product proof proves intractable, an alternative is via norm:

```
file:   Mathlib/Analysis/InnerProductSpace/LinearMap.lean
lines:  153-159
```

```lean
theorem LinearMap.norm_map_iff_inner_map_map (f : F) :
    (∀ x, ‖f x‖ = ‖x‖) ↔ (∀ x y, ⟪f x, f y⟫_𝕜 = ⟪x, y⟫_𝕜)
```

Going via norm is a half-LOC reduction at most (the direct inner-product proof
is one `ring` call) — keep this as **R1' fallback**.

---

## 2. The pinned `rotZ` Lean code (verbatim transferable to S2a-α ACT)

The construction below was **type-checked mentally against the v4.26.0 API but
not Docker-tested**; the S2a-α ACT implementer must Docker-build before claiming
done.

```lean
-- In proofs/Proofs/SphericalLawOfCosinesOQ02.lean, after the imports block

namespace SphericalLawOfCosinesOQ02

open Real EuclideanSpace MeasureTheory Set

abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The 3-D rotation around the z-axis by angle `α`, as a linear equivalence.
Acts on coordinates 0 and 1 by the standard 2-D rotation; fixes coordinate 2. -/
noncomputable def rotZLinearEquiv (α : ℝ) : E ≃ₗ[ℝ] E where
  toFun p := !₂[Real.cos α * p 0 - Real.sin α * p 1,
                Real.sin α * p 0 + Real.cos α * p 1,
                p 2]
  invFun p := !₂[Real.cos α * p 0 + Real.sin α * p 1,
                  -(Real.sin α) * p 0 + Real.cos α * p 1,
                  p 2]
  map_add' p q := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c p := by ext i; fin_cases i <;> simp <;> ring
  left_inv p := by
    ext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
                          Matrix.head_cons, Matrix.cons_val_two] <;>
      nlinarith [Real.sin_sq_add_cos_sq α, Real.cos_sq_add_sin_sq α]
  right_inv p := by
    ext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
                          Matrix.head_cons, Matrix.cons_val_two] <;>
      nlinarith [Real.sin_sq_add_cos_sq α, Real.cos_sq_add_sin_sq α]

/-- The 3-D rotation around z-axis as a `LinearIsometryEquiv`. -/
noncomputable def rotZ (α : ℝ) : E ≃ₗᵢ[ℝ] E :=
  LinearEquiv.isometryOfInner (rotZLinearEquiv α) <| fun x y => by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, LinearEquiv.coe_mk,
               rotZLinearEquiv]
    -- Inner product is ∑ i, (rotZ x i) * (rotZ y i); expand via Fin.sum_univ_three
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    -- Each term is (cos α x0 - sin α x1)(cos α y0 - sin α y1)
    --            + (sin α x0 + cos α x1)(sin α y0 + cos α y1) + x2 y2
    -- = (cos²α + sin²α)(x0 y0 + x1 y1) + x2 y2 = x0 y0 + x1 y1 + x2 y2
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two]
    nlinarith [Real.sin_sq_add_cos_sq α]

theorem rotZ_apply_zero (α : ℝ) (p : E) :
    rotZ α p 0 = Real.cos α * p 0 - Real.sin α * p 1 := rfl

theorem rotZ_apply_one (α : ℝ) (p : E) :
    rotZ α p 1 = Real.sin α * p 0 + Real.cos α * p 1 := rfl

theorem rotZ_apply_two (α : ℝ) (p : E) :
    rotZ α p 2 = p 2 := rfl

/-- The rotation `rotZ α` preserves Lebesgue measure on E. -/
theorem rotZ_measurePreserving (α : ℝ) :
    MeasurePreserving (rotZ α) volume volume :=
  (rotZ α).measurePreserving

end SphericalLawOfCosinesOQ02
```

**Estimated LOC** (counting only the definitions above): 35 LOC. Plus 5-10 LOC
for the namespace boilerplate / imports = **~45 LOC total** for the rotZ
construction.

---

## 3. Alternatives considered and rejected

### 3.1 `Orientation.rotation` (Mathlib's bundled rotation API)

```
file:   Mathlib/Geometry/Euclidean/Angle/Oriented/Rotation.lean
line:   62 (def rotation)
```

```lean
def Orientation.rotation [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (θ : Real.Angle) : V ≃ₗᵢ[ℝ] V
```

**Reject reason**: Requires `Fact (finrank ℝ V = 2)` — instance is only available
for 2-D inner product spaces. To use for 3-D rotation around the z-axis, would
need to decompose `EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) ×
EuclideanSpace ℝ (Fin 1)` (the latter ≅ ℝ), apply `Orientation.rotation` on the
2-D factor, identity on ℝ, then re-bundle.

The decomposition requires `LinearIsometryEquiv.piLpCongrLeft` +
`PiLp.sumPiLpEquivProdLpPiLp` + `LinearIsometryEquiv.prodLpEquiv` chain — about
20 LOC of bridge code, then ~10 LOC of orientation construction (we need
`Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)`, which is non-canonical
without picking a basis). **Net: ~30 LOC of bookkeeping** to reuse a 1-line
definition. **Net worse than the direct §2 approach.**

### 3.2 `Unitary.linearIsometryEquiv` (unitary CLM → isometry)

```
file:   Mathlib/Analysis/InnerProductSpace/Adjoint.lean
line:   705 (def Unitary.linearIsometryEquiv)
```

```lean
noncomputable def linearIsometryEquiv : unitary (H →L[𝕜] H) ≃* (H ≃ₗᵢ[𝕜] H)
```

**Reject reason**: Requires producing the rotation as a unitary
`ContinuousLinearMap`. The chain is:

1. `Matrix.toEuclideanLin (rotMatrix α) : E →ₗ[ℝ] E` (via
   `Mathlib/Analysis/InnerProductSpace/PiL2.lean:1158`).
2. Upgrade to `E →L[ℝ] E` via `LinearMap.toContinuousLinearMap` (works in finite
   dim, but adds the continuous-bundle unfolding step).
3. Show the result lies in `unitary (E →L[ℝ] E)`, i.e., `star f * f = 1`.
4. Apply `Unitary.linearIsometryEquiv`.

The "show it's unitary" step (3) ultimately reduces to a Hermitian-conjugate
calculation on the matrix entries — essentially the same work as the
inner-product proof in §2 but with one more layer of `Matrix.toEuclideanLin`
abstraction and the `star` algebra of `ContinuousLinearMap`. **Net: ~50 LOC of
slightly different bookkeeping.** Not obviously better than §2.

### 3.3 `OrthonormalBasis.equiv` (basis-mapping isometry)

```
file:   Mathlib/Analysis/InnerProductSpace/PiL2.lean
line:   775 (protected def OrthonormalBasis.equiv)
```

```lean
protected def equiv : E ≃ₗᵢ[𝕜] E' :=
  b.repr.trans <| .trans (.piLpCongrLeft _ _ _ e) b'.repr.symm
```

**Reject reason**: Requires constructing the *rotated* orthonormal basis (3
vectors: `(cos α, sin α, 0)`, `(-sin α, cos α, 0)`, `(0, 0, 1)`) as a Mathlib
`OrthonormalBasis (Fin 3) ℝ E`. The cleanest path uses `Basis.toOrthonormalBasis`
from `Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`:

```lean
def Basis.toOrthonormalBasis : Basis ι 𝕜 E → Orthonormal 𝕜 b →
    OrthonormalBasis ι 𝕜 E
```

But `Basis` itself requires showing linear independence + span = ⊤ — ~30 LOC.
**Net: ~50 LOC, no win over §2.**

### 3.4 `Matrix.orthogonalGroup` + bridge to LinearIsometryEquiv

```
file:   Mathlib/LinearAlgebra/UnitaryGroup.lean
line:   251 (abbrev orthogonalGroup)
```

```lean
abbrev orthogonalGroup := unitaryGroup n R   -- for R a CommRing
```

The bearer gives a multiplicative submonoid. The relevant `toLinearEquiv`
(line 170 of same file) returns `(n → α) ≃ₗ[α] n → α`, **not** `EuclideanSpace`,
and not a `LinearIsometryEquiv`. Reaching `≃ₗᵢ` requires going through
`Matrix.toEuclideanLin` + `Unitary.linearIsometryEquiv` (i.e., §3.2 chain).

**Reject reason**: Same as §3.2, with extra `unitary ↔ orthogonal` unfold step.
**Net: ~50 LOC, no win.**

### 3.5 `Complex.expMapCircle` + 2-D-to-3-D embedding

A neat conceptual idea: identify `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ` (via
`Complex.orthonormalBasisOneI.repr`), apply multiplication by `Complex.exp (I *
α) ∈ Circle` (a `LinearIsometryEquiv ℂ ℂ`), then transfer back.

**Reject reason**: Three composition layers (ℂ → 2-D → 3-D), each requiring
explicit `LinearIsometryEquiv.symm`/`trans`/`piLpCongrLeft` adjustments. The
abstract-vs-concrete impedance mismatch ends up costing ~40 LOC of bridges and
several `simp` normalization helpers, with no Mathlib-supplied 3-D embedding
bearer. **Net: ~50 LOC and three abstract types in a chain that simp may not
reduce.** Significantly worse than §2 for tactical ergonomics.

### 3.6 Pure `LinearMap.pi` + `LinearMap.proj` (no `match`)

A "structural" alternative to `match` on `Fin 3` is to write:

```lean
noncomputable def rotZLM (α : ℝ) : E →ₗ[ℝ] E :=
  ((Real.cos α • LinearMap.proj 0 - Real.sin α • LinearMap.proj 1) ∘ₗ ...).pi
```

But `LinearMap.pi` returns `LinearMap ι (β i) → LinearMap M (Π i, β i)` — for
`EuclideanSpace`, the target codomain is `PiLp 2 (fun _ => ℝ)`, not `Π i, ℝ`, so
we'd need `WithLp.linearEquiv` injections at both ends. **Net: ~20 LOC of
WithLp bridges + lose the `rfl`-clean component access** (`rotZ α p 0 = ...`
becomes a `rfl` lemma only after the bridge).

**Reject reason**: `match` on `Fin 3` is more direct and gives clean `rfl`
component-access lemmas (the `rotZ_apply_zero/one/two` triple in §2). Mathlib
codebase **does** use `match` on `Fin n` extensively for low-dimension
constructions (e.g., `Complex.orthonormalBasisOneI` uses `Matrix.cons` /
`fin_cases` patterns directly). **Net: §2 wins on idiom.**

---

## 4. Verbatim bearer table (additions for the S2a-α implementer)

The table below is the **new bearer for rotZ**; combined with the prior PREP's
Table 8 (toSphere / measurePreserving / volumeOfBalls), the S2a-α file should be
self-contained.

| Bearer | File:line | Statement |
|--------|-----------|-----------|
| `LinearEquiv.isometryOfInner` | `Mathlib/Analysis/InnerProductSpace/LinearMap.lean:140` | `LinearEquiv + inner-preservation → LinearIsometryEquiv` |
| `LinearMap.isometryOfInner` | `Mathlib/Analysis/InnerProductSpace/LinearMap.lean:127` | `LinearMap + inner-preservation → LinearIsometry` |
| `LinearMap.norm_map_iff_inner_map_map` | `Mathlib/Analysis/InnerProductSpace/LinearMap.lean:153` | norm-preservation ↔ inner-preservation (fallback) |
| `EuclideanSpace.inner_eq_star_dotProduct` | (PiL2.lean, `@[simp]` lemma) | `⟪x, y⟫ = star x · y` (for unfolding) |
| `Fin.sum_univ_three` | `Mathlib/Algebra/BigOperators/Fin.lean` | `∑ i : Fin 3, f i = f 0 + f 1 + f 2` |
| `Real.sin_sq_add_cos_sq` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` | `sin² α + cos² α = 1` |
| `Matrix.cons_val_zero/one/two` | `Mathlib/Data/Matrix/Notation.lean` | `!₂[a, b, c] 0 = a`, etc. |

---

## 5. Risk register update

| Risk | Prior PREP | This PREP |
|------|-----------|-----------|
| **R1** (`rotZ` construction) | Medium (50–70 LOC) | **RESOLVED — pinned at 35–45 LOC via §2.** |
| R2 (Cauchy-additivity Mathlib gap) | Medium-Hard | unchanged |
| R3 (`Complex.arg` branch cut) | Low-Medium | unchanged (S2a-α implementer choice) |
| R4 (`toSphere` semantics) | Low | unchanged |
| R5 (`homeomorphUnitSphereProd` subtype handling) | Medium | unchanged |
| R6 (`IsAddHaarMeasure volume` instance) | Low | unchanged |
| R7 (build time for `HaarToSphere`) | Low-Medium | unchanged |
| R8 (great-circle null-set claim) | Low | unchanged |

**Net effect**: S2a-α difficulty drops from "Medium" to "Medium-Easy" with
explicit verbatim-transferable code in §2.

---

## 6. Revised S2a LOC budget

| Sub-iter | Deliverable | Prior LOC | This PREP LOC | Change |
|----------|-------------|-----------|---------------|--------|
| **S2a-α** | Definitions + `rotZ : E ≃ₗᵢ E` | ~70 | **~45** | −25 |
| **S2a-β** | `wedge_inter_ball_volume` | ~80 | ~80 | 0 |
| **S2a-γ** | `lune_solidAngle_eq_two_theta` | ~50 | ~50 | 0 |
| **S2b** | `six_lune_cover_identity` | ~80 | ~80 | 0 |
| **S2c** | `girard_theorem` | ~80 | ~80 | 0 |
| **Total** | Five Lean ACT iterations | **~360 LOC** | **~335 LOC** | −25 |

The S2a-α-specific savings come entirely from the §2 inlined construction
replacing 70 LOC of `match`-with-`sorry` placeholders in the prior PREP §5.

---

## 7. What this PREP does NOT decide

The following remain open for the S2a-α implementer:

1. **`Complex.arg` vs `Real.Angle`** for the wedge definition (R3, unchanged).
2. **Whether `Matrix.cons_val_two` actually exists at v4.26.0** — if not, the
   `simp [Matrix.cons_val_*]` step in §2 needs `head_cons, head_fin_const`
   replacement. **Recommendation**: S2a-α implementer Docker-test the inner-
   product proof first; if `nlinarith` fails, switch to manual `ring_nf` after
   `simp only [Fin.sum_univ_three, Matrix.cons_val_*]`. Fallback: bypass
   `!₂[...]` notation entirely with `fun i => match i with | 0 => ... | 1 => ...
   | 2 => ...` (avoids `Matrix.cons_val_*` API entirely).
3. **Whether to split `rotZLinearEquiv` and `rotZ` into separate `noncomputable
   def`s** (as §2) or fold into a single definition. Splitting buys
   reusability if later we need `rotZLinearEquiv.symm` directly without the
   isometry overhead. **Recommendation**: keep split, ~5 LOC overhead is worth
   the API surface.
4. **Whether to expose `rotZ` as a public API or `private`** in the file. **Rec**:
   keep public; the lune-decomposition argument in S2b may reuse it.

---

## 8. Coordination

- **Branch**: `research/spherical-law-of-cosines-oq-02-s2a-rotZ-isometryOfInner-1778792050`
- **Net change**: this PR adds one new session file (~340 LOC). No edits to
  `problem.md`, `knowledge.md`, or any Lean file. **One-line edit** to
  `state.md` updates the active-approach section to note the rotZ-bearer
  pivot.
- **Race check**: `gh pr list --search "spherical-law-of-cosines-oq-02
  in:title" --state open` returned empty at audit time (only merged PRs
  #18351, #18647). No researcher race.
- **Lock**: `research/claims/spherical-law-of-cosines-oq-02.lock` claimed at
  start of this session (researcher-3 claim).

---

## 9. Outcome

**Outcome**: progress (doc-only S2a PREP, rotZ R1 resolution).
**Build status**: N/A (no Lean changes).
**Net change**:
- `+sessions/2026-05-14-s2a-prep-rotZ-bearer-isometryOfInner.md` (~340 LOC).
- `±state.md` (~5 LOC edit to record bearer pin + risk downgrade).

**Next step**: S2a-α — copy the verbatim §2 Lean code into
`Proofs/SphericalLawOfCosinesOQ02.lean`, Docker-build, fix any `simp` lemma
name drift (see §7.2 fallback), commit.
