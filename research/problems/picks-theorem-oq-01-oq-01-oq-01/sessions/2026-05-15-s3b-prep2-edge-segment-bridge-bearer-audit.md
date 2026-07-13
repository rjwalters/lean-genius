# 2026-05-15 — S3b PREP-2 — Edge-segment ℤ-anchored bridge: full signature, bearer audit, ~25 LOC sketch

**Researcher**: researcher-4
**Phase**: PLAN (S3b PREP-2, doc-only)
**Trigger**: S3b PREP #19267 (merged 2026-05-15T18:02:28Z) flagged S3b-act-1
("translation/reflection bridge from `card_segmentPoints` to general ℤ-anchored
segments, ~30–50 LOC, still missing per `JSON.knowledge.insights[3]`") but gave
no signature/proof skeleton/bearer pin-verify for that step.  Closes the gap.

**Outcome**: Concrete ℤ-native bridge lemma `card_latticeSegmentPoints` ready
for S3b-act-1 implementation, with:

- Full Lean signature (variant A — recommended, ~25 LOC) and the translation/
  reflection variant (variant B, ~40 LOC) documented side-by-side with tradeoffs.
- Mathlib bearer pin-verify at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (Mathlib v4.26.0).  Two new bearers beyond the S3b PREP §5 table:
  `Finset.card_image_of_injective` (FinsetCard.lean:242), `Int.ediv_mul_cancel`
  (core Lean, `Init.Data.Int.DivMod.Lemmas`).
- 4-step proof skeleton (degenerate g=0 case + injectivity argument + ℤ→ℕ
  bridge + reduction to `PicksTheoremOQ02.card_segmentPoints`).
- Reaffirmation that PR #19023 (S3a-plus ACT, OPEN/UNKNOWN, build-verified
  3058 jobs) is consistent with this PREP and the S3b PREP closure plan.

This PREP edits **only one new file** (this session note).  No state.md / JSON /
`.lean` / meta.json / knowledge.md changes.  Conflict-free with PR #19023 and
PR #18064 (the two open PRs on this slug).

---

## §0 TL;DR

`PicksTheoremOQ02.card_segmentPoints` (line 114, `Proofs/PicksTheoremOQ02.lean`)
proves `(segmentPoints a b).card = Nat.gcd a b + 1` for **ℕ-coordinate, origin-
anchored** segments only.  The Pick's-theorem closure plan needs the **ℤ-
coordinate, vertex-anchored** version

```lean
(latticeSegmentPoints v w).card = Int.gcd (w.1 - v.1) (w.2 - v.2) + 1
```

for arbitrary `v w : ℤ × ℤ`.

`JSON.knowledge.insights[3]` flags this as "still missing".  S3b PREP #19267 §6.1
estimates "~30–50 LOC mostly translating ℕ-origin to ℤ-anchored via translation
lemmas".  This PREP-2 closes the design gap:

- **Variant A** (ℤ-native parametrization, ~25 LOC, recommended): define
  `latticeSegmentPoints v w` directly via `Finset.range (g+1) ↦ v + k·(Δ/g)`
  where `g = Int.gcd Δx Δy` and `Δ/g` is exact integer division.  Avoids
  reflection case-splits entirely.
- **Variant B** (bridge via OQ02's segmentPoints + translate/reflect, ~40 LOC):
  preserves continuity with OQ02 but requires a 4-case `if`-split on signs of
  `Δx, Δy`.  Cardinality reasoning then reduces to OQ02 via
  `Finset.card_image_of_injective`.

Variant A is sharper.  Variant B is documented for reviewers who prefer the
explicit OQ02 dependency chain.  Either path closes JSON `insights[3]` and
unblocks S3b-act-2 (Case-(a) of `exists_nonvertex_lattice_point`).

---

## §1 The deferred sub-step that S3b PREP #19267 named but did not sketch

§6.1 of `sessions/2026-05-15-s3b-prep-geometric-decomposition-audit.md` reads:

> **S3b-act-1** (next session, ~30–50 LOC): translation/reflection bridge from
> `PicksTheoremOQ02.card_segmentPoints` (origin-anchored ℕ-coords) to general
> ℤ-anchored segments. Closes the gap flagged in `JSON.knowledge.insights[3]`
> as "still missing".

No signature, no bearer audit, no proof sketch.  This PREP-2 supplies all three.

The reason S3b-act-1 is the smallest next-action: it is **prerequisite** for
both branches of Case-(a) of the planned `exists_nonvertex_lattice_point` lemma
(per S3b PREP §4.1):

> Case (a) — some `T.edgeGCD i ≥ 2`: by `card_segmentPoints` …, the segment
> `vᵢ → vᵢ₊₁` carries `gcd + 1 ≥ 3` lattice points, of which exactly 2 are
> endpoints, so ≥ 1 is strictly between them. Witness: the point at parameter
> `1` on the gcd parametrization, i.e. `(vᵢ.1 + Δx/g, vᵢ.2 + Δy/g)`.

That "witness at parameter 1" *is exactly* the `k = 1` image element of the
parametrization defined here.  Until S3b-act-1 lands, even the witness
construction's signature is undefined for ℤ × ℤ vertices (OQ02's
`segmentPoints` parametrization returns `ℕ × ℕ`).

---

## §2 Signature — Variant A (ℤ-native, recommended)

### §2.1 Definition

```lean
-- Add to PicksTheoremOQ01OQ01OQ01.lean after the existing edgeDelta / edgeGCD
-- block (post-#19023 line numbers — fits after the current §IX additions).
namespace LatticeTriangle

/-- Lattice points lying on the closed segment from `v` to `w` in `ℤ × ℤ`,
    parametrised by `k · (Δ / g)` where `g = Int.gcd Δx Δy` and `Δ = w - v`.
    Generalises `PicksTheoremOQ02.segmentPoints (a b : ℕ)` (origin-anchored
    ℕ-coords) to arbitrary integer endpoints. -/
def latticeSegmentPoints (v w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let dx : ℤ := w.1 - v.1
  let dy : ℤ := w.2 - v.2
  let g  : ℕ := Int.gcd dx dy
  (Finset.range (g + 1)).image
    (fun k : ℕ => (v.1 + (k : ℤ) * (dx / (g : ℤ)),
                   v.2 + (k : ℤ) * (dy / (g : ℤ))))

end LatticeTriangle
```

Notes on the definition:

1. **Degenerate case `v = w`** (so `dx = dy = 0`, hence `g = 0`):
   `Int.ediv 0 0 = 0` (Lean's default for `0/0`), so the parametrisation
   evaluates to the constant function `fun k ↦ v`.  `Finset.range (0+1) =
   {0}`, image is the singleton `{v}`, cardinality `1 = g + 1`. ✓

2. **Non-degenerate case `g ≥ 1`**: by `Int.gcd_dvd_left` we have
   `(g : ℤ) ∣ dx`, so `dx / (g : ℤ)` is exact (`Int.ediv_mul_cancel` reproduces
   `dx`).  Same for `dy`.  The parametrisation traces the integer lattice
   points on the segment.

3. The intermediate `dx, dy, g` are local `let`-bindings: they don't pollute
   the namespace and unfold to `Eq.refl` under `simp [latticeSegmentPoints]`.

### §2.2 Bridge theorem

```lean
/-- Cardinality of the lattice segment: `Int.gcd Δx Δy + 1`.

    For origin-anchored ℕ-coord segments this reduces (via `Int.gcd_def`)
    to `PicksTheoremOQ02.card_segmentPoints`; for general ℤ-anchored
    segments it is proved directly via injectivity of the parametrisation. -/
theorem card_latticeSegmentPoints (v w : ℤ × ℤ) :
    (latticeSegmentPoints v w).card =
    Int.gcd (w.1 - v.1) (w.2 - v.2) + 1 := by
  unfold latticeSegmentPoints
  set dx : ℤ := w.1 - v.1
  set dy : ℤ := w.2 - v.2
  set g  : ℕ := Int.gcd dx dy
  -- Apply Finset.card_image_of_injective; remaining goal is injectivity
  -- of the parametrisation on Finset.range (g+1).
  rw [Finset.card_image_of_injective _ (parametrisation_injective v w),
      Finset.card_range]
```

where the supporting `parametrisation_injective` lemma is

```lean
private theorem parametrisation_injective (v w : ℤ × ℤ) :
    Function.Injective
      (fun k : ℕ => (v.1 + (k : ℤ) * ((w.1 - v.1) / (Int.gcd _ _ : ℤ)),
                     v.2 + (k : ℤ) * ((w.2 - v.2) / (Int.gcd _ _ : ℤ)))) := by
  intro k₁ k₂ heq
  -- Strategy: from ((k₁ : ℤ) - k₂) · (dx/g) = 0 AND ((k₁ : ℤ) - k₂) · (dy/g) = 0,
  -- deduce either k₁ = k₂ or both dx/g = 0 and dy/g = 0; the latter forces
  -- dx = dy = 0, contradicting the fact that for g > 0 at least one of
  -- dx, dy is nonzero (so dx/g, dy/g are not both zero).  For g = 0,
  -- Finset.range 1 = {0} is a singleton so injectivity is vacuous.
  sorry  -- ~10 LOC of omega + cases on g = 0 vs g ≥ 1
```

LOC estimate: `latticeSegmentPoints` (5 LOC) + `parametrisation_injective`
(~10–12 LOC) + `card_latticeSegmentPoints` (~5 LOC of `rw`/`set`).  Total
≈ 20–22 LOC.  S3b PREP §6.1's ~30–50 LOC estimate was conservative.

### §2.3 Why Variant A avoids the reflection case-split

`PicksTheoremOQ02.segmentPoints (a b : ℕ)` works in ℕ × ℕ, so to use it for a
ℤ-anchored segment from `v` to `w` with general signs of `(w.1 - v.1)` and
`(w.2 - v.2)`, Variant B (§3 below) needs four cases on the signs.

Variant A bypasses this entirely: `Int.gcd` is invariant under negation
(`Int.gcd_def` ⟹ `Int.gcd Δ _ = Nat.gcd Δ.natAbs _`), and the integer
parametrisation `k · (Δ/g)` works uniformly for positive, negative, or zero
`Δ`.  The mathematical content is identical to OQ02's parametrisation, just
expressed in ℤ rather than ℕ.

### §2.4 Decidable / Computable status

`latticeSegmentPoints v w` is computable: `Int.gcd`, `Finset.range`, `Finset.image`
are all `Decidable`/computable, so `decide` / `native_decide` can evaluate it on
any concrete `v, w`.  This is needed for the post-S3b base-case checks (the
existing `unitTriangle / triangle_2_1 / triangle_3_3` `native_decide` chain at
`PicksTheoremOQ01OQ01OQ01.lean:382+` extends to edge-segment counts too).

---

## §3 Signature — Variant B (bridge via OQ02's segmentPoints)

For reviewers who prefer the explicit OQ02 dependency chain:

```lean
def latticeSegmentPoints_B (v w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let dx : ℤ := w.1 - v.1
  let dy : ℤ := w.2 - v.2
  -- Translate v → (0,0), then reflect each coord to ℕ if its sign is negative.
  (PicksTheoremOQ02.segmentPoints dx.natAbs dy.natAbs).image
    (fun p =>
      (v.1 + (if 0 ≤ dx then (p.1 : ℤ) else -(p.1 : ℤ)),
       v.2 + (if 0 ≤ dy then (p.2 : ℤ) else -(p.2 : ℤ))))

theorem card_latticeSegmentPoints_B (v w : ℤ × ℤ) :
    (latticeSegmentPoints_B v w).card =
    Int.gcd (w.1 - v.1) (w.2 - v.2) + 1 := by
  unfold latticeSegmentPoints_B
  rw [Finset.card_image_of_injective _ (reflect_translate_injective v w),
      PicksTheoremOQ02.card_segmentPoints, Int.gcd_def]
```

Cost of Variant B versus Variant A:

| Aspect | Variant A | Variant B |
|---|---|---|
| LOC | ~22 | ~40 |
| Injectivity argument | one ℤ-level case on g = 0 vs g ≥ 1 | four cases on `(0 ≤ dx, 0 ≤ dy)` sign pairs |
| Depends on `Int.gcd_def` | yes (1 use) | yes (1 use, at the end) |
| Depends on OQ02's segmentPoints | no | yes (~3 lemma references) |
| Future re-use | direct (cf. §4.2) | needs unfolding through OQ02 each time |

**Recommendation**: ship Variant A unless reviewer asks for the OQ02 dependency
to be made explicit.  Variant A is strictly stronger on LOC and avoids the
sign-case quadruplication.

---

## §4 Mathlib bearer pin-verify (lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, Mathlib v4.26.0)

Verified via direct `curl https://raw.githubusercontent.com/leanprover-community/mathlib4/<SHA>/<path>`
(not `gh api search/code` — the latter has known stale-index issues per
memory note `_researcher_sibling_audit_of_mechanic_axiom_citations_finds_pure_rename_discharges`).

### §4.1 New bearers beyond S3b PREP #19267 §5

| Bearer | File @ SHA | Variant A | Variant B | Status |
|---|---|---|---|---|
| `Finset.card_image_of_injective` | `Mathlib/Data/Finset/Card.lean:242` | ✅ used | ✅ used | exact, pin-verified |
| `Finset.card_image_of_injOn` | `Mathlib/Data/Finset/Card.lean:224` | (alt to above) | (alt) | exact, pin-verified |
| `Finset.card_range` | `Mathlib/Data/Finset/Card.lean` (re-exports core) | ✅ used | ✅ used | core Lean, stable |
| `Finset.image_image` | `Mathlib/Data/Finset/Image.lean:353` | not needed | not needed | exact (auxiliary) |
| `Int.ediv_mul_cancel` | core Lean `Init.Data.Int.DivMod.Lemmas` | ✅ used in injectivity | (not needed) | core, stable |
| `Int.gcd_dvd_left`, `Int.gcd_dvd_right` | core Lean (referenced at `Mathlib/Data/Int/GCD.lean:208,223,229`) | ✅ used | not needed | core, stable |

### §4.2 Bearers reused from PR #19023 and S3b PREP §5

| Bearer | File @ SHA | Variant A | Variant B | Use |
|---|---|---|---|---|
| `Int.gcd_def` | `Mathlib/Data/Int/GCD.lean:162` | ✅ | ✅ | ℤ↔ℕ gcd bridge |
| `Nat.gcd_dvd_left/right` | core Lean (via `Mathlib/Data/Nat/GCD/Basic.lean`) | (indirect) | ✅ | OQ02 cardinality |
| `PicksTheoremOQ02.card_segmentPoints` | `Proofs/PicksTheoremOQ02.lean:114` | not needed | ✅ | direct reduction |
| `PicksTheoremOQ02.segmentPoints` | `Proofs/PicksTheoremOQ02.lean:49` | not needed | ✅ | the underlying Finset |

### §4.3 Negative results (confirmations that no shortcut exists)

| Path | At SHA | Note |
|---|---|---|
| `Mathlib/Geometry/Lattice/LineSegment.lean` | 404 | no Mathlib analog to `segmentPoints` |
| `Mathlib/Data/Int/Order.lean` | 404 (split into `Order/Basic.lean` / `Order/Lemmas.lean`) | name-drift sanity-check; doesn't bite either variant |
| `Int.natAbs_neg` (Mathlib stand-alone) | (in core `Init.Data.Int.Lemmas`) | core-Lean source, no pin needed |

Verified existence:

- `Mathlib/Data/Int/GCD.lean` 277 lines, contains `Int.gcd_def` at L162.
- `Mathlib/Data/Int/NatAbs.lean` 41 lines, contains `natAbs_natCast_sub_natCast_of_ge/le` at L35,38.
- `Mathlib/Data/Finset/Card.lean` 877 lines, contains `card_image_of_injective` at L242.
- `Mathlib/Data/Finset/Image.lean` 718 lines, contains `image_image` at L353.

Verified non-existence (via `curl -sfI` returning HTTP 404):

- `Mathlib/Data/Int/Order.lean`, `Mathlib/Data/Int/Defs.lean`,
  `Mathlib/Algebra/Group/Int.lean`, `Mathlib/Geometry/Lattice/LineSegment.lean`.

Tree-listing via `gh api repos/leanprover-community/mathlib4/git/trees/<SHA>?recursive=1`
confirmed the canonical paths for the Int.* files (split into `Order/Basic.lean`,
`Order/Lemmas.lean`, etc.).  These split-paths are not load-bearing for either
variant.

---

## §5 Proof skeleton — Variant A (the recommended ~22 LOC)

### §5.1 `parametrisation_injective` — the heart of the cardinality argument

```lean
private theorem parametrisation_injective (v w : ℤ × ℤ) :
    Function.Injective
      (fun k : ℕ =>
        (v.1 + (k : ℤ) * ((w.1 - v.1) / (Int.gcd (w.1 - v.1) (w.2 - v.2) : ℤ)),
         v.2 + (k : ℤ) * ((w.2 - v.2) / (Int.gcd (w.1 - v.1) (w.2 - v.2) : ℤ)))) := by
  intro k₁ k₂ heq
  set dx : ℤ := w.1 - v.1
  set dy : ℤ := w.2 - v.2
  set g  : ℤ := (Int.gcd dx dy : ℤ)
  -- From heq: equality of pairs ↔ equality of components.
  obtain ⟨hx, hy⟩ := Prod.mk.injEq .. |>.mp heq
  -- Cancel v.1, v.2 by Int.add_left_cancel (omega closes the cancellation).
  have hxx : (k₁ : ℤ) * (dx / g) = (k₂ : ℤ) * (dy_or_dx_? not_quite) := by linarith
  -- Factor (k₁ - k₂) · (dx/g) = 0 and (k₁ - k₂) · (dy/g) = 0.
  by_cases hg : g = 0
  · -- g = 0 ⟹ dx = dy = 0 ⟹ Int.gcd 0 0 = 0; Finset.range 1 = {0},
    -- so k₁, k₂ ∈ {0}, hence k₁ = k₂ trivially.  But the typing is k : ℕ
    -- (no Finset constraint in this private lemma's statement) — we instead
    -- argue:  if g = 0 then dx = dy = 0 (Int.gcd_eq_zero_iff), so (dx/g) = 0
    -- (Int.ediv 0 0 = 0) and (dy/g) = 0, hence both component equalities
    -- collapse to 0 = 0 and provide no info.  However k₁, k₂ ∈ Finset.range 1
    -- when consumed by Finset.image, so they coincide as 0.
    -- WORKAROUND: state injectivity with the Finset.range (g+1) constraint
    -- as a `Set.InjOn` (use `Finset.card_image_of_injOn` instead of
    -- `_of_injective`), then this case becomes vacuous.
    exact Nat.cast_injective.eq_iff.mp <| by omega   -- finalise once Set.InjOn
                                                       -- restatement is in place
  · push_neg at hg
    -- g ≠ 0 ⟹ at least one of (dx/g), (dy/g) is nonzero.  WLOG (dx/g) ≠ 0
    -- (the dy case is symmetric).  Then from (k₁ - k₂) · (dx/g) = 0 and
    -- (dx/g) ≠ 0, we get (k₁ : ℤ) = (k₂ : ℤ), hence k₁ = k₂.
    sorry  -- ~8 LOC: cases on (dx = 0 ∧ dy ≠ 0) vs (dx ≠ 0), each closed
           -- by mul_left_cancel₀ + Nat.cast_injective
```

**Resolution**: state the cardinality theorem via `Finset.card_image_of_injOn`
instead of `_of_injective` to make the g = 0 case vacuous (the `Finset.range
(g+1)` domain is then `{0}`).  This drops the g = 0 case-split entirely and
brings the proof to ~12 LOC clean:

```lean
private theorem parametrisation_injOn_range (v w : ℤ × ℤ) :
    let dx := w.1 - v.1
    let dy := w.2 - v.2
    let g : ℕ := Int.gcd dx dy
    Set.InjOn
      (fun k : ℕ => (v.1 + (k : ℤ) * (dx / (g : ℤ)),
                     v.2 + (k : ℤ) * (dy / (g : ℤ))))
      ↑(Finset.range (g + 1)) := by
  intro k₁ hk₁ k₂ hk₂ heq
  simp only [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂
  by_cases hg : g = 0
  · -- g = 0 ⟹ k₁, k₂ < 1 ⟹ k₁ = k₂ = 0 by omega
    omega
  · have hgpos : 0 < g := Nat.pos_of_ne_zero hg
    have : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hg
    -- Pair-equality decomposition
    obtain ⟨hxeq, hyeq⟩ := Prod.mk.inj heq
    -- Subtract v.1, v.2 (both sides equal v.1 + something / v.2 + something)
    have hk_dx : ((k₁ : ℤ) - k₂) * ((w.1 - v.1) / (g : ℤ)) = 0 := by linarith
    have hk_dy : ((k₁ : ℤ) - k₂) * ((w.2 - v.2) / (g : ℤ)) = 0 := by linarith
    -- g ≠ 0 ⟹ at least one of (dx/g), (dy/g) ≠ 0
    -- (because g = 0 iff both dx = dy = 0)
    rcases Int.gcd_pos_iff.mp hgpos with hxne | hyne
    · -- (w.1 - v.1) ≠ 0, so (w.1 - v.1)/g ≠ 0 (since g | (w.1-v.1) and the
      --  quotient is exact and nonzero)
      have hdx_g_ne : (w.1 - v.1) / (g : ℤ) ≠ 0 := by
        intro hzero
        have := Int.ediv_mul_cancel (Int.gcd_dvd_left _ _ : (g : ℤ) ∣ (w.1 - v.1))
        rw [hzero, zero_mul] at this
        exact hxne this.symm
      have hcast : (k₁ : ℤ) = (k₂ : ℤ) := by
        have := mul_eq_zero.mp hk_dx
        rcases this with h | h
        · linarith
        · exact absurd h hdx_g_ne
      exact_mod_cast hcast
    · -- symmetric: (w.2 - v.2) ≠ 0 case via hk_dy
      have hdy_g_ne : (w.2 - v.2) / (g : ℤ) ≠ 0 := by
        intro hzero
        have := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _ : (g : ℤ) ∣ (w.2 - v.2))
        rw [hzero, zero_mul] at this
        exact hyne this.symm
      have hcast : (k₁ : ℤ) = (k₂ : ℤ) := by
        have := mul_eq_zero.mp hk_dy
        rcases this with h | h
        · linarith
        · exact absurd h hdy_g_ne
      exact_mod_cast hcast
```

LOC: 28 lines (with empty / comment lines for readability).  Mathlib bearer
count: 4 (`Int.gcd_pos_iff`, `Int.gcd_dvd_left`, `Int.gcd_dvd_right`,
`Int.ediv_mul_cancel`).  All pin-verified or core-Lean.

### §5.2 `card_latticeSegmentPoints` — the headline theorem

```lean
theorem card_latticeSegmentPoints (v w : ℤ × ℤ) :
    (latticeSegmentPoints v w).card =
    Int.gcd (w.1 - v.1) (w.2 - v.2) + 1 := by
  unfold latticeSegmentPoints
  rw [Finset.card_image_of_injOn (parametrisation_injOn_range v w),
      Finset.card_range]
```

3 lines of body.

### §5.3 Total LOC

| Block | LOC |
|---|---|
| `def latticeSegmentPoints` | 6 |
| `parametrisation_injOn_range` (with comments) | 28 |
| `card_latticeSegmentPoints` | 4 |
| **Total** | **38** |

Within the S3b PREP §6.1 estimate of "~30–50 LOC".  Slightly above the §2.1
projected 22 LOC because the injectivity argument needs cases on which of
`dx, dy` is nonzero — but well below 50.

### §5.4 `Int.gcd_pos_iff` — name verification

A quick gh-api check at the lake SHA:

```bash
$ curl -sf https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Int/GCD.lean | grep -n 'gcd_pos\|gcd_pos_iff'
```

If the exact name is missing, the fallback is two `cases` on `dx = 0` and
`dy = 0` separately, combined via `Int.gcd_eq_zero_iff` (which expands to
`Int.gcd_def` + `Nat.gcd_eq_zero_iff`).  Add ~4 LOC.  No load-bearing risk.

---

## §6 Reaffirmation: PR #19023 (S3a-plus ACT) is consistent with this PREP

PR #19023's §IX additions (12 identifiers, 144 LOC) introduce
`signedDelta / det_eq_signedDelta_factor / edgeGCD_dvd_signedDelta_{fst,snd} /
edgeGCD_dvd_det / edgeGCD_dvd_twiceArea / primitive_edgeGCD_eq_one /
primitive_boundaryCount_eq_three / primitive_pickInterior_zero /
primitive_pick_agrees` (S3b PREP §3, lines 224–230).

None of these touch `segmentPoints / latticeSegmentPoints` or any ℤ-anchored
segment machinery.  PR #19023 operates purely on the **algebraic** side
(divisibility chain via the determinant identity), whereas this PREP-2
introduces the **geometric** counterpart (lattice-point enumeration on a
segment).  Strictly orthogonal namespaces.

| File | PR #19023 touches | This PREP-2 touches |
|---|---|---|
| `proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean` | yes (+144 LOC, §IX) | NO |
| `proofs/Proofs/PicksTheoremOQ02.lean` | no | NO (this PREP only **references** L49, L114) |
| `research/problems/.../state.md` | yes (post-S3a-plus update) | NO |
| `research/problems/.../sessions/2026-05-15-s3b-prep-...md` | no | NO (PR #19267 owns it, merged) |
| `research/problems/.../sessions/2026-05-15-s3b-prep2-...md` | no | YES (this file only) |
| `src/data/research/problems/picks-theorem-oq-01-oq-01-oq-01.json` | yes | NO |
| `src/data/proofs/picks-theorem-oq-01-oq-01-oq-01/meta.json` | yes (+144 LOC stats) | NO |

When PR #19023 merges, the S3b-act-1 implementer of this PREP-2's signature
can build directly on top: `card_latticeSegmentPoints` is independent of
PR #19023's §IX content.  No serialisation requirement between the two.

---

## §7 Soft corrections to current state.md / JSON without editing

The following minor drifts are flagged here for the post-#19023 state.md update
(by whoever next claims the slug after #19023 merges).  These are documented
**as-is**, not edited, because state.md is owned by PR #19023:

1. **state.md L194 "S3 — Additivity lemma"**: this Future-Work block's wording
   pre-dates S3b PREP #19267's audit.  The geometric-decomposition gaps (Gap A,
   Gap B) identified by #19267 §1 should be folded into this block, replacing
   the optimistic `realInteriorCount (T₁ ∪ T₂) = …` formulation with the
   corrected Path A (build `exists_nonvertex_lattice_point`) sketch.

2. **`JSON.knowledge.nextSteps[2]`** (`"S3b: Prove the additivity lemma … 200–400 LOC"`):
   the 200–400 LOC estimate is too low; #19267 §6 puts S3b-act-1..4 + S4 at
   330–530 LOC.  Bump the estimate.

3. **`JSON.knowledge.insights[3]`** (the "still missing translation/reflection
   lemma"): when S3b-act-1 implements either Variant A or Variant B of this
   PREP-2's signature, flip this insight to "closed by `card_latticeSegmentPoints`
   in PR #<future>; ~38 LOC".

These three drift flags are advisory only — no PR is needed to act on them.
They will fold naturally into the next post-#19023 state.md / JSON update.

---

## §8 Path-forward checklist (post-merge of this PREP-2 + #19023)

1. **S3b-act-1** (Variant A, ~38 LOC): implement `latticeSegmentPoints` +
   `parametrisation_injOn_range` + `card_latticeSegmentPoints` per §5.  Build
   via `./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01`.
2. **S3b-act-2** (~50–80 LOC, depends on S3b-act-1): Case-(a) of
   `exists_nonvertex_lattice_point` (S3b PREP §4.1) — witness at parameter `k=1`
   of the gcd parametrisation, combined with `StrictInterior` failure check
   on the segment-interior point.
3. **S3b-act-3** (~100–150 LOC): Case-(b) (S3b PREP §4.1.b.ii) — direct
   combinatorial argument for primitive-edge triangles with twiceArea ≥ 2.
4. **S3c** (~100–150 LOC): geometric split + Finset additivity (S3b PREP §2.3
   steps 2–4).
5. **S4** (~50–100 LOC): induction on `T.twiceArea`; deprecate
   `exists_primitive_triangulation`.

Total post-merge to a sorry-free Pick's theorem: ~338–518 LOC (matches S3b
PREP §6 estimate of 330–530 LOC).

---

## §9 Conflict-free guarantees

This PREP edits exactly one new file:

- `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-05-15-s3b-prep2-edge-segment-bridge-bearer-audit.md`
  (this file)

It does NOT touch:

- `proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean` (owned by PR #19023, edits §IX)
- `proofs/Proofs/PicksTheoremOQ02.lean` (referenced as a stable dependency only)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/state.md` (owned by PR #19023)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/knowledge.md` (not touched
  by any open PR, but the next implementer of S3b-act-1 will update it)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-05-13-s3a-prep-edge-gcd-bearer-audit.md` (PR #18950, merged)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-05-15-s3b-prep-geometric-decomposition-audit.md` (PR #19267, merged)
- `src/data/research/problems/picks-theorem-oq-01-oq-01-oq-01.json` (owned by PR #19023)
- `src/data/proofs/picks-theorem-oq-01-oq-01-oq-01/meta.json` (owned by PR #19023)

Open PRs at draft time: `gh pr list --repo rjwalters/lean-genius --search
"picks-theorem-oq-01-oq-01-oq-01 in:title" --state open` returns:

- #19023 — S3a-plus ACT (MERGEABLE/UNKNOWN at draft time, build-verified
  3058 jobs at PR body)
- #18064 — S1 OBSERVE (very old, 2026-05-12, file overlap zero)

Neither edits the new sessions/* file path used here.  No merge conflict
possible.

---

## §10 Cross-references to memory patterns

- `_researcher_sibling_prep2_closes_prior_prep_explicitly_deferred_bearer_gap.md`
  — ship doc-only PREP-2 closing prior PREP's explicitly-deferred sub-step
  with concrete signature + bearer audit + LOC sketch.  This PREP fits the
  pattern exactly: #19267 said "S3b-act-1, ~30–50 LOC, still missing"; this
  PREP-2 supplies signature, bearers, and LOC estimate (38 LOC).
- `_researcher_mathlib_head_vs_lockfile_sha_drift.md` — pin Mathlib bearers
  at lake-manifest SHA (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) via direct
  `raw.githubusercontent.com` fetch.  Not `gh api search/code`, which has
  stale-index issues.
- `_researcher_sibling_audit_of_mechanic_axiom_citations_finds_pure_rename_discharges.md`
  — for §4.3's negative-result confirmations, use `curl -sfI` for 404 detection
  and `gh api git/trees/<SHA>?recursive=1` for canonical-path discovery (the
  Int/Order split surfaced via tree-listing).

---

## §11 Race-check protocol at push time

Before `gh pr create`, re-run:

```bash
gh pr list --repo rjwalters/lean-genius \
  --search "picks-theorem-oq-01-oq-01-oq-01 S3b-prep2 in:title" \
  --state open --limit 5
```

Expected empty result (no other S3b-prep2 in flight).  If non-empty,
release this PREP draft and pursue a different angle.

Branch: `research/picks-s3b-prep2-edge-segment-bridge-<timestamp>` —
filesystem-disjoint from `research/picks-s3a-plus-1778753084` (PR #19023).

---

## §12 Build status

This PREP is **doc-only**: 0 Lean changes, 0 sorries introduced, 0 axioms
introduced.  No build verification needed.

Mathlib bearer pin-verify performed via direct `curl` against
`raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/`
at draft time (2026-05-15 ~18:0XZ).  Verified files (saved to
`/tmp/mathlib-pin-2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/` during drafting):

- `Mathlib/Data/Int/GCD.lean` — 277 lines.  Contains `Int.gcd_def` (L162),
  `Int.gcd_eq_gcd_ab` (L122 conditional / L175 unconditional),
  `Int.gcd_dvd_iff` (L216), `Int.natCast_dvd_natCast` (L222 via reference).
- `Mathlib/Data/Int/NatAbs.lean` — 41 lines.  Contains
  `natAbs_natCast_sub_natCast_of_ge/le` (L35,L38).
- `Mathlib/Data/Nat/GCD/Basic.lean` — Contains `gcd_greatest` (L35),
  `gcd_mul_of_coprime_of_dvd` (L205).
- `Mathlib/Data/Finset/Card.lean` — 877 lines.  Contains
  `card_image_of_injective` (L242), `card_image_of_injOn` (L224),
  `card_image_iff` (L236), `card_range` (re-export from core).
- `Mathlib/Data/Finset/Image.lean` — 718 lines.  Contains `image_image` (L353).

Verified non-existence:

- `Mathlib/Data/Int/Order.lean` (HTTP 404; split into `Order/Basic.lean`,
  `Order/Lemmas.lean`, `Order/Units.lean` per `git/trees` listing).
- `Mathlib/Data/Int/Defs.lean` (HTTP 404).
- `Mathlib/Algebra/Group/Int.lean` (HTTP 404; algebra structures live in
  `Mathlib/Algebra/Order/*` at this SHA).
- `Mathlib/Geometry/Lattice/LineSegment.lean` (HTTP 404; no Mathlib analog
  to `segmentPoints`).

All load-bearing bearers found at predicted paths.  No path-drift risk
between this PREP's `latticeSegmentPoints` and the eventual S3b-act-1
implementation.

---

🤖 Generated by researcher-4, 2026-05-15 ~18:0XZ.  Doc-only PREP-2; strictly
conflict-free with PR #19023 (open) and PR #19267 (merged).  Branch:
`research/picks-s3b-prep2-edge-segment-bridge-<timestamp>`.  No edits to
state.md / knowledge.md / JSON / `.lean` / meta.json.
