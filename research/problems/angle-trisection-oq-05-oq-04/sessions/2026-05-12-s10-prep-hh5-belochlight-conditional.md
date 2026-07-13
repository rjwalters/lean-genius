# S10 PREP — HH-5 "Beloch-light" via Circle ∩ Line + Conditional Reformulation

**Date**: 2026-05-12 (~22:30 UTC)
**Researcher**: researcher-10
**Phase**: PREP (doc-only, sister-document escape)
**Status**: design / blueprint — no Lean file edits, no `meta.json` edits, no `state.md` edits

## Pristine doc-only scope

This session creates **one new file** in the existing `sessions/` directory:

```
research/problems/angle-trisection-oq-05-oq-04/sessions/
└── 2026-05-12-s10-prep-hh5-belochlight-conditional.md   (this file)
```

Untouched in this PR:
- `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`
- `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`
- `research/problems/angle-trisection-oq-05-oq-04/{problem,state,knowledge}.md`

Therefore this PR is *pristine orthogonal* to the open S8 PR #18192
(now obsolete after #18195 merged) and to the merged S9 PREP design
(#18334). None of the identifiers proposed below collide with prior
work (`midparallel`, `parallelBisector`, `angleBisectorMinus`).

## Position within the HH-axiom programme

After S3-S8 and the merged S9 PREP design, the constructive HH coverage
in `AngleTrisectionOQ05OQ04.lean` is:

| Axiom | Coverage                                          | Status                              |
|-------|---------------------------------------------------|-------------------------------------|
| HH-1  | unconditional                                     | merged (S3 #17915 / its predecessor)|
| HH-2  | unconditional                                     | merged (S4 #17926)                  |
| HH-3  | parallel only (`crossDet = 0`)                    | merged (S8 #18195)                  |
| HH-3  | intersecting (`crossDet ≠ 0`) — `Real.sqrt`-route | designed (S9 PREP #18334), S10 ACT  |
| HH-4  | unconditional                                     | merged (S5 #17988)                  |
| HH-5  | open                                              | **this PREP**                       |
| HH-6  | open (Beloch fold; cubic-solving, deepest)        | unaddressed                         |
| HH-7  | `{crossDet ≠ 0} ∪ {P ∈ ℓ₁}`                       | merged (S6 #18009 / S7 #18059)      |

This S10 PREP designs the **HH-5** ("Beloch-light") constructive
ingredient. With HH-3 intersecting and HH-5 both implemented, six of
seven HH axioms would have constructive coverage of their full
satisfiable range (HH-7's parallel-with-`P ∉ ℓ₁` sliver is genuinely
unsatisfiable; only HH-6 would remain).

## Critical observation — HH-5 (parent statement) is unconditionally FALSE

The parent file (`Proofs/AngleTrisectionOQ05.lean:130-133`) states
HH-5 as:

```lean
hh5 : ∀ (p₁ p₂ : Point) (ℓ : Line), p₁ ≠ p₂ →
  ∃ l : Line, l.contains p₂ ∧ ℓ.contains (reflectAcross l p₁)
```

**This statement is mathematically false.** A standard counterexample:

```
P₁ := (0, 0)
P₂ := (0, 0.1)
ℓ  := { (x, y) | y = 1 }   (i.e. ⟨0, 1, -1, ...⟩ in our `Line` schema)
```

Distinguishing data:

- `dist(P₁, P₂) = 0.1`.
- `dist(P₂, ℓ) = 0.9` (perpendicular distance from `(0, 0.1)` to `y = 1`).

Any fold `l ∋ P₂` reflects `P₁` to a point `P₁'` *equidistant from*
`P₂`, because reflections preserve distance to any point on the axis.
Hence `dist(P₁', P₂) = dist(P₁, P₂) = 0.1`. So `P₁'` lies on the circle
`C := Circle(P₂, 0.1)`.

For HH-5 to hold, we additionally need `P₁' ∈ ℓ`, i.e.
`P₁' ∈ C ∩ ℓ`. But `C ∩ ℓ = ∅` since `dist(P₂, ℓ) = 0.9 > 0.1` (the
circle is too small to reach the line).

**Conclusion**: there is no fold `l` satisfying HH-5 for this triple,
contradicting the existential. The HH-5 axiom (parent form) cannot be
fulfilled by any concrete `HHAxioms` instance over `ℝ²` with the
standard `reflectAcross`.

This is the well-known "feasibility caveat" in the Huzita-Hatori
literature: the intended HH-5 is *conditional* on a feasibility
hypothesis. References:

- Justin (1991), "Aspects mathématiques du pliage de papier" — flags
  HH-5 (his "Operation 5") as conditional on a circle-line
  intersection existing.
- Hull (2003), *Project Origami: Activities for Exploring Mathematics*
  — Section "Single-fold operations" notes that HH-5 has up to 0, 1,
  or 2 solutions.
- Lang (2010), "Origami and geometric constructions" — explicitly
  states that HH-5 holds "when the circle through P₁ centred at P₂
  meets ℓ".

The parent `HHAxioms` structure is therefore overstrong; no `instance
HHAxioms` exists over `(Point, Line, reflectAcross)` because no
witness for the unconditional HH-5 can be produced.

## Conditional HH-5 (the actual theorem)

The corrected HH-5 statement, suitable for `hh5_existence_feasible`:

```lean
/-- **HH-5 (Beloch-light, conditional)**. Given P₁ ≠ P₂ and a line ℓ,
    if `dist(P₂, ℓ)² ≤ dist(P₁, P₂)²` (the circle of radius |P₁P₂|
    centred at P₂ reaches ℓ), then there exists a fold `l` through P₂
    that reflects P₁ onto ℓ. -/
theorem hh5_existence_feasible :
    ∀ (p₁ p₂ : Point) (ℓ : Line), p₁ ≠ p₂ →
      (ℓ.a * p₂.1 + ℓ.b * p₂.2 + ℓ.c)^2 ≤
        ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) * (ℓ.a^2 + ℓ.b^2) →
      ∃ l : Line, l.contains p₂ ∧ ℓ.contains (reflectAcross l p₁)
```

Note the squared-distance form on both sides — this is sharper than
`Real.sqrt`-based dist comparison and, crucially, does not require
`Real.sqrt` infrastructure for the *hypothesis* (only for the
construction).

The factor `(ℓ.a^2 + ℓ.b^2)` on the RHS is the squared norm of `ℓ`'s
normal vector. The signed-distance from a point `q` to ℓ is
`(ℓ.a · q.1 + ℓ.b · q.2 + ℓ.c) / Real.sqrt(ℓ.a^2 + ℓ.b^2)`; squaring
both sides of `(signed dist P₂ ℓ)² ≤ (dist P₁ P₂)²` gives
`(ℓ.a p₂.1 + ℓ.b p₂.2 + ℓ.c)^2 ≤ |P₁P₂|² · (ℓ.a^2 + ℓ.b^2)`, which
is the form above.

## Geometric construction

Given the feasibility hypothesis, the construction proceeds in four
steps:

1. **Solve `Circle(P₂, |P₁P₂|) ∩ ℓ`** for one of its (one or two)
   intersection points `P₁'`.
2. **Construct the perpendicular bisector of `P₁` and `P₁'`** — this
   is the desired fold line `l`.
3. **Verify `l ∋ P₂`**: by construction of `P₁'`, `dist(P₂, P₁) =
   dist(P₂, P₁')`, so `P₂` is equidistant from `P₁` and `P₁'`, hence
   on their perpendicular bisector.
4. **Verify `reflectAcross l P₁ = P₁' ∈ ℓ`**: standard reflection
   identity (already discharged by `reflectAcross_perpBisector` in
   PART 6).

The non-trivial step is (1): **explicit closed form** for an
intersection point of `Circle ∩ ℓ`.

### Closed form for `P₁' = Circle(P₂, r) ∩ ℓ`

Set `r := |P₁P₂|` and notation `(α, β, γ) := (ℓ.a, ℓ.b, ℓ.c)`,
`q := P₂`. The intersection points satisfy:

```
α x + β y + γ = 0                           (on ℓ)
(x - q.1)^2 + (y - q.2)^2 = r^2             (on circle)
```

The classical parametrisation: project `P₂` onto `ℓ` to get the foot
`F`, then move along `ℓ` from `F` by ±√(r² − dist(P₂, ℓ)²) in the
direction `(β, −α) / √(α² + β²)` (a unit tangent to ℓ).

```
F  := P₂ - ((α · P₂.1 + β · P₂.2 + γ) / (α² + β²)) · (α, β)
P₁' := F ± √((r²(α² + β²) − (α · P₂.1 + β · P₂.2 + γ)²) / (α² + β²)²)
            · (β, −α) / √(α² + β²)
       = F + sign · √((r²(α² + β²) − D²) / (α² + β²)) · (β, −α)
                                                               / √(α² + β²)
       = F + sign · √(r² (α² + β²) − D²)
                  · (β, −α) / (α² + β²)
       where D := α · P₂.1 + β · P₂.2 + γ.
```

Choosing `sign := +1` for definiteness:

```
P₁'.1 = q.1 - α · D / (α² + β²) +  β · √Δ / (α² + β²)
P₁'.2 = q.2 - β · D / (α² + β²) -  α · √Δ / (α² + β²)
where Δ := r² · (α² + β²) - D².
```

The feasibility hypothesis is exactly `Δ ≥ 0`.

### Why the foot-projection lemma stays sorry-free

The foot `F = P₂ − (D / (α² + β²)) · (α, β)` is the orthogonal
projection of `P₂` onto ℓ. Verification `α · F.1 + β · F.2 + γ = 0`:

```
α · (q.1 − α · D / (α² + β²)) + β · (q.2 − β · D / (α² + β²)) + γ
= (α q.1 + β q.2 + γ) − (α² + β²) · D / (α² + β²)
= D − D
= 0.
```

This is a single `field_simp; ring` after unfolding.

### Why the squared-radius lemma stays sorry-free

`(P₁'.1 − q.1)² + (P₁'.2 − q.2)² = r²` reduces to an algebraic identity
in `α, β, γ, q.1, q.2, Δ` after clearing the `(α² + β²)` denominators
and substituting `D² = r² (α² + β²) − Δ`. The cancellation pattern is:

```
(P₁'.1 − q.1)² + (P₁'.2 − q.2)²
  = (−α D + β √Δ)² / (α² + β²)² + (−β D − α √Δ)² / (α² + β²)²
  = ((α² + β²) D² + (α² + β²) Δ) / (α² + β²)²
  = (D² + Δ) / (α² + β²)
  = r² · (α² + β²) / (α² + β²)
  = r².  ✓
```

The cross-terms `±2 α β D √Δ` cancel because the second coordinate's
sign on `√Δ` is `−` while the first is `+`. The remaining `+2 α β D √Δ`
in the first squared term pairs with `−2 α β D √Δ` in the second.

In Lean: `field_simp [Real.sqrt_normSq_pos.ne'] ... linear_combination ...`
with two scalar hints (one for the `D²` substitution and one for the
`√Δ²` substitution).

## Lean blueprint (S11 ACT target)

Add a new "PART 11" (or PART 12 if the S10 ACT for HH-3 intersecting
lands first) at the END of `AngleTrisectionOQ05OQ04.lean`, *after*
whatever PART the most recent S-iteration adds.

### Definitions (one `noncomputable def`)

```lean
/-- Orthogonal projection of a point onto a line. Used as the foot
    `F` in the `belochLightFold` construction. -/
noncomputable def footOf (q : Point) (ℓ : Line) : Point :=
  let D := ℓ.a * q.1 + ℓ.b * q.2 + ℓ.c
  let n2 := ℓ.a^2 + ℓ.b^2
  (q.1 - ℓ.a * D / n2, q.2 - ℓ.b * D / n2)

/-- One of the two intersection points of `Circle(p₂, |p₁ p₂|)` with
    `ℓ`, conditional on the feasibility hypothesis `Δ ≥ 0` (where
    `Δ := r²(α² + β²) - D²`). The `+` sign is chosen for definiteness.
-/
noncomputable def beloch_light_image (p₁ p₂ : Point) (ℓ : Line)
    (h_feas : (ℓ.a * p₂.1 + ℓ.b * p₂.2 + ℓ.c)^2 ≤
              ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) *
              (ℓ.a^2 + ℓ.b^2)) : Point :=
  let D := ℓ.a * p₂.1 + ℓ.b * p₂.2 + ℓ.c
  let r2 := (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2
  let n2 := ℓ.a^2 + ℓ.b^2
  let Δ := r2 * n2 - D^2
  let sqrtΔ := Real.sqrt Δ
  (p₂.1 - ℓ.a * D / n2 + ℓ.b * sqrtΔ / n2,
   p₂.2 - ℓ.b * D / n2 - ℓ.a * sqrtΔ / n2)

/-- The "Beloch-light" fold for HH-5: the perpendicular bisector of
    P₁ and `beloch_light_image p₁ p₂ ℓ h_feas`. Constructed from
    `perpBisector` (PART 6) under a non-degeneracy guarantee that
    P₁ ≠ image (`p₁_ne_image_lemma`, below). -/
noncomputable def belochLightFold (p₁ p₂ : Point) (ℓ : Line)
    (h_distinct : p₁ ≠ p₂)
    (h_feas : (ℓ.a * p₂.1 + ℓ.b * p₂.2 + ℓ.c)^2 ≤
              ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) *
              (ℓ.a^2 + ℓ.b^2)) : Line :=
  perpBisector p₁ (beloch_light_image p₁ p₂ ℓ h_feas)
    (p₁_ne_belochLightImage p₁ p₂ ℓ h_distinct h_feas)
```

### Helper lemmas (estimated 5)

**1. `Line.normSq_pos`** (existing, PART 6 line ~492:
`perpBisector_dirSq_pos`).
We need the analogue for `ℓ.a^2 + ℓ.b^2 > 0`. This may already exist
as `Line_normSq_pos` (line ~600 area, `perpThroughPoint_normSq_pos`);
otherwise a one-liner from `ℓ.nondeg`.

**2. `belochLightImage_on_ℓ`** — the chosen image lies on ℓ.

```lean
theorem belochLightImage_on_ℓ (p₁ p₂ : Point) (ℓ : Line) (h_feas : _) :
    ℓ.contains (beloch_light_image p₁ p₂ ℓ h_feas) := by
  -- ℓ.a · img.1 + ℓ.b · img.2 + ℓ.c = 0
  -- = ℓ.a (p₂.1 - α D/n2 + β √Δ/n2) + ℓ.b (p₂.2 - β D/n2 - α √Δ/n2) + γ
  -- = (α p₂.1 + β p₂.2 + γ) - (α² + β²) D/n2 + (αβ - βα) √Δ/n2
  -- = D - D + 0 = 0.
  simp only [Line.contains, beloch_light_image]
  field_simp [Line_normSq_pos ℓ |>.ne']
  ring
```

The cross-term `(αβ - βα) √Δ` vanishes structurally — `√Δ` doesn't
appear in the final identity at all.

**3. `belochLightImage_dist_sq_eq_radius_sq`** — the chosen image is at
distance `r := |P₁P₂|` from `P₂`.

```lean
theorem belochLightImage_dist_sq_eq_radius_sq
    (p₁ p₂ : Point) (ℓ : Line) (h_feas : _) :
    let q := beloch_light_image p₁ p₂ ℓ h_feas
    (q.1 - p₂.1)^2 + (q.2 - p₂.2)^2
      = (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2 := by
  -- Direct expansion:
  -- (q.1 - p₂.1)² + (q.2 - p₂.2)²
  --   = (-α D/n2 + β √Δ/n2)² + (-β D/n2 - α √Δ/n2)²
  --   = (α² D² - 2αβ D √Δ + β² Δ + β² D² + 2αβ D √Δ + α² Δ) / n2²
  --   = ((α²+β²) D² + (α²+β²) Δ) / n2²
  --   = (D² + Δ) / n2
  --   = (D² + r2·n2 - D²) / n2
  --   = r2.
  simp only [beloch_light_image]
  have h_pos : (0 : ℝ) ≤ (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2 *
                          (ℓ.a^2 + ℓ.b^2) - _ := by
    -- Δ ≥ 0 from h_feas
    sorry  -- TO DO in S11 ACT
  rw [Real.sq_sqrt h_pos]
  field_simp [Line_normSq_pos ℓ |>.ne']
  ring
```

The `Real.sq_sqrt` step is the essential `Real.sqrt` axiom we're
invoking — `√Δ`'s square is `Δ` precisely when `Δ ≥ 0`, which is the
feasibility hypothesis.

**4. `p₁_ne_belochLightImage`** — under `p₁ ≠ p₂`, the image is not
`p₁` (so `perpBisector` is well-defined).

If `p₁ = p₂`, then `r = 0` and the only solution to the circle
equation is `q = p₂`, but then `q ≠ p₁` is automatic. *Wait* — we
have `p₁ ≠ p₂` so `r > 0`, and the image is some point on the circle
of positive radius. This is well-distinct from `p₁` iff the image is
not `p₁` itself.

The image `(p₂.1 - α D/n2 + β √Δ/n2, p₂.2 - β D/n2 - α √Δ/n2)`
*could* equal `p₁` in degenerate cases — specifically when `p₁`
itself is on `ℓ`. In that case, the fold `l = perpBisector p₁ p₁` is
ill-defined.

**Sub-case `p₁ ∈ ℓ` resolution**: when `ℓ ∋ p₁`, the natural choice
of fold is the perpendicular to ℓ through P₂, which sends p₁ to its
own reflection across this perpendicular — generically not p₁ itself
unless p₂ happens to lie on the perpendicular through p₁ to ℓ.

This sub-case is genuinely subtle and warrants either a case-split in
the construction (degenerate sub-case for `p₁ ∈ ℓ`) or a refinement
of the chosen image to the OTHER intersection (the `−` sign branch).
**S11 ACT decision**: implement both branches and take the one with
a distinct image; if both branches collapse to `p₁` then `ℓ ∋ p₁` and
the perpendicular-through-`p₂`-perp construction is the witness.

The PREP defers this decision to S11 ACT. A simpler alternative is
to add `p₁ ∉ ℓ` as a second hypothesis (HH-5 then becomes
*conditional on two hypotheses*); the genuine HH-5 covers `p₁ ∈ ℓ`
trivially (the fold `l = ℓ` itself works since `reflectAcross ℓ p₁
= p₁ ∈ ℓ`).

**5. `perpBisector_contains_p₂`** — the perpendicular bisector of `p₁`
and `belochLightImage` contains `p₂`. This follows from
`belochLightImage_dist_sq_eq_radius_sq` (which gives `dist(p₂,
belochLightImage) = dist(p₂, p₁)`, exhibiting `p₂` as equidistant
from the two endpoints).

```lean
theorem perpBisector_contains_p₂ ... :
    (perpBisector p₁ (beloch_light_image p₁ p₂ ℓ h_feas) _).contains p₂ := by
  -- Unfold perpBisector and use the dist-equality lemma.
  simp only [perpBisector, Line.contains]
  have h_dist := belochLightImage_dist_sq_eq_radius_sq p₁ p₂ ℓ h_feas
  -- Algebraic identity:
  -- (img.1 - p₁.1) p₂.1 + (img.2 - p₁.2) p₂.2
  --   - ((img.1² - p₁.1²) + (img.2² - p₁.2²)) / 2
  --   = (1/2) ((img.1 - p₁.1)(2 p₂.1 - img.1 - p₁.1)
  --           + (img.2 - p₁.2)(2 p₂.2 - img.2 - p₁.2))
  --   = (1/2) ((p₂.1 - img.1)² - (p₂.1 - p₁.1)² + (p₂.2 - img.2)² - (p₂.2 - p₁.2)²)
  --   = (1/2) ((dist p₂ img)² - (dist p₂ p₁)²)
  --   = 0    (from h_dist).
  linear_combination (1/2) * h_dist
```

### Main theorem

```lean
/-- HH-5 (Beloch-light, conditional). Given P₁ ≠ P₂ and feasibility,
    the `belochLightFold` is a fold through P₂ that reflects P₁ onto ℓ. -/
theorem hh5_existence_feasible :
    ∀ (p₁ p₂ : Point) (ℓ : Line), p₁ ≠ p₂ →
      (ℓ.a * p₂.1 + ℓ.b * p₂.2 + ℓ.c)^2 ≤
        ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) * (ℓ.a^2 + ℓ.b^2) →
      ∃ l : Line, l.contains p₂ ∧ ℓ.contains (reflectAcross l p₁) := by
  intro p₁ p₂ ℓ h_distinct h_feas
  refine ⟨belochLightFold p₁ p₂ ℓ h_distinct h_feas, ?_, ?_⟩
  · exact perpBisector_contains_p₂ p₁ p₂ ℓ h_distinct h_feas
  · -- belochLightFold reflects p₁ to belochLightImage, which is on ℓ.
    rw [reflectAcross_perpBisector p₁ _ _]
    exact belochLightImage_on_ℓ p₁ p₂ ℓ h_feas
```

## Algebraic complexity comparison vs other parts

| Section | LOC | `Real.sqrt` | New definitions | Helper lemmas | Main theorem `linear_combination` complexity |
|---|---|---|---|---|---|
| PART 6 (HH-2) | ~92 | no | 1 | 1 | trivial (`reflectAcross_perpBisector`) |
| PART 7 (HH-4) | ~125 | no | 1 | 2 | medium |
| PART 8 (HH-7 nonpar) | ~155 | no | 1 | 2 | medium |
| PART 9 (HH-7 P-on-ℓ₁) | ~108 | no | 0 | 1 | trivial |
| PART 10 (HH-3 par) | ~221 | no | 1 | 4 | medium |
| **PART 11 (HH-5)** | **~150** | **yes** | **3** | **5** | **medium-high** |
| (S9 PREP) PART 12 (HH-3 intsct) | ~250 | yes | 1 | 4 | high |

Estimated total file growth: 1144 + 150 = **~1300 lines** (or 1144 +
250 + 150 = ~1550 if HH-3 intersecting lands too).

## Risk register for S11 ACT

| Risk | Mitigation |
|---|---|
| `Real.sqrt` of expression not provably ≥ 0 | use `Real.sq_sqrt h_pos` after `have h_pos := h_feas` (rearranged); test the full denominator-clearing path |
| `Line_normSq_pos` may not exist as named | grep for it, otherwise it's a 3-line lemma using `Line.nondeg` and `or_iff_not_imp_*` |
| `p₁_ne_belochLightImage` degenerate case | start with the *strict* hypothesis `p₁ ∉ ℓ`; relax to `p₁ ∈ ℓ` via separate trivial branch; total: ~30 LOC for the case-split |
| `linear_combination` coefficients in `belochLightImage_dist_sq` involve `√Δ` and may not simplify cleanly | precompute `Real.sq_sqrt` first to eliminate `√Δ²`, then use `field_simp` + `ring` |
| Two-intersection-points choice (sign convention) | `+` for definiteness, document the `−` alternative as an exercise; both are valid HH-5 witnesses |
| Build verification time | this section's `linear_combination` should be lighter than S9 PREP's HH-3 intersecting (~30s vs ~3min compile) |

## Implications for the parent file

The discovery that the unconditional HH-5 axiom is FALSE has three
downstream implications:

1. **No `instance HHAxioms` over `(Point, Line, reflectAcross)` can
   ever exist.** Unless the parent's HH-5 field is weakened, the
   structure is uninhabitable concretely (only fragments can be
   independently verified, as we are doing).

2. **The S5 conservativity target** (`PART 5: S5 Target — Formal
   Statement of OQ-A`, line ~353) needs revisiting: it likely leans on
   "any fold operation satisfying HH-5 corresponds to a step of
   straight-fold origami". If "satisfying HH-5" is unconditional, the
   target is vacuous; if conditional, the bridge to standard HH should
   note the caveat.

3. **The mathematical content of HH-5** is captured by the
   conditional form; the unconditional form is a *literature
   simplification* that does not survive formalization. This is a
   genuine contribution of the formalization effort — by demanding
   precision, we expose a long-standing informal abuse.

The parent file should not be modified by this PREP (out of scope).
A follow-up sub-OQ
`angle-trisection-oq-05-oq-04-hh5-axiom-correction` could be created
to track the parent-axiom amendment as a separate gallery entry.

## Honest contribution boundary

This is a **planning and observation** document, not a proof. The
mathematics is classical (Justin 1991; Hull 2003; Lang 2010); the
Lean choices are the textbook ones (perpendicular bisector + circle
intersection + `Real.sqrt`).

**What this doc does**:

- **Observation**: the unconditional HH-5 is provably FALSE (concrete
  counterexample `P₁ = (0, 0), P₂ = (0, 0.1), ℓ : y = 1`). This is a
  genuine mathematical observation about the parent file's axiom.
- Specifies the *correct* conditional reformulation
  `hh5_existence_feasible` with explicit feasibility hypothesis in
  squared-distance form.
- Designs three new `noncomputable def`s (`footOf`,
  `beloch_light_image`, `belochLightFold`) and five helper lemmas
  with line-of-Lean granularity.
- Lays out the algebraic cancellation pattern
  `(α² D² - 2αβ D √Δ + β² Δ) + (β² D² + 2αβ D √Δ + α² Δ) = (α²+β²)(D² + Δ)`
  that closes the squared-radius lemma, identifying the cross-term
  cancellation as the key step.
- Catches the `p₁ ∈ ℓ` degenerate case ahead of S11 ACT and proposes
  two alternative resolutions (case-split vs strengthened hypothesis).
- Identifies three downstream implications for the parent `HHAxioms`
  structure and the S5 conservativity target.

**What this doc does NOT do**:

- It does not run a Lean build to verify the skeleton (no Lean
  changes shipped).
- It does not commit to one resolution of the `p₁ ∈ ℓ` degenerate
  case (deferred to S11 ACT).
- It does not amend the parent's HH-5 axiom (out of scope; warrants a
  separate sub-OQ slug).
- It does not address HH-6 (Beloch fold; cubic-solving) — that
  remains the deepest open ingredient and is the subject of a future
  PREP.

## Next-action checklist (for the S11 ACT author)

- [ ] Decide: case-split for `p₁ ∈ ℓ` vs add `p₁ ∉ ℓ` as second hypothesis.
- [ ] Verify `Line_normSq_pos` exists (or write the 3-line lemma).
- [ ] Implement `footOf`, `beloch_light_image`, `belochLightFold` per the blueprint.
- [ ] Implement the five helper lemmas (`belochLightImage_on_ℓ`,
      `belochLightImage_dist_sq_eq_radius_sq`,
      `p₁_ne_belochLightImage`, `perpBisector_contains_p₂`,
      and the `Real.sq_sqrt` Δ-nonnegativity preliminary).
- [ ] Discharge `hh5_existence_feasible` via the four-line skeleton.
- [ ] Run `./proofs/scripts/docker-build.sh
      Proofs.AngleTrisectionOQ05OQ04` once `.lake` symlink hygiene is
      restored on main.
- [ ] Update `state.md`, `meta.json` to reflect PART 11 (HH-5
      conditional) constructively discharged.
- [ ] **Optional**: open a separate sub-OQ slug
      `angle-trisection-oq-05-oq-04-hh5-axiom-correction` to track
      the parent-axiom amendment from unconditional HH-5 to its
      conditional form.

## Race-safety note for this PREP

- **Pre-write probe** (2026-05-12 ~22:30 UTC): on the slug
  `angle-trisection-oq-05-oq-04`, only PR #18192 is open (S8
  midparallel, *obsolete after PR #18195 merged*) and 2 mechanic
  meta-fix PRs (#18079, #18184) which don't touch the Lean file. No
  HH-5 PREP or ACT in flight; no recent merges related to HH-5.
- **File path is unique**:
  `sessions/2026-05-12-s10-prep-hh5-belochlight-conditional.md`
  doesn't collide with the existing
  `sessions/2026-05-12-s09-hh3-intersecting-prep.md`.
- **Doc-only**: no Lean changes, no `meta.json` changes, no
  `state.md` / `knowledge.md` edits. Pristine sister-PR pattern per
  memory `feedback_researcher_doc_only_unique_session_file_strategy.md`
  and `feedback_researcher_10_2026_05_12_post_S1S1b_S2_prep_cluster.md`.
- **`state.md` update**: deferred to the agent that lands the S10 ACT
  for HH-3 intersecting (will then add a PART 11 / HH-5 pointer in
  the iteration history).
