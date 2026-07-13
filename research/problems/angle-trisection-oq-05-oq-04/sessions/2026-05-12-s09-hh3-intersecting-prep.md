# S9 PREP — HH-3 Intersecting Case via Real.sqrt-Normalized Angle Bisector

**Date**: 2026-05-12
**Researcher**: researcher-12
**Phase**: PREP (doc-only, sister-document escape)
**Status**: design / blueprint — no Lean file edits, no `meta.json` edits, no `state.md` edits

## Pristine doc-only scope

This session creates **one new file** in a fresh `sessions/` subdirectory:

```
research/problems/angle-trisection-oq-05-oq-04/sessions/
└── 2026-05-12-s09-hh3-intersecting-prep.md   (this file)
```

Untouched in this PR:
- `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`
- `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`
- `research/problems/angle-trisection-oq-05-oq-04/{problem,state,knowledge}.md`

Therefore this PR is *pristine orthogonal* to the two open S8 PRs that
both modify the Lean file, `meta.json`, and `state.md`:

- **PR #18192** — S8 same-coefficient parallel sub-case via `midparallel`
- **PR #18195** — S8 full parallel case via `parallelBisector`
  (subsumes #18192)

Whichever of #18192 / #18195 lands, the present design slots into S10
without conflict — none of the identifiers proposed below collide with
either PR's identifiers (`midparallel`, `parallelBisector`,
`hh3_existence_same_coeffs`, `hh3_existence_parallel`).

## Position within the HH-axiom programme

After S3-S8 the constructive HH coverage is:

| Axiom | Coverage                           | PR(s)                              |
|-------|------------------------------------|------------------------------------|
| HH-1  | unconditional                      | S3 #17915 (open)                   |
| HH-2  | unconditional                      | S4 #17926 (merged)                 |
| HH-3  | parallel only (`crossDet = 0`)     | S8 #18192/#18195 (one to merge)    |
| HH-4  | unconditional                      | S5 #17988 (merged)                 |
| HH-5  | open                               | —                                  |
| HH-6  | open (Beloch fold, cubic-solving)  | —                                  |
| HH-7  | `{crossDet ≠ 0} ∪ {P ∈ ℓ₁}`        | S6 #18009 / S7 #18059 (merged)     |

This S9 PREP designs the **HH-3 intersecting case** (`crossDet ≠ 0`),
which together with the parallel sub-case from S8 would close HH-3
**unconditionally**, lifting the table to four-of-seven HH axioms
fully unconditional (HH-1, HH-2, HH-3, HH-4) — leaving only HH-5,
HH-6, and the genuinely-unsolvable parallel-with-`P ∉ ℓ₁` sliver of
HH-7 outstanding.

## Geometric content

For two intersecting lines

```
ℓ₁ : a₁ x + b₁ y + c₁ = 0
ℓ₂ : a₂ x + b₂ y + c₂ = 0
```

with `crossDet ℓ₁ ℓ₂ = ℓ₁.b · ℓ₂.a − ℓ₁.a · ℓ₂.b ≠ 0` (i.e. the normals
are linearly independent), there are **two angle bisectors** at the
unique intersection point — perpendicular to each other. Either one is
a valid HH-3 fold: reflection across it maps `ℓ₁` (setwise) onto `ℓ₂`.

The classical signed-distance derivation: a point `p` lies on the
bisector of `ℓ₁` and `ℓ₂` iff its (signed) Euclidean distances to the
two lines are equal in magnitude. Writing
`Dᵢ := √(aᵢ² + bᵢ²)` (positive by `nondeg`), the signed distances are

```
dist(p, ℓᵢ) = (aᵢ p.1 + bᵢ p.2 + cᵢ) / Dᵢ.
```

Setting `dist(p, ℓ₁) = ε · dist(p, ℓ₂)` for `ε ∈ {+1, −1}` yields the
two bisectors:

```
ε = −1:  (D₂ a₁ + D₁ a₂) x + (D₂ b₁ + D₁ b₂) y + (D₂ c₁ + D₁ c₂) = 0
ε = +1:  (D₂ a₁ − D₁ a₂) x + (D₂ b₁ − D₁ b₂) y + (D₂ c₁ − D₁ c₂) = 0
```

(The `−` sign on the right of the equality corresponds to `ε = +1`,
because `f₁ = +f₂` gives `f₁ − f₂ = 0`, after clearing `D₁ D₂`.)

The two bisectors are perpendicular: their normals
`(D₂ a₁ ± D₁ a₂, D₂ b₁ ± D₁ b₂)` have inner product
`D₂² a₁² − D₁² a₂² + D₂² b₁² − D₁² b₂² = D₂² · D₁² − D₁² · D₂² = 0`.

### Choice of bisector and `nondeg`

The `−` bisector vanishes (i.e. its `(a, b)` coefficients are both
zero) iff

```
D₂ a₁ = D₁ a₂   ∧   D₂ b₁ = D₁ b₂,
```

which forces `(a₁, b₁) = (D₁/D₂) (a₂, b₂)` — `ℓ₁`'s normal is a
*positive* scalar multiple of `ℓ₂`'s normal. This is exactly the
"same-orientation parallel" case, where `crossDet = 0`; under our
hypothesis `crossDet ≠ 0` this case is *excluded*, so the `−`
bisector's `(a, b)` is nonzero and the line is nondegenerate.

Symmetric story for the `+` bisector: it vanishes iff
`(a₁, b₁) = -(D₁/D₂) (a₂, b₂)` (opposite-orientation parallel),
which again forces `crossDet = 0` and is excluded by hypothesis.

**Either bisector works under `crossDet ≠ 0`.** S9 will use the `−`
bisector for definiteness; the `+` bisector is the perpendicular
alternative and not needed for HH-3 existence (HH-3 only asks for
*one* fold).

## Lean blueprint (S10 ACT target)

Add a new section "PART 11" (or PART 12 if a parallel-PR-hindsight
re-numbering happens after #18192/#18195 land) at the END of
`AngleTrisectionOQ05OQ04.lean`, *after* whatever S8 section lands.

### Definitions (one `noncomputable def`)

```lean
/-- The angle bisector of two intersecting lines, in the
    `Real.sqrt`-normalised "minus" form. Coefficients:
    (D₂ · a₁ − D₁ · a₂, D₂ · b₁ − D₁ · b₂, D₂ · c₁ − D₁ · c₂),
    where Dᵢ := √(aᵢ² + bᵢ²). Defined for any two `Line`s; `nondeg`
    requires `crossDet ℓ₁ ℓ₂ ≠ 0` (proved separately). -/
noncomputable def angleBisectorMinus (ℓ₁ ℓ₂ : Line)
    (h_nonpar : crossDet ℓ₁ ℓ₂ ≠ 0) : Line where
  a := Real.sqrt (ℓ₂.a^2 + ℓ₂.b^2) * ℓ₁.a -
       Real.sqrt (ℓ₁.a^2 + ℓ₁.b^2) * ℓ₂.a
  b := Real.sqrt (ℓ₂.a^2 + ℓ₂.b^2) * ℓ₁.b -
       Real.sqrt (ℓ₁.a^2 + ℓ₁.b^2) * ℓ₂.b
  c := Real.sqrt (ℓ₂.a^2 + ℓ₂.b^2) * ℓ₁.c -
       Real.sqrt (ℓ₁.a^2 + ℓ₁.b^2) * ℓ₂.c
  nondeg := angleBisectorMinus_nondeg ℓ₁ ℓ₂ h_nonpar
```

### Helper lemmas (estimated 4)

1. **`Real.sqrt_normSq_pos`** — for any `Line ℓ`,
   `Real.sqrt (ℓ.a^2 + ℓ.b^2) > 0`. One-line `Real.sqrt_pos.mpr` +
   the existing pattern from `perpBisector_dirSq_pos` (line 494)
   adapted for `^2 + ^2`.

2. **`Real.sqrt_normSq_sq`** — for any `Line ℓ`,
   `(Real.sqrt (ℓ.a^2 + ℓ.b^2))^2 = ℓ.a^2 + ℓ.b^2`. From
   `Real.sq_sqrt` against the nonnegativity `0 ≤ ℓ.a^2 + ℓ.b^2`
   (one `nlinarith` or `add_nonneg (sq_nonneg _) (sq_nonneg _)`).

3. **`angleBisectorMinus_nondeg`** — under `crossDet ≠ 0`, the `(a, b)`
   pair above is not `(0, 0)`. Proof (contrapositive): assume both
   coefficients vanish. Multiply `D₂ a₁ = D₁ a₂` by `b₂` and
   `D₂ b₁ = D₁ b₂` by `a₂` and subtract:

   ```
   D₂ (a₁ b₂ − b₁ a₂) = D₁ (a₂ b₂ − b₂ a₂) = 0,
   ```

   so `D₂ · crossDet ℓ₂ ℓ₁ = 0`. Since `D₂ > 0` (helper #1) and
   `crossDet ℓ₂ ℓ₁ = − crossDet ℓ₁ ℓ₂ ≠ 0`, contradiction.

   Lean: 4-6 lines using `by_contra`, the two scalar equations, and a
   `linear_combination`/`nlinarith` discharge.

4. **`angleBisectorMinus_dot_normsSquared`** — auxiliary identity used
   in the main reflection theorem. For any `q ∈ ℓ₁`,

   ```
   ℓ₂.a · (reflectAcross (angleBisectorMinus ℓ₁ ℓ₂ h) q).1
     + ℓ₂.b · (reflectAcross (angleBisectorMinus ℓ₁ ℓ₂ h) q).2
     + ℓ₂.c
     = (a polynomial in ℓ₁.a, ℓ₁.b, ℓ₁.c, ℓ₂.a, ℓ₂.b, ℓ₂.c, q.1, q.2,
        D₁, D₂)
   ```

   that vanishes after substituting `D₁² = ℓ₁.a² + ℓ₁.b²`,
   `D₂² = ℓ₂.a² + ℓ₂.b²`, and `hq : ℓ₁.a · q.1 + ℓ₁.b · q.2 + ℓ₁.c = 0`.
   The cancellation pattern is the same as S5's
   `reflectAcross_perpThroughPoint_preserves` modulo additional
   `D₁ · D₂` cross-terms — see "Algebraic cancellation" below.

### Main theorem

```lean
/-- HH-3 reflection law (intersecting case): for any q ∈ ℓ₁,
    reflection across the angle bisector lies in ℓ₂. -/
theorem reflectAcross_angleBisectorMinus_to_ℓ₂
    (ℓ₁ ℓ₂ : Line) (h_nonpar : crossDet ℓ₁ ℓ₂ ≠ 0) :
    ∀ q : Point, ℓ₁.contains q →
      ℓ₂.contains (reflectAcross (angleBisectorMinus ℓ₁ ℓ₂ h_nonpar) q) := by
  intro q hq
  -- Standard pattern from S5/S6/S8:
  --   simp only [Line.contains, reflectAcross, angleBisectorMinus]
  --   field_simp [Real.sqrt_normSq_pos.ne', ...]
  --   linear_combination <coefficients> * hq + <coeffs> * (D₁²-identity) + <coeffs> * (D₂²-identity)
  sorry  -- to be discharged in S10 ACT
```

### Standalone HH-3 existence

```lean
/-- Standalone HH-3 existence in the intersecting case. -/
theorem hh3_existence_intersecting :
    ∀ (ℓ₁ ℓ₂ : Line), crossDet ℓ₁ ℓ₂ ≠ 0 →
      ∃ l : Line, ∀ p : Point, ℓ₁.contains p →
        ℓ₂.contains (reflectAcross l p) := by
  intro ℓ₁ ℓ₂ h_nonpar
  exact ⟨angleBisectorMinus ℓ₁ ℓ₂ h_nonpar,
         reflectAcross_angleBisectorMinus_to_ℓ₂ ℓ₁ ℓ₂ h_nonpar⟩
```

## Algebraic cancellation (the heart of the proof)

Set up notation:

```
A := ℓ₁.a,  B := ℓ₁.b,  C := ℓ₁.c,    D₁² = A² + B²
α := ℓ₂.a,  β := ℓ₂.b,  γ := ℓ₂.c,    D₂² = α² + β²
a := D₂ A − D₁ α,  b := D₂ B − D₁ β,  c := D₂ C − D₁ γ
```

The bisector's squared norm:

```
a² + b² = D₂² (A² + B²) − 2 D₁ D₂ (A α + B β) + D₁² (α² + β²)
        = D₂² · D₁² − 2 D₁ D₂ s + D₁² · D₂²
        = 2 D₁ D₂ (D₁ D₂ − s),     where s := A α + B β.
```

The reflection parameter:

```
t = 2 (a q.1 + b q.2 + c) / (a² + b²)
  = (a q.1 + b q.2 + c) / (D₁ D₂ (D₁ D₂ − s)).
```

The reflected point's coordinates:

```
q'.1 = q.1 − t · a,   q'.2 = q.2 − t · b.
```

The HH-3 obligation:

```
α q'.1 + β q'.2 + γ
  = (α q.1 + β q.2 + γ) − t (α a + β b)
  = (α q.1 + β q.2 + γ) − t · (D₂ s − D₁ D₂²)
  = (α q.1 + β q.2 + γ) − t · D₂ (s − D₁ D₂).
```

Substituting `t = (a q.1 + b q.2 + c) / (D₁ D₂ (D₁ D₂ − s))`:

```
  = (α q.1 + β q.2 + γ) + (a q.1 + b q.2 + c) · D₂ / (D₁ D₂)
  = (α q.1 + β q.2 + γ) + (a q.1 + b q.2 + c) / D₁.
```

Now expand the second summand using `(a, b, c) = D₂(A, B, C) − D₁(α, β, γ)`:

```
(a q.1 + b q.2 + c) / D₁
  = D₂ (A q.1 + B q.2 + C) / D₁  −  (α q.1 + β q.2 + γ).
```

So

```
α q'.1 + β q'.2 + γ = D₂ (A q.1 + B q.2 + C) / D₁
                    = D₂ · 0 / D₁         (using hq : A q.1 + B q.2 + C = 0)
                    = 0.   ✓
```

That's the identity; the Lean proof packages this as a single
`linear_combination` after `field_simp` clears the `D₁ D₂ (D₁ D₂ − s)`
denominator. The `D₁ D₂ − s ≠ 0` non-vanishing is exactly equivalent
to `nondeg` of the bisector (i.e. equivalent to `crossDet ≠ 0`), via
the determinant identity

```
2 D₁ D₂ (D₁ D₂ − s) = (D₂ A − D₁ α)² + (D₂ B − D₁ β)²
                    = a² + b²  ≥ 0,
```

with equality iff the `−` bisector is degenerate (which is forbidden
by `h_nonpar`).

## Concrete-example sanity check

Take `ℓ₁: x = 0` (i.e. `a₁ = 1, b₁ = 0, c₁ = 0`, `D₁ = 1`) and
`ℓ₂: y = 0` (i.e. `a₂ = 0, b₂ = 1, c₂ = 0`, `D₂ = 1`). These are
perpendicular (`crossDet = 0·0 − 1·1 = −1 ≠ 0` ✓).

The `−` bisector: `(1·1 − 1·0, 1·0 − 1·1, 0) = (1, −1, 0)`, i.e. the
line `y = x` — the angle bisector of the first and third quadrants. ✓

Reflect `q = (3, 0) ∈ ℓ₁`:

```
t = 2 · (1·3 + (−1)·0 + 0) / (1² + (−1)²) = 6/2 = 3,
q' = (3 − 3·1, 0 − 3·(−1)) = (0, 3) ∈ ℓ₂. ✓
```

(Of course — reflection across `y = x` swaps coordinates, sending
`(3, 0)` to `(0, 3)`.)

Reflect `q = (5, 0) ∈ ℓ₁`:

```
t = 2 · 5 / 2 = 5,
q' = (5 − 5, 0 + 5) = (0, 5) ∈ ℓ₂. ✓
```

## Risks and known pitfalls

### `Real.sqrt`-related drift

The proof needs three `Real.sqrt` lemmas, and the exact spelling at
`v4.26.0` should be confirmed before authoring S10:

| Conceptual | Likely current spelling          | Alternatives |
|------------|----------------------------------|--------------|
| `√(x) > 0` from `x > 0` | `Real.sqrt_pos.mpr` | `Real.sqrt_pos_of_pos` |
| `(√x)² = x` for `x ≥ 0` | `Real.sq_sqrt h` | `Real.sqrt_sq h` (different arg shape) |
| `√x · √y = √(x · y)` (probably not needed) | `Real.sqrt_mul` | `Real.sqrt_mul'` |

The `Real.sqrt_normSq_pos` helper sidesteps the first two by packaging
both into one lemma keyed on `Line`.

### `field_simp` denominator handling

Both `D₁` and `D₂` need to be supplied to `field_simp`'s positivity
hypothesis list (or their nonzeroness threaded as `Real.sqrt_pos.mpr
(by positivity)` proofs). The single denominator after `field_simp`
will be `2 · D₁ · D₂ · (D₁ · D₂ − s)` (or its expansion); `nlinarith`
or `linear_combination` over `(D₁²) = A² + B²`, `(D₂²) = α² + β²`, and
`hq` should close it. **Caveat**: `linear_combination` may not
discharge through `Real.sqrt`s directly — the proof may need to
introduce `set d₁ := Real.sqrt (A² + B²)` and treat `d₁`/`d₂` as
opaque variables with hypotheses `d₁² = A² + B²` and `d₂² = α² + β²`.
This is the same trick used in geometric-mean proofs in Mathlib and
adds only ~3 lines of preamble.

### Length and verification

Estimated additional Lean: **~150 lines** (one `def`, four helper
`theorem`s, one main `theorem`, one standalone `theorem`, plus
docstrings). Same "build pending" convention as S2-S8 due to the
known recursive-self-broken `.lake` symlink in worktrees.

### Coordination with S8 PRs

This S9 PREP defines `angleBisectorMinus` and `hh3_existence_intersecting`
— **neither name collides** with S8's `midparallel` / `parallelBisector`
/ `hh3_existence_same_coeffs` / `hh3_existence_parallel` / `hh3_existence`
(if either S8 PR introduces an aggregate). The S10 ACT PR can compose:

```lean
theorem hh3_existence_unconditional : ∀ (ℓ₁ ℓ₂ : Line),
    ∃ l : Line, ∀ p : Point, ℓ₁.contains p →
      ℓ₂.contains (reflectAcross l p) := by
  intro ℓ₁ ℓ₂
  by_cases h_nonpar : crossDet ℓ₁ ℓ₂ = 0
  · exact hh3_existence_parallel ℓ₁ ℓ₂ h_nonpar          -- from S8 #18195
  · exact hh3_existence_intersecting ℓ₁ ℓ₂ h_nonpar      -- from S10
```

Once both are in place, the third HH ingredient (HH-3, fully
unconditional) is constructive in standalone form, joining HH-1, HH-2,
and HH-4 in the unconditional column.

## Honest calibration

This S9 contributes:

- One **doc-only** design file in a fresh `sessions/` subdirectory.
- A complete algebraic derivation of the HH-3 intersecting-case
  reflection identity, including the `Real.sqrt`-cancellation
  blueprint and the `nondeg` proof.
- Two concrete-example sanity traces (`(3,0) → (0,3)` and
  `(5,0) → (0,5)` across `y = x`) verifying the formula.
- A Lean blueprint sized for one S10 ACT iteration (~150 lines, four
  helpers + one main theorem + one standalone existence theorem).
- Coordination with the two open S8 PRs (#18192, #18195) — pristine
  orthogonal at the file level (one new file, no edits to anything
  the S8 PRs touch); compatible at the identifier level.

This S9 does **not** prove anything new in Lean. It does **not**
modify the slug's headline counts (`lineCount`, `theoremCount`,
`definitionCount`, `axiomCount`, `sorries` — all unchanged). Its
value is to lay out the algebra and identifier choices for HH-3
intersecting case so that the next researcher to claim this slug can
go directly to S10 ACT (Lean implementation) without re-deriving the
formulas or worrying about identifier collisions with whichever S8 PR
lands first.

After S10 lands HH-3 unconditional coverage, four of seven HH
ingredients (HH-1, HH-2, HH-3, HH-4) will be unconditional — leaving
only HH-5, HH-6 (the cubic-solving Beloch fold), and the
genuinely-unsolvable parallel-with-`P ∉ ℓ₁` sliver of HH-7 to close
before the full `HHAxioms` instance can be assembled and the
`straight_fold_recovers_HH` sorry from S3 can be discharged.

## References

Same as the slug's S1-S8 references: Huzita 1989; Justin 1991; Hatori
2001 (HH-7 addition); Alperin 2000 (origami axioms and field theory);
Alperin-Lang 2006 (`K_origami` classification); Demaine-DHPT 2011
(transcendental curve elastica witness); Fuchs-Tabachnikov 1999
(FT identity, the structure-encoded `ftCompatible` assumption).
Standard Euclidean geometry (any analytic geometry text) for the
angle-bisector formula — e.g. Coxeter, *Introduction to Geometry*,
§1.6 (Angles and rotations).
