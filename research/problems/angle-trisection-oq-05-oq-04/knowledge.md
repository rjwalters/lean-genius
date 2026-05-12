# Knowledge — angle-trisection-oq-05-oq-04

## S1 (researcher-12, 2026-05-12) — OBSERVE survey

### Status

The question asks whether the seven straight-crease Huzita-Hatori axioms
admit a *coherent extension* — a finite axiom or axiom-schema — that
captures **curved-crease origami constructibility**. The literature
distinguishes three separate strands; only the first is in scope for a
Lean axiomatic formalisation.

| Strand | Object | Setting | Lean tractability |
|--------|--------|---------|--------------------|
| (i) Smooth differential geometry of a single curved fold | `(γ, θ)` with `κ_n = κ_g · cot(θ/2)` | Fuchs-Tabachnikov 1999 | **tractable**, given the compatibility identity as a primitive |
| (ii) Algorithmic / discretised construction of curved-crease tessellations | piecewise-analytic γ; meshing | Tachi 2010, Mitani 2009, Demaine et al. 2011 | not appropriate for axiomatic Lean treatment |
| (iii) Constructibility-field theory `K_curved ⊆ ℝ` | algebraic-closure question | open (folklore) | **partially tractable** — axiom system can be stated; the strict-inclusion theorem is open mathematics |

We pursue (i) + (iii). Strand (ii) is out of scope.

### Parent file inventory

`proofs/Proofs/AngleTrisectionOQ05.lean` (695 lines, 0 axioms, 0 sorries,
27 theorems) provides exactly the primitives the OQ-04 extension needs:

| Decl | Line | Used by OQ-04 |
|------|------|---------------|
| `structure Point` (in earlier imports) | — | yes (γ's codomain) |
| `structure Line` | 68 | yes (straight-fold limit) |
| `def reflectAcross : Line → Point → Point` | 99 | conceptually — the curved-fold reflection generalises this |
| `structure HHAxioms` (fields HH1-HH7) | 108 | yes (limit case of curved fold) |
| `def IsOrigamiConstructible (α d)` | 182 | yes (`K_origami ⊆ K_curved`) |
| `def IsConstructible (α d)` | 187 | for the c+s comparison |
| `def IsMultiFoldConstructible (α d k)` | 520 | the natural rival hierarchy |
| `theorem origami_degree_classification` | 575 | the algebraic-closure model to *strengthen* |
| `theorem multifold_strictly_stronger` | 544 | reference for "strict inclusion" template |

The straight-fold limit case (κ_g ≡ 0) reduces to a single H-H axiom; the
parent file's `HHAxioms` structure is the codomain of that reduction.

### The Fuchs-Tabachnikov compatibility identity

The mathematical heart of the curved-fold theory is the **single
compatibility identity** linking the planar geometry of γ to the
dihedral fold-angle profile θ:

```
                  θ(s)
   κ_n(s)  =  κ_g(s) · cot( ───── )                          (FT)
                            2
```

Here, with γ : [0,L] → ℝ² a unit-speed analytic curve:
- `κ_g(s)` = signed planar curvature of γ in the unfolded paper
  (since the paper is intrinsically flat, planar curvature = geodesic
  curvature),
- `θ(s) ∈ (0, π)` = dihedral fold angle along γ,
- `κ_n(s)` = normal curvature of γ as a curve on the folded surface.

The straight-fold limit `κ_g ≡ 0` forces `κ_n ≡ 0`: both sides remain
flat, recovering exactly the H-H setting. Conversely, fixing
`θ(s) ≡ θ_0` constant gives `κ_n = κ_g · cot(θ_0/2)`: a curved crease
with constant fold angle determines `κ_g` up to a global scale.

**Reference**: Fuchs, D.; Tabachnikov, S. *More on paperfolding.* Amer.
Math. Monthly 106(1), 27-35, 1999. The identity is Theorem 1 of that
paper; the proof is a one-page differential-geometric computation using
the Darboux frame on γ.

### Three candidate axiomatic strengthenings

The Lean question reduces to *picking* the right axiom schema. The
three options that have been floated (informally) are:

#### Strengthening (P1): Single curved axiom O8

Add a single axiom O8 *parametrised by (γ, θ) satisfying FT* asserting
that the fold exists. This is the most natural extension and matches
Strand (i) above. **Cost**: O8 is parametrised by *infinite-dimensional*
data (smooth functions), unlike the H-H axioms which are parametrised
by finitely many marked points. The resulting system is not finitary.

#### Strengthening (P2): Finite Beloch-style restriction

Restrict O8 to **algebraic** γ and θ of bounded degree, parametrised by
their finitely many coefficients. Compatibility is then a polynomial
identity on those coefficients (after rationalising the `cot(θ/2)` via
`t = tan(θ/4)`, the identity becomes algebraic). The resulting system
is **finitary** but has an infinite hierarchy of axioms indexed by the
degree bound `d` — i.e. it is a *schema*, not a single axiom.

#### Strengthening (P3): Algebraic-closure-only

Skip the explicit fold and just postulate: `K_curved` is the smallest
subfield of ℝ closed under the H-H constructions **and under solving
the resulting polynomial system** (compatibility for a degree-`d` γ is
a system of `O(d)` polynomial equations in `O(d)` unknowns). Equivalent
to (P2) by elimination theory; cleaner for algebraic statements but
loses the geometric primitive.

The **OQ-04 question itself** is whether (P1), (P2) and (P3) all generate
the same field `K_curved` — and if so, whether that field strictly
contains `K_origami`.

### Connections to the sibling proofs

| Sibling | Result | Use in OQ-04 |
|---------|--------|--------------|
| `oq-05-oq-01` | k-fold origami via p-smooth degree closure | upper bound on `K_curved` if curved-fold ≤ ω-fold |
| `oq-05-oq-02` | ω-fold algebraic completeness (every positive degree) | the conjectured ceiling: `K_curved ⊆ K_ω` |
| `oq-05-oq-03` | `minFoldLevel(d)` characterisation | quantifies the "fold complexity" of a degree |
| `oq-05` parent | `α origami-constructible ↔ [ℚ(α):ℚ] | 2^a · 3^b` | the **algebraic model** that OQ-04 strengthens |

### Mathlib gap analysis

The curved-fold primitive needs four ingredients absent from Mathlib
at the pinned revision:

| # | Missing primitive | Closest Mathlib API | Effort to bridge |
|---|--------------------|---------------------|------------------|
| 1 | Geodesic / planar curvature of a smooth `γ : ℝ → ℝ²` | `Mathlib.Geometry.Euclidean.Curvature.Plane` has `curvatureOfFunction` for graphs only | ~80 lines: extend to parametric unit-speed curves |
| 2 | Developable ruled surface from `γ` and rulings field | none | ~200 lines: define a parametrised ruled surface and prove it is developable iff its Gaussian curvature is identically zero |
| 3 | Dihedral fold angle as a function on γ | none | ~30 lines: just `θ : [0,L] → ℝ`, smooth, valued in `(0, π)` |
| 4 | Fuchs-Tabachnikov compatibility identity (FT) | none | ~150 lines: differential-geometric computation in the Darboux frame |

For OQ-04 *axiomatisation* only (i.e. without proving FT internally) we
can postulate (4) as a **structure field**: a `CurvedCrease` is a tuple
`(γ, θ, κg, κn, ftCompatible)` with `ftCompatible : ∀ s, κn s = κg s * Real.tan (θ s / 2)⁻¹`.
This sidesteps (1)-(4) entirely and gives a Lean-tractable S2 deliverable.

### Decomposition plan (revisits the problem.md table with effort numbers)

| Session | Lines (est.) | Sorries delta | Axioms delta | Net |
|---------|--------------|---------------|--------------|-----|
| S1 OBSERVE (this) | 0 Lean / ~400 md+json | 0 | 0 | survey only |
| S2 ORIENT | ~180 Lean | +3 (statements only) | 0 | new structure + main theorem stmts |
| S3 ACT (straight-fold conservativity) | ~120 Lean | -1 | 0 | proves limit case |
| S4 ACT (algebraic curve curved-fold ≤ origami) | ~100 Lean | -1 | 0 | partial sharpness |
| S5 ACT (OQ-A formal conjecture) | ~50 Lean | +1 (open conjecture) | 0 | sorry-bearing theorem stmt for archival |

Total over 5 sessions: ~450 Lean, 1 open sorry (intentional, the
unresolved mathematical conjecture), 0 axioms.

### Next action for S2

Create `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (no Aristotle
companion needed; the targets are too geometric for current Aristotle
heuristics). Skeleton:

```lean
import Proofs.AngleTrisectionOQ05
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace AngleTrisectionOQ05OQ04

open AngleTrisectionOQ05

/-- A smooth curved crease: a parametric curve γ on [0, L], a dihedral
fold-angle profile θ, and signed geodesic/normal curvatures κg, κn that
satisfy the Fuchs-Tabachnikov compatibility identity
  κn s = κg s · cot(θ s / 2)
along the entire crease. -/
structure CurvedCrease where
  L : ℝ
  hL : 0 < L
  γ : ℝ → ℝ × ℝ
  θ : ℝ → ℝ
  κg : ℝ → ℝ
  κn : ℝ → ℝ
  hθ_pos : ∀ s ∈ Set.Icc 0 L, 0 < θ s ∧ θ s < Real.pi
  ftCompatible :
    ∀ s ∈ Set.Icc 0 L,
      κn s = κg s * (Real.tan (θ s / 2))⁻¹

/-- A curved crease is **straight** if its geodesic curvature is
identically zero on the parameter interval [0, L]. -/
def CurvedCrease.IsStraight (c : CurvedCrease) : Prop :=
  ∀ s ∈ Set.Icc 0 c.L, c.κg s = 0

/-- **Conservativity**: any straight curved crease whose endpoints
lie on a constructible line and whose midpoint folds two H-H-marked
points onto each other reduces to a fold satisfying one of the seven
HHAxioms fields. (S3 target.) -/
theorem straight_fold_recovers_HH (c : CurvedCrease)
    (hStraight : c.IsStraight) :
    True := by
  sorry  -- S3 ACT: reduce κg ≡ 0 case to HHAxioms.HH2 / HH3 / ...

end AngleTrisectionOQ05OQ04
```

### Honest assessment

This is a **broad, partly-open** mathematical question. The S1 survey is
the genuinely tractable contribution; S2-S4 are tractable formalisation
work; S5 is by definition an open conjecture that we can only *state*
in Lean, not prove. The OQ-04 deliverable, even if completed end-to-end,
would not "close" the question — it would package the *language* in
which the question can be precisely stated.

Honesty calibration:
- The S1 OBSERVE document **does not** resolve the mathematical question.
- The S2-S4 plan delivers a **conservative extension** (curved fold ⊇
  straight fold), which is the *minimum useful* gallery contribution.
- The S5 conjecture is **open mathematics**, dating back to Huffman 1976.

---

## S9 (researcher-6, 2026-05-12) — HH-3 intersecting case plan, `Real.sqrt` API survey, HH-5 / HH-6 outlook

This is a **doc-only OBSERVE** iteration. Its purpose is to provide a
concrete, race-safe plan for the remaining three HH-axiom existence
ingredients (HH-3 intersecting case, HH-5, HH-6) so that whichever
researcher claims `angle-trisection-oq-05-oq-04` next has a ready
work order. No Lean source is touched in this iteration to avoid
textual conflict with the two in-flight S8 PRs (#18192 same-coefficient
midparallel; #18195 full-parallel translate-bisector) — both of which
add a new "Part 10" section at the end of `AngleTrisectionOQ05OQ04.lean`
and rewrite `state.md` + `meta.json`. The Lean code referenced below
should be added as **Part 11/12** *after* one of the S8 PRs merges and
its final identifier names are visible.

### S9 starting snapshot (origin/main HEAD)

After S7 (PR #18059 merged), the constructive HH coverage on
`origin/main` is:

| Axiom | Coverage in main | Builder | Open work |
|------:|------------------|--------:|-----------|
| HH-1 | unconditional | S3 (PR #17915, still open build-pending in main as a sorry-bearing target) | reduction `straight_fold_recovers_HH` is the S3 sorry |
| HH-2 | unconditional | S4 (PR #17926) | none — clean |
| HH-3 | **none in main** — both S8 sub-cases are still in flight | (S8 #18192 / #18195) | **the intersecting case `crossDet ≠ 0` is not yet planned** (S9 below) |
| HH-4 | unconditional | S5 (PR #17988) | none — clean |
| HH-5 | none | — | **S10/S11 target** (Beloch-light, parabola tangent) |
| HH-6 | none | — | **final** target (cubic-solving Beloch fold) |
| HH-7 | `{crossDet ≠ 0} ∪ {P ∈ ℓ₁}` | S6 (PR #18009), S7 (PR #18059) | the corner `crossDet = 0 ∧ P ∉ ℓ₁` is **genuinely unsolvable** — S6 documented why (any fold perpendicular to ℓ₂ in the parallel configuration preserves perpendicular distance to ℓ₁, so `P ∉ ℓ₁` is a reflection-invariant) |

So three HH ingredients remain to be made constructive: **HH-3
intersecting**, **HH-5**, **HH-6**. The HH-7 obstruction is permanent
and will be encoded as a precondition on the eventual `HHAxioms`
instance (parent file's HH-7 signature is unconditional, so the
constructive instance will need to either weaken HH-7 in the curved-
crease setting or carry the parallel-and-`P ∉ ℓ₁` corner as the *one*
remaining assumption).

### Plan for HH-3 intersecting case (S9/S10 ACT target)

#### Geometric statement

Given two lines `ℓ₁ : a₁x + b₁y + c₁ = 0` and `ℓ₂ : a₂x + b₂y + c₂ = 0`
with `crossDet ℓ₁ ℓ₂ ≠ 0` (so they meet at a unique point), there are
**two** fold lines that map `ℓ₁` to `ℓ₂` — the two angle bisectors at
the intersection point. Either suffices as a constructive witness.

The classical formula for the angle bisectors is:

```
                                      a · n + s · a₂ · n         (interior)
  bisector_± :   a· x  +  b · y +
                                      a · n − s · a₂ · n         (exterior)
```

where `n_i = Real.sqrt (aᵢ² + bᵢ²)` is the Euclidean norm of `ℓᵢ`'s
normal vector, and the normalised coefficient triple is the sum (or
difference) of the *unit* normals' triples:

```
  (a_±, b_±, c_±)  =  ( a₁/n₁  ±  a₂/n₂ ,  b₁/n₁  ±  b₂/n₂ ,  c₁/n₁  ±  c₂/n₂ )
```

Both bisectors pass through the intersection of `ℓ₁` and `ℓ₂` and meet
at right angles. Pick *one* (the `+` branch) for the constructive
witness; the existence statement is satisfied by either.

#### Why this needs `Real.sqrt`

The midparallel and translate-bisector constructions (S8 parallel case)
are pure ℝ-algebra — no square root. The intersecting case has no such
ℝ-algebraic witness because the bisector's *direction* depends on the
*ratio* of the two normals' magnitudes, and that ratio is in general
irrational even when `(a₁, b₁, c₁)` and `(a₂, b₂, c₂)` are rational
(e.g. `ℓ₁: x = 0, ℓ₂: x + y = 0` have norms `1, √2` and bisector
direction `(1 + 1/√2, 1/√2)`). Hence the S9 file unavoidably consumes
the `Real.sqrt` API from Mathlib.

#### Concrete `noncomputable def` skeleton

```lean
/-- Reciprocal Euclidean norm of a line's normal vector. Strictly positive
when the line is non-degenerate. -/
noncomputable def Line.invNorm (l : Line) : ℝ :=
  (Real.sqrt (l.a^2 + l.b^2))⁻¹

/-- Sum of the two unit normals' constant terms, used as the
intersecting-case bisector's `c` coefficient. -/
noncomputable def bisectorIntersecting (ℓ₁ ℓ₂ : Line)
    (_h_nonpar : crossDet ℓ₁ ℓ₂ ≠ 0) : Line where
  a := ℓ₁.a * ℓ₁.invNorm + ℓ₂.a * ℓ₂.invNorm
  b := ℓ₁.b * ℓ₁.invNorm + ℓ₂.b * ℓ₂.invNorm
  c := ℓ₁.c * ℓ₁.invNorm + ℓ₂.c * ℓ₂.invNorm
  nondeg := by
    -- Both summands have the same sign-direction of the normal as ℓ₁
    -- and ℓ₂; under crossDet ≠ 0 they are linearly independent (since
    -- their unscaled versions are), so the sum is non-zero coordinatewise.
    sorry  -- S9 ACT lemma — see proof outline below
```

#### Proof outline for `bisectorIntersecting_nondeg`

Argument by contradiction: assume `a₁/n₁ + a₂/n₂ = 0` and
`b₁/n₁ + b₂/n₂ = 0`. Multiplying through, `a₂ = -(n₂/n₁) · a₁` and
`b₂ = -(n₂/n₁) · b₁`, so `(a₂, b₂) = -(n₂/n₁) · (a₁, b₁)`. But then
`crossDet ℓ₁ ℓ₂ = b₁ · a₂ − a₁ · b₂ = (-(n₂/n₁)) · (b₁·a₁ − a₁·b₁) = 0`,
contradicting `crossDet ≠ 0`. Mathlib-tactic shape:

```lean
have h_ratio : ℓ₂.a = -(Real.sqrt (ℓ₂.a^2 + ℓ₂.b^2) / Real.sqrt (ℓ₁.a^2 + ℓ₁.b^2)) * ℓ₁.a := by
  -- from `a₁/n₁ + a₂/n₂ = 0`
  field_simp at h_a
  linarith [h_a, Real.sqrt_pos.mpr (l_pos ℓ₁)]
-- similarly for b
have : crossDet ℓ₁ ℓ₂ = 0 := by simp [crossDet]; linear_combination ...
exact _h_nonpar this
```

(The exact `linear_combination` coefficients fall out of running
`linear_combination?` once the file builds.)

#### Setwise-preservation theorem

The key theorem `reflectAcross_bisectorIntersecting_to_ℓ₂` says: for
any `q ∈ ℓ₁`, the reflection across `bisectorIntersecting ℓ₁ ℓ₂` lies
on `ℓ₂`. The algebraic content is the *normalised-reflection identity*:

```
  ℓ₂.a · q'.1 + ℓ₂.b · q'.2 + ℓ₂.c
    = (1/n₂) · ⟨ℓ₂_normalised, q'⟩
    = (1/n₂) · ( ⟨ℓ₂_normalised, q⟩ − 2 · ⟨ℓ₁_normalised + ℓ₂_normalised, q⟩ · cos α )
```

where `cos α` is the cosine of half the angle between `ℓ₁` and `ℓ₂`.
The proof in Lean reduces, after `field_simp` clearing
`(a₁/n₁ + a₂/n₂)² + (b₁/n₁ + b₂/n₂)²`, to a polynomial identity in
`a_i, b_i, c_i, n_i, q.1, q.2` modulo the four hypotheses

```
  n₁² = ℓ₁.a^2 + ℓ₁.b^2     (definition of n₁)
  n₂² = ℓ₂.a^2 + ℓ₂.b^2     (definition of n₂)
  ℓ₁.a · q.1 + ℓ₁.b · q.2 + ℓ₁.c = 0     (hq : q ∈ ℓ₁)
  crossDet ℓ₁ ℓ₂ = b₁ · a₂ − a₁ · b₂ ≠ 0     (intersecting hypothesis, used only for nondeg)
```

The identity is *not* a `ring`-only identity — `n_i` are `Real.sqrt`
values, so `n_i²` reduces to `aᵢ² + bᵢ²` only after the `Real.sqrt_sq`
rewrite (or equivalently `Real.sq_sqrt`). The cleanest proof strategy
is therefore:

1. Introduce abbreviations `n₁ := Real.sqrt (ℓ₁.a^2 + ℓ₁.b^2)` and
   `n₂ := Real.sqrt (ℓ₂.a^2 + ℓ₂.b^2)`.
2. Get the two non-vanishing facts `n₁ > 0`, `n₂ > 0` (from
   `Real.sqrt_pos.mpr` + the parent file's `nondeg`-derived
   `a² + b² > 0` lemma `perpThroughPoint_normSq_pos`).
3. Get the two squaring facts `n₁^2 = ℓ₁.a^2 + ℓ₁.b^2`,
   `n₂^2 = ℓ₂.a^2 + ℓ₂.b^2` from `Real.sq_sqrt` applied to the
   non-negativity `0 ≤ ℓᵢ.a^2 + ℓᵢ.b^2` (which is `add_nonneg
   (sq_nonneg _) (sq_nonneg _)`).
4. `simp only [Line.contains, reflectAcross, bisectorIntersecting,
   Line.invNorm] at hq ⊢`.
5. `field_simp` clears denominators `n₁`, `n₂`, and
   `(a₁/n₁ + a₂/n₂)² + (b₁/n₁ + b₂/n₂)²` (the last is positive via
   `nondeg`).
6. `linear_combination` against `n₁^2 = …`, `n₂^2 = …`, and `hq`.

Expected size of `bisectorIntersecting` + nondeg + preservation +
`hh3_existence_intersecting`: ~150 lines (comparable to `hatoriFold`
+ S6 setwise preservation + `hh7_existence_nonparallel`).

### `Real.sqrt` Mathlib API survey (relevant lemmas)

| Lemma | Statement | Used for |
|-------|-----------|----------|
| `Real.sqrt_pos` | `0 < Real.sqrt x ↔ 0 < x` | positivity of `n_i` |
| `Real.sqrt_nonneg` | `0 ≤ Real.sqrt x` | trivial nonneg |
| `Real.sq_sqrt` | `0 ≤ x → (Real.sqrt x)^2 = x` | replace `n^2` with `a² + b²` |
| `Real.sqrt_sq` | `0 ≤ x → Real.sqrt (x^2) = x` | the converse direction |
| `Real.sqrt_mul_self` | `0 ≤ x → Real.sqrt x * Real.sqrt x = x` | alternative to `sq_sqrt` when avoiding `^2` |
| `Real.sqrt_ne_zero'` | `Real.sqrt x ≠ 0 ↔ 0 < x` | `field_simp` precondition |
| `Real.sqrt_lt_sqrt` | monotonicity | not needed in HH-3 |
| `Real.sqrt_eq_iff_mul_self_eq` | for explicit-witness shape | not needed if we work with `^2` |

The two we will definitely consume are `Real.sqrt_pos` and
`Real.sq_sqrt`. The proof structure does *not* need any non-trivial
square-root identities (no `Real.sqrt_mul`, `Real.sqrt_div`, etc.) —
the bisector formula is a *sum of unit normals*, and once we know
`n_i^2 = aᵢ² + bᵢ²`, the polynomial identity dissolves.

### Plan for HH-5 (S10/S11 ACT target — parabola tangent)

#### Geometric statement

Given two distinct points `P₁, P₂` and a line `ℓ`, there is a fold line
*through `P₂`* that places `P₁` onto `ℓ`. Equivalently (by reflection):
the fold line is the tangent at some point of the parabola with focus
`P₁` and directrix `ℓ`, *constrained to pass through `P₂`*.

#### Constructive witness

Two cases:

1. **`P₂` outside the parabola** (i.e. `dist P₂ P₁ > dist P₂ ℓ`):
   there are **two** tangents from `P₂` to the parabola; pick either
   one as the witness.

2. **`P₂` on the parabola** (i.e. `dist P₂ P₁ = dist P₂ ℓ`):
   there is **one** tangent — the parabola's tangent line at `P₂`.

3. **`P₂` inside the parabola** (i.e. `dist P₂ P₁ < dist P₂ ℓ`):
   **no tangent** through `P₂` reaches the parabola, so HH-5's
   existence fails. This is a genuine obstruction to the *unconditional*
   HH-5; the constructive instance will need a `dist P₂ P₁ ≥ dist P₂ ℓ`
   precondition (or carry an axiom for the deep case).

#### Explicit formula (case 1: `P₂` outside the parabola)

Let `(x₀, y₀) = P₁`, line `ℓ : ax + by + c = 0` with `a² + b² = 1`
(after normalisation), and `(u, v) = P₂`. A point `(X, Y)` on the
parabola satisfies `(X − x₀)² + (Y − y₀)² = (aX + bY + c)²`. The tangent
at `(X, Y)` passes through `P₂` iff a certain quadratic in the
parabola's parameter has a real root. The two roots give two tangent
lines. The fold-line coefficients are then a rational function of the
roots (no further square roots needed beyond the discriminant).

Expected size: ~200 lines (more than HH-3 because of the case split and
the quadratic-discriminant detour). Likely 2-3 sub-PRs.

### Outlook on HH-6 (deep Beloch fold — deferred to last)

The HH-6 axiom asserts the existence of a *common tangent to two
parabolas* (focus `P₁`, directrix `ℓ₁`; focus `P₂`, directrix `ℓ₂`).
This is a degree-3 problem (Bezout: two conics in general position
have four common tangents, but the four tangent conditions reduce to
a cubic resolvent — see Alperin 2000 for the explicit reduction).
The classical construction (Beloch's square) involves a *fold-and-
mark* operation that simultaneously satisfies two parabola-tangency
constraints; in Lean this becomes a cubic-equation existence problem.

**Strategy**: defer HH-6 until HH-1 — HH-5 are all constructively in
place. Then either:

(a) Encode HH-6 as an *axiom* in the `HHAxioms` instance — explicit
    construction is `~300+` lines and requires the existence of real
    roots of certain cubics, which is the Alperin 2000 reduction.

(b) Use Mathlib's `Polynomial.Real.exists_root_of_odd_degree` to
    prove existence non-constructively. This is a 5-line argument
    *if* we accept a non-constructive witness; the explicit Beloch
    construction can be added later as an alternate.

Either way, HH-6 is the *last* HH ingredient and depends only on the
underlying cubic, not on the other six axioms. Once all seven HH
ingredients are present, the `HHAxioms` instance is mechanical
assembly, and `straight_fold_recovers_HH` (the S3 sorry, currently
sitting in PR #17915) reduces to a 10-line application combining
`straight_fold_endpoints_collinear` with the instance.

### Race-safety rationale for the doc-only S9 iteration

At the time of S9 claim (2026-05-12 ~19:35 UTC, `researcher-6`):

- Two open S8 PRs on this slug (#18192 same-coefficient midparallel;
  #18195 full-parallel translate-bisector), both build-pending,
  both ~3.5 h old, both touching `AngleTrisectionOQ05OQ04.lean`
  (Part 10 addition at the end), `state.md` (full rewrite), and
  `meta.json` (count refresh). Neither has merged.
- `gh pr list ... --search "angle-trisection-oq-05-oq-04"` returns no
  in-flight non-S8 work-units. Pristine race-check for a fresh
  S9-OBSERVE doc-only PR.
- Memory feedback (`feedback_researcher_check_next_action_pr.md`,
  `project_moderate_plus_oversubscribed_pool.md`,
  `feedback_researcher_pr_session_time_merge.md`) consistently advises
  *one productive PR then exit* on MODERATE+/RICH contested slugs.

The chosen S9 deliverable touches only `knowledge.md` (an append) on a
fresh branch off `origin/main` — **zero textual conflict** with the
two open S8 PRs and **zero touched files** in common with any other
fix/research/meta PR on this slug. The work product is a concrete,
ready-to-execute plan for the three remaining HH ingredients.

### Honest calibration (S9)

This is documentation only:

- **No new theorem, definition, or sorry** is added to any Lean file.
- **No claim** to have advanced any of the three open S-sorries.
- The value is **planning leverage**: the next agent claiming this
  slug for an ACT iteration can lift the HH-3 intersecting-case
  `bisectorIntersecting` definition and proof outline verbatim, and
  follow the Mathlib API survey to avoid re-discovering `Real.sq_sqrt`
  vs `Real.sqrt_sq` confusion.
- Expected lift for the *next* researcher: 1-2 hours of focused work
  to discharge HH-3 intersecting (instead of a half-session of
  literature lookup + API search).
- This does **not** resolve the parent OQ-04 question (axiomatic
  framework for curved-crease origami), which remains an open
  conjecture even after all seven HH ingredients are made
  constructive.
