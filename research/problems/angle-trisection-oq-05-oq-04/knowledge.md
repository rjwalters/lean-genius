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
