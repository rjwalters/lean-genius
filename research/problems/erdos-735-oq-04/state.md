# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-10): OBSERVE survey for `erdos-735-oq-04` — the seeker-extracted child of the verified gallery entry `erdos-735` ("Magic Configurations"). Parent's `conclusion.openQuestions[3]`:

> Does the classification extend to configurations where the equal-sum constraint is imposed on k-flats instead of lines?

This iteration produces:

- `problem.md` — formal Lean target signatures (`PointConfigD`, `WeightingD`, `ConfigKFlat`, `IsKFlatMagic`); S2-S7 decomposition; hierarchy table of cases by $(d, k)$.
- `knowledge.md` — recap of ABKPR's 4 classes; concrete tetrahedron/octahedron/cube examples for $k=2, d=3$; combinatorial counting (general position is always $k$-flat magic via uniform weights); Mathlib gap analysis.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/erdos-735-oq-04.json` — gallery JSON.

No Lean changes.

## Active Approach

**The $k$-flat extension is structurally richer than the parent**:

- **Trivial limits**: $k = 0$ (every config is 0-flat magic) and $k = d$ (single ambient flat is trivially magic).
- **Parent reduction**: $d = 2, k = 1$ recovers exactly the parent's `IsMagic` (definitional).
- **Higher ambient dim $d \ge 3$, $k = 1$**: extends parent's 4 classes; conjecturally similar form.
- **Higher flats $k \ge 2$**: introduces **new magic configurations** — regular convex polytopes (tetra, octa, cube) are $(d-1)$-flat magic via uniform weighting. This was NOT a class in the parent's 4-fold classification.

### Concrete polytope examples (S6 deliverable)

- **Tetrahedron** ($n = 4, d = 3, k = 2$): 4 triangular faces × 3 vertices each = 12 incidences; uniform $w_i = 1$ gives each face-sum = 3.
- **Octahedron** ($n = 6, d = 3, k = 2$): 8 triangular faces × 3 vertices each = 24 incidences; uniform $w_i = 1$ gives face-sum = 3.
- **Cube** ($n = 8, d = 3, k = 2$): 6 face planes × 4 vertices each = 24 incidences; uniform $w_i = 1$ gives face-sum = 4.

These are all $(d-1)$-flat-magic and provide a *new* class beyond the parent's 4.

### Higher-dim classification (S5 conjecture)

The author's conjecture: for $\mathbb{R}^d$ with $k = 1$, the parent's 4 classes generalise as:
1. All collinear (on a 1-flat).
2. General position (no 3 collinear in any 1-flat).
3. Near-pencil ($n - 1$ on a 1-flat, 1 off).
4. Some $d$-dimensional analogue of "triangle + bisectors + incenter".

For $k \ge 2$, the classification likely has 4–6 classes including the new "regular polytope" family.

## Blockers

None mathematical for S1. Practical:

- **ABKPR 2008 absent from Mathlib**: parent axiomatises; reuse for this OQ.
- **Higher-flat classification absent from published literature**: S5 axiom is genuinely open.
- **`status: "axiomatized"` mandatory**: ABKPR alone forces this.

## Next Action

**S2 (any researcher)**: Define `PointConfigD`, `WeightingD`, `ConfigKFlat`, `IsKFlatMagic` in `proofs/Proofs/Erdos735OQ04.lean`. Approach: parameterise parent's definitions on $(d, k)$, using `EuclideanSpace ℝ (Fin d)` and `AffineSubspace`. Prove trivial cases $k = 0, k = d$.

Concrete plan:

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Proofs.Erdos735Problem  -- parent

namespace Erdos735OQ04

def PointConfigD (d : ℕ) := Finset (EuclideanSpace ℝ (Fin d))

def WeightingD {d : ℕ} (P : PointConfigD d) := {w : P → ℝ // ∀ p, w p > 0}

def ConfigKFlat {d : ℕ} (k : ℕ) (P : PointConfigD d) :=
  { F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) //
    F.direction.toSubmodule.rank = k ∧ (P.filter (· ∈ F)).card ≥ k + 1 }

def kFlatSum {d k : ℕ} (P : PointConfigD d) (w : WeightingD P)
    (F : ConfigKFlat k P) : ℝ := ...

def IsKFlatMagic {d : ℕ} (k : ℕ) (P : PointConfigD d) : Prop := ...

theorem zero_flat_magic_trivial : IsKFlatMagic 0 P := ...
theorem ambient_flat_magic_trivial : IsKFlatMagic d P := ...
theorem oneflat_eq_parent : IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := ...

end Erdos735OQ04
```

Expected ~50 Lean lines, ~3 sorries on the trivial-case theorems (mechanical to discharge).

**S3** — S4: prove trivial cases and parent reduction.
**S5** — axiomatise the conjectured higher-dim classification.
**S6** — `native_decide` certificates for tetrahedron / octahedron / cube examples.
**S7** — gallery JSON with `status: "axiomatized"`.

## Honesty

This S1 OBSERVE is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry/axiom deltas
- 3 markdown files
- 1 gallery JSON

The higher-flat extension is **research-level open**. The polytope examples (S6) show the higher-dim classification has MORE classes than the parent's 4-fold theorem, suggesting the question is genuinely richer.

Future Lean entry: `status: "axiomatized"`.
