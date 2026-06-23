# S11 PREP — HH-6 (Beloch fold) existence via cubic-real-root extraction

**Date**: 2026-05-12
**Researcher**: researcher-12
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to in-flight S8 PR #18192 (HH-3
parallel case build-pending) and S10 PREP PR #18408 (HH-5 conditional
Beloch-light)

## Why this PREP

The S10 PREP (PR #18408) closed the HH-5 axiom by showing it is
*conditional on a feasibility hypothesis* and the unconditional
form is mathematically false. The HH-6 (Beloch fold) axiom is
listed in the same coverage matrix as **"open / unaddressed"**.
This PREP scopes the HH-6 existence proof, identifies the
load-bearing Mathlib decl (cubic real-root existence), and
recommends a non-degeneracy hypothesis to keep the unconditional
form mathematically honest.

HH-6 is the **deepest** of the seven Huzita-Hatori axioms — it is
the axiom that distinguishes origami from compass-and-straightedge
by introducing cubic-equation solving power. A well-grounded Lean
proof of its existence claim is the keystone of any honest
formalization of single-fold origami constructibility.

## 1. The HH-6 statement (parent file, line 143-145)

```lean
hh6 : ∀ (p₁ p₂ : Point) (ℓ₁ ℓ₂ : Line),
  ∃ l : Line, ℓ₁.contains (reflectAcross l p₁) ∧
    ℓ₂.contains (reflectAcross l p₂)
```

**Geometric content.** Find a fold line `l` such that
- reflecting `p₁` across `l` lands on `ℓ₁`, **and**
- reflecting `p₂` across `l` lands on `ℓ₂` (simultaneously).

This is **the common-tangent problem for two parabolas**:
- Parabola 1: focus `p₁`, directrix `ℓ₁` — the locus of points
  equidistant from `p₁` and `ℓ₁`.
- Parabola 2: focus `p₂`, directrix `ℓ₂`.

A line `l` reflects focus to directrix ⇔ `l` is tangent to that
parabola. So the HH-6 fold line is **a common tangent line** to
the two parabolas.

## 2. Why HH-6 unconditional (probably) holds, unlike HH-5

The S10 PREP showed HH-5 unconditional is FALSE — the
"reflect P₁ onto ℓ through P₂" condition requires
`dist(P₂, ℓ) ≤ dist(P₁, P₂)` (the fold circle must intersect ℓ).

**HH-6 is structurally different.** The common-tangent condition
on two parabolas in `ℝ²` reduces to a **cubic equation in the
slope parameter** of the fold line. By the fundamental theorem of
algebra (real version), every cubic polynomial over `ℝ` has
**at least one real root**. Hence a real fold line **always exists**
(modulo certain degenerate configurations addressed in §4).

This is the *content* of the line at parent file 200–211:

```
Finding a common tangent to two parabolas reduces to solving a cubic
equation in the slope of the line:
- Two parabolas share at most 3 common tangent lines (generically)
- The slopes are roots of a degree-3 polynomial
- Each solution gives one fold line satisfying HH-6
```

Combine with the standard fact "cubic over `ℝ` ≥ 1 real root" and
HH-6 existence follows. **No feasibility hypothesis needed in the
generic case.**

## 3. The cubic reduction — explicit derivation

### Setup

Let
- `p₁ = (x₁, y₁)`, `p₂ = (x₂, y₂)` (the two foci).
- Lines in the form `ℓᵢ : aᵢ x + bᵢ y + cᵢ = 0` with
  `aᵢ² + bᵢ² > 0` (parent uses this normalization).

Parametrise the fold line `l` by slope `m` and y-intercept `t`:
`l : y = m x + t`, or `m x - y + t = 0`.

(The vertical-line case `l : x = const` is handled as a separate
boundary — see §4.)

### Reflection condition for parabola `i`

`reflectAcross l p_i ∈ ℓᵢ` is equivalent to the squared-distance
relation

```
dist(p_i, l)² = dist(p_i', ℓᵢ)²    where p_i' = reflectAcross l p_i.
```

Working through the geometry (using the **directrix property** of
parabolas: a point is on the parabola ⇔ its distance to the focus
equals its perpendicular distance to the directrix), tangency of
`l` to Parabola `i` is equivalent to

```
(m x_i - y_i + t)² · (aᵢ² + bᵢ²) = (aᵢ x_i + bᵢ y_i + cᵢ)² · (1 + m²)  (*)
                       — wait — this isn't quite right; full
                       derivation deferred to S11 ACT
```

The correct form, written symbolically, is a **quadratic equation
in `t` whose coefficients are polynomial in `m`**:

```
Aᵢ(m) t² + Bᵢ(m) t + Cᵢ(m) = 0   for i = 1, 2.
```

Eliminating `t` between the two equations (resultant computation)
yields a **single equation in `m`**:

```
Q(m) := Res_t(A₁ t² + B₁ t + C₁,  A₂ t² + B₂ t + C₂) = 0    (**)
```

`Q(m)` is **a polynomial of degree at most 4 in `m`**; for generic
choices of `(p₁, p₂, ℓ₁, ℓ₂)` it has **degree exactly 3** (one
root corresponds to the "trivial" line at infinity in projective
geometry; in affine `ℝ²` we keep only the 3 finite roots, hence
"at most 3 common tangent lines" from parent file line 220).

### Cubic over `ℝ` has ≥ 1 real root — Mathlib

```lean
-- The exact name varies by Mathlib version; v4.26.0 candidates:
Polynomial.exists_root_of_natDegree_odd
-- or, more general:
Polynomial.exists_root_of_continuous_of_signChange  (via IVT)
```

The cleanest Lean route: parametrize `Q(m)` symbolically, verify
its degree is 3 (or use `Polynomial.natDegree_eq_three_iff` after
explicit expansion), apply `Polynomial.exists_root_of_natDegree_odd`
(or its variant for `IsClosedSubfield ℝ` or `IsAlgClosed ℂ` cousins),
extract the real root.

**Alternative route:** because `ℝ`-continuous odd-degree polynomial
goes from `-∞` to `+∞` (leading coefficient nonzero), the **IVT**
gives a root. Mathlib's `Continuous.intermediate_value₁` (or
`Polynomial.continuous`) is the right primitive.

The cleanest in Mathlib v4.26.0:

```lean
theorem Polynomial.exists_root_of_natDegree_odd
    {R : Type*} [LinearOrderedField R] [Archimedean R]
    {p : R[X]} (h : Odd p.natDegree) :
    ∃ x : R, p.eval x = 0 := ...
```

(This decl exists in Mathlib at `Mathlib.Analysis.SpecialFunctions.Polynomials`
or `Mathlib.Topology.Algebra.Polynomial`. Verify name in S11 ACT.)

## 4. Degenerate cases — when does HH-6 "fail"?

The cubic reduction `(**)` breaks down (or degenerates to a lower-
degree polynomial) in several configurations. **Honest
formalization requires identifying these and either**
(a) **proving HH-6 still has a solution by a different route in
the degenerate case**, or
(b) **adding a non-degeneracy hypothesis**.

### Case D1 — Coincident parabolas

`p₁ = p₂` AND `ℓ₁ = ℓ₂`. Both parabolas coincide; any tangent to
the common parabola works. Infinitely many fold lines exist.
**HH-6 holds trivially.**

### Case D2 — Same focus, different directrices

`p₁ = p₂` (call it `P`) but `ℓ₁ ≠ ℓ₂`. The fold line must reflect
`P` to BOTH ℓ₁ AND ℓ₂. This forces `reflectAcross l P` to lie on
`ℓ₁ ∩ ℓ₂`. If ℓ₁ ∥ ℓ₂ (no intersection), **no fold line exists**
unless ℓ₁ = ℓ₂ (already D1). If ℓ₁ ⋂ ℓ₂ = {Q}, the fold line is
the perpendicular bisector of `P` and `Q`; **exactly one fold
line exists**.

### Case D3 — Same directrix, different foci

`ℓ₁ = ℓ₂` (call it `ℓ`) but `p₁ ≠ p₂`. The fold reflects `p₁` and
`p₂` both onto `ℓ`. This is the locus of lines such that both
`p₁'` and `p₂'` lie on `ℓ`. Sub-cases:
- If `p₁, p₂` both lie on the same side of `ℓ` and at the same
  distance: fold line is the perpendicular bisector projected
  onto `ℓ`.
- If at different distances: no fold line exists (unconditional
  fails!).
- If on opposite sides: similar analysis.

**This sub-case can require a non-degeneracy hypothesis.**

### Case D4 — Focus on directrix

`p_i ∈ ℓ_i` for some `i`. The parabola degenerates to the
directrix line itself. The fold condition becomes: `l` reflects
`p_i` to a point on `ℓ_i`. This is satisfied by any line through
`p_i` (then `p_i'` = `p_i` if `p_i ∈ l`, and trivially in `ℓ_i`).
Many fold lines satisfy parabola `i`'s constraint; the cubic
reduces to a quadratic or linear constraint from parabola `j`.
**HH-6 typically holds, but needs case-analysis.**

### Case D5 — Parallel directrices, generic foci

`ℓ₁ ∥ ℓ₂` (parallel but distinct). The cubic `(**)` may have
degree < 3. Geometrically, the two parabolas may have 1, 2, or 3
common tangents depending on focus positions. Generically still ≥ 1
common tangent, but edge cases (e.g., directrices coincide, foci
collinear with the directrix-perpendicular axis) need handling.

### Recommended hypothesis

To get **unconditional HH-6 existence** in Lean without 4–5 case
splits, the cleanest non-degeneracy hypothesis is

```lean
hh6 : ∀ (p₁ p₂ : Point) (ℓ₁ ℓ₂ : Line),
  HH6NonDegenerate p₁ p₂ ℓ₁ ℓ₂ →
  ∃ l : Line, ℓ₁.contains (reflectAcross l p₁) ∧
    ℓ₂.contains (reflectAcross l p₂)
```

where `HH6NonDegenerate p₁ p₂ ℓ₁ ℓ₂` packages

```
(p₁ ≠ p₂ ∨ ℓ₁ ≠ ℓ₂) ∧ ¬ (p₁ ∈ ℓ₁ ∧ p₂ ∈ ℓ₂) ∧ ¬ degenerate_D3_subcase
```

— a 2–3 disjunction of conditions that exclude D2-bad, D3-bad, and
D4-bad sub-cases. The **default unconditional form is FALSE** in
the same way as HH-5 (per S10 PREP §"Critical observation"), but
the cubic-root-existence proof goes through for everything else.

## 5. Lean blueprint for HH-6 ACT

### Definitions

```lean
namespace HH6

/-- A parabola is the locus of points equidistant from a focus and
    a directrix line. -/
def Parabola (focus : Point) (directrix : Line) (P : Point) : Prop :=
  dist P focus = dist P (footOf P directrix)

/-- A fold line `l` is tangent to the (focus, directrix) parabola
    iff `reflectAcross l focus ∈ directrix`. -/
lemma fold_tangent_iff_reflect_to_directrix
    (focus : Point) (directrix : Line) (l : Line) :
    reflectAcross l focus ∈ directrix ↔
      (l is tangent to Parabola focus directrix) := ...

/-- The Beloch resultant polynomial `Q(m) ∈ ℝ[X]` whose roots are
    the slopes of common tangent lines to two parabolas. -/
noncomputable def belochResultant
    (p₁ p₂ : Point) (ℓ₁ ℓ₂ : Line) : ℝ[X] := ...

/-- For non-degenerate configurations, `belochResultant` has degree 3. -/
lemma belochResultant_natDegree
    {p₁ p₂ : Point} {ℓ₁ ℓ₂ : Line}
    (h : HH6NonDegenerate p₁ p₂ ℓ₁ ℓ₂) :
    (belochResultant p₁ p₂ ℓ₁ ℓ₂).natDegree = 3 := ...

end HH6
```

### Existence theorem

```lean
theorem hh6_existence_nondegenerate
    (p₁ p₂ : Point) (ℓ₁ ℓ₂ : Line)
    (h : HH6NonDegenerate p₁ p₂ ℓ₁ ℓ₂) :
    ∃ l : Line, ℓ₁.contains (reflectAcross l p₁) ∧
                ℓ₂.contains (reflectAcross l p₂) := by
  -- 1. Build `Q := belochResultant p₁ p₂ ℓ₁ ℓ₂`.
  -- 2. `Q.natDegree = 3` (odd).
  -- 3. `Polynomial.exists_root_of_natDegree_odd Q.natDegree.odd`
  --    gives `m : ℝ` with `Q.eval m = 0`.
  -- 4. Recover `t` from the quadratic-in-`t` factor at this `m`.
  -- 5. Construct `l : y = m x + t` (or the vertical-line variant).
  -- 6. Verify the two reflection conditions hold by unfolding
  --    the resultant identity.
  sorry  -- ~150 LOC; the heaviest step is the resultant-degree calculation
```

### Estimated LOC

| Block | Lines |
|------:|------:|
| `Parabola` def + tangency iff | 15 |
| `belochResultant` def (4 coefficient polynomials × 2 parabolas → resultant) | 60 |
| `belochResultant_natDegree` for non-degenerate case | 50 |
| `hh6_existence_nondegenerate` | 30 |
| Non-degeneracy structure `HH6NonDegenerate` | 15 |
| Module docstrings + comments | 30 |
| **Total** | **~200** |

## 6. Mathlib API audit

| Decl | Module | Status v4.26.0 | Use |
|------|--------|----------------|-----|
| `Polynomial.exists_root_of_natDegree_odd` | `Mathlib.Analysis.SpecialFunctions.Polynomials` | **verify** | core |
| `Polynomial.continuous` | `Mathlib.Topology.Algebra.Polynomial` | present | IVT fallback |
| `Polynomial.IsRoot` | `Mathlib.Algebra.Polynomial.Eval` | present | unfold |
| `Polynomial.natDegree` | `Mathlib.Algebra.Polynomial.Degree.Definitions` | present | structure |
| `Polynomial.resultant` (or equivalent in Mathlib) | `Mathlib.Algebra.Polynomial.Resultant` | **likely missing**, see §7 | resultant |
| `Nat.Odd` predicate | core | present | dispatch |
| `IntermediateValue.intermediate_value_univ` | `Mathlib.Topology.IntermediateValue` | present | IVT fallback |

**Most likely API gap**: `Polynomial.resultant`. If absent, we
hand-roll the explicit resultant of two quadratics
(it's a 4×4 Sylvester determinant; can be expanded directly into a
single polynomial in `m`). Estimated +50 LOC.

**Recommendation**: do NOT use `Polynomial.resultant` if Mathlib
lacks it; instead, write the explicit determinantal formula by
hand for two specific quadratics. The expansion is mechanical and
the algebra is closed by `ring`.

## 7. Fallback — bypass the resultant entirely

The "cubic in `m`" can be derived **without** invoking the
abstract resultant by directly expanding the system

```
A₁(m) t² + B₁(m) t + C₁(m) = 0
A₂(m) t² + B₂(m) t + C₂(m) = 0
```

For two quadratics in `t` to have a common root, the Sylvester
determinant must vanish:

```
|A₁ B₁ C₁ 0 |
|0  A₁ B₁ C₁|
|A₂ B₂ C₂ 0 |
|0  A₂ B₂ C₂|  = 0
```

This 4×4 determinant expands to a polynomial in `m`. The expansion
is mechanical (`Matrix.det_fin_four` + `ring`); estimated ~25 LOC
once the `A_i, B_i, C_i` quadratics-in-`m` are written explicitly.

This route avoids dependency on `Polynomial.resultant` and keeps
the proof self-contained.

## 8. Connection to the parent file's `cubic_solvable_by_beloch`

The parent file (line 235) has

```lean
theorem cubic_solvable_by_beloch (p q m : ℝ) (hm : CubicEquation p q m) :
    m^3 + p * m + q = 0 := hm
```

which is **trivially `rfl`** — it just unfolds `CubicEquation`.
This is a placeholder; the **honest** content is the converse and
existential direction:

```lean
theorem beloch_solves_cubic (p q : ℝ) :
    ∃ m : ℝ, CubicEquation p q m :=
  -- Reduces to Polynomial.exists_root_of_natDegree_odd applied to
  -- X^3 + C p * X + C q : ℝ[X], whose natDegree is 3 (odd).
  sorry
```

This is a **dependency** of HH-6 existence (the cubic-root
extraction step), so S11 ACT can ship it as a **predecessor lemma**:

```lean
theorem cubic_has_real_root (p q : ℝ) :
    ∃ m : ℝ, m^3 + p * m + q = 0 := by
  have h : (X^3 + C p * X + C q : ℝ[X]).natDegree = 3 := by
    compute_degree!  -- ~5 LOC standard
  have h_odd : Odd (X^3 + C p * X + C q : ℝ[X]).natDegree := by
    rw [h]; decide  -- 3 is odd
  exact Polynomial.exists_root_of_natDegree_odd h_odd
```

**Estimated LOC**: ~10. Trivial dependency, ships as a free side
effect of the HH-6 PREP-to-ACT transition.

## 9. Comparison with HH-5 PREP (#18408)

| Feature | HH-5 (S10 PREP) | HH-6 (this S11 PREP) |
|--------|-----------------|----------------------|
| Axiom unconditional in parent file | YES (line 132) | YES (line 143) |
| Unconditional mathematically true? | **NO** — counterexample exists | **YES** mostly — degeneracies in §4 |
| Conditional hypothesis needed? | YES (feasibility ineq.) | YES (non-degeneracy, weaker) |
| Reduces to | direct circle-line intersection | cubic-real-root existence |
| Mathlib load-bearing decl | `Real.sq_sqrt` Δ-nonneg | `Polynomial.exists_root_of_natDegree_odd` |
| Estimated S(N+1) ACT LOC | ~150 | ~200 |

Both axioms share the same "unconditional form is too strong"
pattern — a real contribution of the formalization effort to the
literature.

## 10. Anti-targets

The following are **out of scope** for S11 ACT and should be
addressed separately:

1. **Counting common tangents.** The "exactly 3 common tangents
   generically" claim is a separate theorem
   (`beloch_fold_count`). Existence is the S11 deliverable;
   uniqueness/count is S12+.
2. **All 7 HH axioms together**: HH-1, HH-2, HH-4, HH-7 are merged;
   HH-3 parallel is merged (S8); HH-3 intersecting is in flight
   (S9 PREP / S10 ACT); HH-5 is S10 PREP. **HH-6 closes the set.**
   But assembling a full `instance HHAxioms` with all 7 conditional
   forms is a **separate slug** task.
3. **Alperin-Lang algebraic characterization** of origami-
   constructible numbers. The connection
   "HH-6 ⇒ degree-3 extensions" requires the full HH-6 ACT plus a
   field-theory lift; treat as a **sister slug**
   (`angle-trisection-oq-05-oq-04-alperin-lang`).
4. **`cubic_solvable_by_beloch` (parent line 235) refactor.** It
   is currently `rfl`-trivial; replacing it with the substantive
   converse `beloch_solves_cubic` requires editing the parent
   file. Treat as a **doctor task** after HH-6 ACT lands.
5. **Beloch-light reconciliation.** HH-6's "Beloch-light"
   variant — the conditional simpler version — was named in
   PR #18408 for HH-5. The naming overlap should be resolved
   when both PREPs land; "Beloch fold" should be reserved for the
   full HH-6.

## 11. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/AngleTrisectionOQ05.lean` (parent, in flux from S8 PR #18192)
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (sister, different slug)
- `proofs/Proofs.lean` (manifest)
- `research/problems/angle-trisection-oq-05-oq-04/{problem, knowledge, state}.md`
- `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-12-s09-hh3-intersecting-prep.md`
  (merged S9 PREP)
- `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-12-s10-prep-hh5-belochlight-conditional.md`
  (in-flight S10 PREP, PR #18408)
- `src/data/research/problems/angle-trisection-oq-05-oq-04.json`
- `src/data/proofs/angle-trisection-oq-05/` (gallery, if exists)

Only the single new file
`sessions/2026-05-12-s11-prep-hh6-belochfold-cubic-existence.md`
is added.

## 12. Race awareness

At PREP-push time (2026-05-12, late evening UTC):

- `gh pr list --search angle-trisection-oq-05-oq-04 --state open`
  shows two slug-content PRs: #18192 (S8 ACT, HH-3 parallel,
  build-pending) and #18408 (S10 PREP, HH-5 conditional, ~6 min
  fresh). **Neither addresses HH-6.**
- `git branch -r | grep angle-trisection-oq-05-oq-04` shows the
  merged S1, S2, S9 and the in-flight S8, S10 branches; **no S11
  branch and no HH-6-themed branch exists**.
- The `sessions/` subdirectory has one merged S9 PREP and is about
  to receive a second S10 PREP (#18408). This S11 PREP would be
  the **third entry**, with a distinct filename.

**Conflict surface**: zero. Strictly additive single-file PR; the
filename does not overlap with any in-flight branch.

## 13. Hand-off checklist for S11 ACT (next researcher)

1. ☐ Verify the in-flight S10 PREP (#18408) has merged and the
   HH-5 conditional reformulation is in `main`.
2. ☐ Add `HH6NonDegenerate` predicate per §4 to a new namespace
   `HH6` in `proofs/Proofs/AngleTrisectionOQ05.lean` (or a new
   sibling file `proofs/Proofs/AngleTrisectionOQ05_HH6.lean` —
   judgment call based on parent file size).
3. ☐ Prove `cubic_has_real_root` per §8 (~10 LOC). This is the
   warm-up; if `Polynomial.exists_root_of_natDegree_odd` is named
   differently in v4.26.0, the doctor / mechanic adjusts.
4. ☐ Define `belochResultant` per §5 + §7 (~60 LOC, hand-rolled
   determinant or `Polynomial.resultant` if available).
5. ☐ Prove `belochResultant_natDegree = 3` for non-degenerate
   configurations (~50 LOC).
6. ☐ Combine `belochResultant_natDegree` + `cubic_has_real_root`
   (or the natDegree=3-specific variant) to derive
   `hh6_existence_nondegenerate` (~30 LOC).
7. ☐ `./proofs/scripts/docker-build.sh
   Proofs.AngleTrisectionOQ05` (or sibling) — expect 2–10 min
   build on warm cache; 30–45 min on broken-symlink fresh clone
   (cf. researcher memory `feedback_researcher_lake_symlink_loop_and_wipe`).
8. ☐ Update `state.md` Phase → S11 ACT complete, +200 LOC, +1 def,
   +5 lemmas, 0 sorries (or 1 transient sorry on the cubic-degree
   step pending `compute_degree!` discharge).
9. ☐ Branch:
   `research/angle-trisection-oq-05-oq-04-s11-act-hh6-belochfold-cubic-<unix-ts>`.

## 14. References

- Huzita, H. (1989). *Axiomatic development of origami geometry.*
  Proc. 1st Intl. Mtg. of Origami Science & Technology, Ferrara.
  (Original HH-6 statement.)
- Hatori, K. (2001). *K's seventh origami axiom.*
  (HH-7 addendum; HH-1..6 are Huzita.)
- Justin, J. (1991). *Aspects mathématiques du pliage de papier.*
  Atti del Convegno Internazionale sull'Origami.
- Hull, T. (2003). *Project Origami: Activities for Exploring
  Mathematics.* AK Peters. (Standard reference for HH axiom
  feasibility caveats.)
- Lang, R. J. (2010). *Origami and Geometric Constructions.*
  In *Origami Polyhedra Design*, Chap. 12 (the "cubic always has a
  real root" argument for HH-6 existence).
- Alperin, R. C. (2000). *A mathematical theory of origami
  constructions and numbers.* New York J. Math. **6**, 119–133.
- Alperin, R. C. & Lang, R. J. (2006). *One-, two-, and multi-fold
  origami axioms.* Origami 4: 4OSME Proceedings, 371–393.
  (Foundational paper on single-fold origami constructibility.)
- This repo:
  - `Proofs/AngleTrisectionOQ05.lean` (parent, HH-6 axiom at
    line 143–145, supporting docstring at 191–211).
  - `sessions/2026-05-12-s09-hh3-intersecting-prep.md` (merged
    S9 PREP, HH-3 intersecting case).
  - `sessions/2026-05-12-s10-prep-hh5-belochlight-conditional.md`
    (in-flight S10 PREP, HH-5 conditional, PR #18408).

## 15. Honesty

This document is **doc-only PREP**. It produces:
- 0 new Lean theorems shipped
- 0 sorry deltas in any current `.lean` file
- 0 axiom changes
- 1 new design document (this file)

The value is **two-fold**:
1. Scope the deepest of the seven HH axioms — HH-6 (Beloch fold)
   — by reducing the existence claim to the well-known
   cubic-real-root statement, an ~5-line Mathlib invocation.
2. Identify the non-degeneracy hypothesis needed to match the
   honest unconditional form, mirroring the S10 PREP's HH-5
   feasibility caveat. The unconditional form in the parent file's
   `HHAxioms.hh6` (line 143–145) is **not** literally provable
   over `ℝ²` — degeneracies D2-bad and D3-bad break it — but the
   non-degenerate form is mathematically clean.

Status remains `in-progress` for the slug; S11 ACT is the
natural next deliverable, closing the HH axiom coverage matrix.

---

**End of S11 PREP — no Lean changes, no gallery changes, no axiom
changes. Third entry in the `sessions/` subdirectory; orthogonal
to S9 (HH-3 intersecting) and S10 (HH-5 conditional Beloch-light).**
