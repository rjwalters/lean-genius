/-
# Erdős 1215, OQ-02 — reflection (complex-conjugation) symmetry of the sublevel set

Companion to `Erdos1215UnitCircleRadius.lean` (radius sandwich, compactness),
`Erdos1215UnitCircleArea.lean` (planar-area sandwich) and
`Erdos1215UnitCircleMonotone.lean` (monotonicity in the level `C`).  Those files pin the
*size* and *growth* of the closed sublevel set

    `closedLevelSet P C = {z : ℂ | ‖P.eval z‖ ≤ C}`

for a polynomial `P`.  This file records a *symmetry* of that region that is special to
the arithmetic of the OQ-02 target family: when `P` has **real coefficients**
(`P.map (starRingEnd ℂ) = P`) its sublevel set is symmetric under complex conjugation,
i.e. under reflection across the real axis.

This is a concrete manifestation of **cyclotomic root rigidity**, the theme of
`erdos-1215-oq-02`: the non-real roots of `Φₙ` (the primitive `n`-th roots of unity) come
in conjugate pairs, so the whole lemniscate geometry `{|Φₙ| ≤ C}` is forced to be
mirror-symmetric across `ℝ`.  Where a Mac Lane labyrinth may be sculpted freely, a
cyclotomic sublevel set cannot break this reflection symmetry — a genuine geometric
constraint imposed by the arithmetic of roots of unity.

## Main results

* `eval_conj` — for real-coefficient `P`, `P.eval (conj z) = conj (P.eval z)`;
* `norm_eval_conj` — hence `‖P.eval (conj z)‖ = ‖P.eval z‖`;
* `mem_closedLevelSet_conj` / `mem_levelSet_conj` — membership in the (closed/open)
  sublevel set is invariant under conjugation;
* `closedLevelSet_conj_image` / `levelSet_conj_image` — the sublevel set is exactly its own
  image under conjugation (mirror symmetry across the real axis);
* `cyclotomic_hasRealCoeffs` — every cyclotomic polynomial `Φₙ` (over `ℂ`) has real
  coefficients, via `Polynomial.map_cyclotomic`;
* `cyclotomic_closedLevelSet_conj_image` / `cyclotomic_levelSet_conj_image` — therefore the
  sublevel sets of every `Φₙ` are reflection-symmetric across the real axis.

All results are axiom-free / sorry-free.
-/

import Mathlib
import Proofs.Erdos1215UnitCircleRadius

open Complex Polynomial

namespace Erdos1215UnitCircleConjugation

open Erdos1215 Erdos1215UnitCircleRadius

variable {P : ℂ[X]}

/-- A complex polynomial has **real coefficients** when conjugating each coefficient leaves
    it unchanged: `P.map (starRingEnd ℂ) = P`.  Equivalently, all coefficients are fixed by
    complex conjugation, i.e. lie in `ℝ ⊆ ℂ`. -/
def HasRealCoeffs (P : ℂ[X]) : Prop := P.map (starRingEnd ℂ) = P

/-- **Real-coefficient polynomials intertwine evaluation with conjugation.**
    If `P` has real coefficients then `P(z̄) = \overline{P(z)}`: conjugating the argument
    conjugates the value.  This is the algebraic heart of the reflection symmetry — the map
    `starRingEnd ℂ` is a ring homomorphism fixing the coefficients of `P`. -/
theorem eval_conj (hP : HasRealCoeffs P) (z : ℂ) :
    P.eval (starRingEnd ℂ z) = starRingEnd ℂ (P.eval z) := by
  conv_lhs => rw [← hP, Polynomial.eval_map]
  exact Polynomial.eval₂_hom (starRingEnd ℂ) z

/-- **Reflection preserves the modulus of a real-coefficient polynomial.**
    `‖P(z̄)‖ = ‖P(z)‖`: the sublevel value at the reflected point equals the value at the
    original point, since conjugation is an isometry of `ℂ`. -/
theorem norm_eval_conj (hP : HasRealCoeffs P) (z : ℂ) :
    ‖P.eval (starRingEnd ℂ z)‖ = ‖P.eval z‖ := by
  rw [eval_conj hP, RCLike.norm_conj]

/-- **Membership in the closed sublevel set is conjugation-invariant.**  For real-coefficient
    `P`, `z̄ ∈ {‖P‖ ≤ C}` iff `z ∈ {‖P‖ ≤ C}`. -/
theorem mem_closedLevelSet_conj (hP : HasRealCoeffs P) (C : ℝ) (z : ℂ) :
    starRingEnd ℂ z ∈ closedLevelSet P C ↔ z ∈ closedLevelSet P C := by
  simp only [closedLevelSet, Set.mem_setOf_eq, norm_eval_conj hP]

/-- **Membership in the open Mac Lane sublevel set is conjugation-invariant.**  For
    real-coefficient `P`, `z̄ ∈ {‖P‖ < C}` iff `z ∈ {‖P‖ < C}`. -/
theorem mem_levelSet_conj (hP : HasRealCoeffs P) (C : ℝ) (z : ℂ) :
    starRingEnd ℂ z ∈ levelSet P C ↔ z ∈ levelSet P C := by
  simp only [levelSet, Set.mem_setOf_eq, norm_eval_conj hP]

/-- **The closed sublevel set is its own mirror image across the real axis.**  For
    real-coefficient `P`, `conj '' (closedLevelSet P C) = closedLevelSet P C`.  Combined with
    the radius/area sandwiches, this pins the sublevel region as a reflection-symmetric
    lemniscate interior. -/
theorem closedLevelSet_conj_image (hP : HasRealCoeffs P) (C : ℝ) :
    (starRingEnd ℂ) '' (closedLevelSet P C) = closedLevelSet P C := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_closedLevelSet_conj hP C z).mpr hz
  · intro hw
    exact ⟨starRingEnd ℂ w, (mem_closedLevelSet_conj hP C w).mpr hw, Complex.conj_conj w⟩

/-- **The open Mac Lane sublevel set is its own mirror image across the real axis.**  For
    real-coefficient `P`, `conj '' (levelSet P C) = levelSet P C`. -/
theorem levelSet_conj_image (hP : HasRealCoeffs P) (C : ℝ) :
    (starRingEnd ℂ) '' (levelSet P C) = levelSet P C := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_levelSet_conj hP C z).mpr hz
  · intro hw
    exact ⟨starRingEnd ℂ w, (mem_levelSet_conj hP C w).mpr hw, Complex.conj_conj w⟩

/-- **Every cyclotomic polynomial has real (indeed integer) coefficients.**  `Φₙ` over `ℂ`
    is the image of `Φₙ` over `ℤ` under the integer cast, whose values are fixed by complex
    conjugation; equivalently `(Φₙ).map (starRingEnd ℂ) = Φₙ` by `Polynomial.map_cyclotomic`
    (conjugation is a ring endomorphism of `ℂ`). -/
theorem cyclotomic_hasRealCoeffs (n : ℕ) :
    HasRealCoeffs (Polynomial.cyclotomic n ℂ) :=
  Polynomial.map_cyclotomic n (starRingEnd ℂ)

/-- **Cyclotomic rigidity, geometric form (closed sublevel set).**  The closed sublevel set
    `{z : ‖Φₙ(z)‖ ≤ C}` of the `n`-th cyclotomic polynomial is symmetric under reflection
    across the real axis, for every `n` and every level `C`.  Roots of unity come in
    conjugate pairs, so the cyclotomic lemniscate geometry cannot break this mirror symmetry
    — a constraint absent from a general Mac Lane labyrinth. -/
theorem cyclotomic_closedLevelSet_conj_image (n : ℕ) (C : ℝ) :
    (starRingEnd ℂ) '' (closedLevelSet (Polynomial.cyclotomic n ℂ) C)
      = closedLevelSet (Polynomial.cyclotomic n ℂ) C :=
  closedLevelSet_conj_image (cyclotomic_hasRealCoeffs n) C

/-- **Cyclotomic rigidity, geometric form (open Mac Lane sublevel set).**  The open sublevel
    set `{z : ‖Φₙ(z)‖ < C}` of `Φₙ` is symmetric under reflection across the real axis, for
    every `n` and every level `C`. -/
theorem cyclotomic_levelSet_conj_image (n : ℕ) (C : ℝ) :
    (starRingEnd ℂ) '' (levelSet (Polynomial.cyclotomic n ℂ) C)
      = levelSet (Polynomial.cyclotomic n ℂ) C :=
  levelSet_conj_image (cyclotomic_hasRealCoeffs n) C

end Erdos1215UnitCircleConjugation
