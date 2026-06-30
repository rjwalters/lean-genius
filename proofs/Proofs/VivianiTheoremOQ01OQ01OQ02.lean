import Mathlib
import Proofs.VivianiTheoremOQ01OQ01

/-
# Viviani's Theorem — OQ-01-OQ-01-OQ-02: interior witnesses of non-constancy

## Research Problem: viviani-theorem-oq-01-oq-01-oq-02

The parent `viviani-theorem-oq-01-oq-01` proves the *converse* of Viviani's
theorem as a characterisation:

    the signed distance-sum `sumDist A B C P` is independent of `P`
        ⇔   the triangle `A B C` is equilateral.

Negating the right-hand side gives only the abstract statement that for a
non-equilateral triangle the distance-sum is non-constant *somewhere in the
plane*.  This leaf sharpens the negation to a **constructive, interior**
statement, which is what one really wants geometrically:

    a non-degenerate, non-equilateral triangle has **two points in its open
    interior** with distinct distance-sums.

(On the open interior all three inward signed distances are positive, so there
the signed `sumDist` coincides with the genuine perpendicular-distance sum of
the classical statement; the witnesses are therefore witnesses for the honest
Viviani distance-sum, not merely for its signed extension.)

## The construction

The signed distance-sum is affine with constant gradient
`g = n_A + n_B + n_C` (parent lemma `sumDist_sub`).  Non-equilaterality forces
`g ≠ 0` (parent `viviani_converse` ∘ `const_iff_normalSum_zero`).  Since the two
edge vectors `B − A` and `C − A` span the plane (non-degeneracy), `g` cannot be
orthogonal to both, so `⟪g, B−A⟫ ≠ 0` or `⟪g, C−A⟫ ≠ 0`.  Perturbing the
centroid by `±1/6` of the barycentric weight along that edge produces two points
with all-positive barycentric coordinates — hence interior — whose distance-sums
differ by `⅓·⟪g, edge⟫ ≠ 0`.

We reuse the parent's plane model `ℂ`, the real inner product `rdot`, the inward
unit normals `nA, nB, nC`, and the distance-sum `sumDist`.  Verified, 0 axioms.

Tags: geometry, viviani, interior, barycentric, equilateral-triangle, non-constant
-/

namespace VivianiTheoremOQ01OQ01OQ02

open Complex VivianiTheoremOQ01OQ01

/-- A point `P` lies in the **open interior** of triangle `A B C` when it is a
strictly-positive barycentric combination of the vertices. -/
def IsInterior (A B C P : ℂ) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P = α • A + β • B + γ • C

/-- **Interior witnesses of non-constancy.**  For a non-degenerate
(`hnd`: non-zero edge determinant) and non-equilateral (`hne`) planar triangle
`A B C`, there are two points `P, Q` in the open interior whose signed
distance-sums differ.  Equivalently: the Viviani distance-sum, constant on an
equilateral triangle, is provably non-constant *already inside* any triangle that
fails to be equilateral. -/
theorem viviani_interior_witnesses {A B C : ℂ}
    (hnd : (C - B).re * (A - C).im - (C - B).im * (A - C).re ≠ 0)
    (hne : ¬ (‖C - B‖ = ‖A - C‖ ∧ ‖A - C‖ = ‖B - A‖)) :
    ∃ P Q : ℂ, IsInterior A B C P ∧ IsInterior A B C Q ∧
      sumDist A B C P ≠ sumDist A B C Q := by
  -- The non-degeneracy in the `(B−A, C−A)` basis (equal to `hnd` by a `ring`).
  have hdm : (B - A).re * (C - A).im - (B - A).im * (C - A).re ≠ 0 := by
    have h : (B - A).re * (C - A).im - (B - A).im * (C - A).re
        = (C - B).re * (A - C).im - (C - B).im * (A - C).re := by
      simp only [Complex.sub_re, Complex.sub_im]; ring
    rw [h]; exact hnd
  -- Non-equilateral ⇒ the gradient (normal sum) is non-zero.
  have hg : nA A B C + nB A B C + nC A B C ≠ 0 := by
    intro h0
    exact hne ((viviani_converse hnd).mp
      ((const_iff_normalSum_zero (nA A B C) (nB A B C) (nC A B C) B C A).mpr h0))
  set g : ℂ := nA A B C + nB A B C + nC A B C with hgdef
  -- The gradient is not orthogonal to both spanning edges.
  have hsplit : rdot g (B - A) ≠ 0 ∨ rdot g (C - A) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hg
    have e1 : g.re * (B - A).re + g.im * (B - A).im = 0 := h1
    have e2 : g.re * (C - A).re + g.im * (C - A).im = 0 := h2
    have hre : g.re = 0 := by
      have hh : g.re * ((B - A).re * (C - A).im - (B - A).im * (C - A).re) = 0 := by
        linear_combination (C - A).im * e1 - (B - A).im * e2
      exact (mul_eq_zero.mp hh).resolve_right hdm
    have him : g.im = 0 := by
      have hh : g.im * ((B - A).re * (C - A).im - (B - A).im * (C - A).re) = 0 := by
        linear_combination (B - A).re * e2 - (C - A).re * e1
      exact (mul_eq_zero.mp hh).resolve_right hdm
    exact Complex.ext (hre.trans Complex.zero_re.symm) (him.trans Complex.zero_im.symm)
  rcases hsplit with hd | hd
  · -- perturb the `A`/`B` barycentric weights along edge `B − A`
    refine ⟨(1/6 : ℝ) • A + (1/2 : ℝ) • B + (1/3 : ℝ) • C,
            (1/2 : ℝ) • A + (1/6 : ℝ) • B + (1/3 : ℝ) • C, ?_, ?_, ?_⟩
    · exact ⟨1/6, 1/2, 1/3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨1/2, 1/6, 1/3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    · intro hEq
      have key : sumDist A B C ((1/6 : ℝ) • A + (1/2 : ℝ) • B + (1/3 : ℝ) • C)
            - sumDist A B C ((1/2 : ℝ) • A + (1/6 : ℝ) • B + (1/3 : ℝ) • C)
          = rdot g (((1/6 : ℝ) • A + (1/2 : ℝ) • B + (1/3 : ℝ) • C)
              - ((1/2 : ℝ) • A + (1/6 : ℝ) • B + (1/3 : ℝ) • C)) := by
        rw [hgdef]
        exact sumDist_sub (nA A B C) (nB A B C) (nC A B C) B C A _ _
      rw [hEq, sub_self] at key
      have hPQ : rdot g (((1/6 : ℝ) • A + (1/2 : ℝ) • B + (1/3 : ℝ) • C)
            - ((1/2 : ℝ) • A + (1/6 : ℝ) • B + (1/3 : ℝ) • C))
          = (1/3 : ℝ) * rdot g (B - A) := by
        simp only [rdot, Complex.real_smul, Complex.sub_re, Complex.sub_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im]; ring
      rw [hPQ] at key
      exact hd (by linarith)
  · -- perturb the `A`/`C` barycentric weights along edge `C − A`
    refine ⟨(1/6 : ℝ) • A + (1/3 : ℝ) • B + (1/2 : ℝ) • C,
            (1/2 : ℝ) • A + (1/3 : ℝ) • B + (1/6 : ℝ) • C, ?_, ?_, ?_⟩
    · exact ⟨1/6, 1/3, 1/2, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨1/2, 1/3, 1/6, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    · intro hEq
      have key : sumDist A B C ((1/6 : ℝ) • A + (1/3 : ℝ) • B + (1/2 : ℝ) • C)
            - sumDist A B C ((1/2 : ℝ) • A + (1/3 : ℝ) • B + (1/6 : ℝ) • C)
          = rdot g (((1/6 : ℝ) • A + (1/3 : ℝ) • B + (1/2 : ℝ) • C)
              - ((1/2 : ℝ) • A + (1/3 : ℝ) • B + (1/6 : ℝ) • C)) := by
        rw [hgdef]
        exact sumDist_sub (nA A B C) (nB A B C) (nC A B C) B C A _ _
      rw [hEq, sub_self] at key
      have hPQ : rdot g (((1/6 : ℝ) • A + (1/3 : ℝ) • B + (1/2 : ℝ) • C)
            - ((1/2 : ℝ) • A + (1/3 : ℝ) • B + (1/6 : ℝ) • C))
          = (1/3 : ℝ) * rdot g (C - A) := by
        simp only [rdot, Complex.real_smul, Complex.sub_re, Complex.sub_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im]; ring
      rw [hPQ] at key
      exact hd (by linarith)

/-- **Restatement.**  The Viviani signed distance-sum of a non-degenerate,
non-equilateral triangle is not a constant function on its interior: there is no
real number it equals at every interior point. -/
theorem sumDist_not_constant_on_interior {A B C : ℂ}
    (hnd : (C - B).re * (A - C).im - (C - B).im * (A - C).re ≠ 0)
    (hne : ¬ (‖C - B‖ = ‖A - C‖ ∧ ‖A - C‖ = ‖B - A‖)) :
    ¬ ∃ k : ℝ, ∀ P : ℂ, IsInterior A B C P → sumDist A B C P = k := by
  rintro ⟨k, hk⟩
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := viviani_interior_witnesses hnd hne
  exact hPQ ((hk P hP).trans (hk Q hQ).symm)

end VivianiTheoremOQ01OQ01OQ02
