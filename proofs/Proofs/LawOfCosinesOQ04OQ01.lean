import Mathlib

/-
# Law of Cosines — OQ-04-OQ-01: Stewart's Theorem via Inner Products

## Research Problem: law-of-cosines-oq-04-oq-01

The parent file `LawOfCosinesOQ04.lean` derives Stewart's theorem at the *scalar*
level: it takes the law-of-cosines equations for the two sub-triangles as
hypotheses (with an abstract cosine parameter `t`) and eliminates the cosines
algebraically.  The vertices `A, B, C` never appear as actual geometric objects.

This file grounds Stewart's theorem in genuine geometry: the vertices are points
`A, B, C` in an arbitrary real inner product space, the cevian foot is the
affine combination `D = (1 - s) • B + s • C`, and all lengths are honest norms.
The abstract cosine `t` of the parent file is replaced by the real inner product
`⟪A - B, A - C⟫`.

## Main results

* `stewart_cevian_inner` — the coordinate-free Stewart / cevian-length identity:
    ‖A - D‖² = (1 - s)‖A - B‖² + s‖A - C‖² − s(1 - s)‖B - C‖²
  This is a single bilinear identity, valid in any real inner product space and
  in any dimension.

* `stewarts_theorem_inner` — the classical form `b²m + c²n = a(d² + mn)` with
    a = ‖B - C‖,  m = s·a,  n = (1 - s)·a,  b = ‖A - C‖,  c = ‖A - B‖,  d = ‖A - D‖,
  recovered from the master identity.  Note `m + n = a` automatically.

* `apollonius_median_inner` — the median special case `s = 1/2` (Apollonius'
  theorem): ‖A - midpoint(B,C)‖² = ½‖A - B‖² + ½‖A - C‖² − ¼‖B - C‖².

* `angle_bisector_length_inner` — the internal-bisector length formula
    (b + c)²‖A - D‖² = bc((b + c)² − a²)
  for the cevian foot dividing `BC` in the ratio `BD:DC = c:b`.
* `angle_bisector_ratio_inner` — the genuine angle-bisector property: with the
  same ratio hypothesis, ray `AD` bisects `∠BAC` (equal half-angle cosines),
  `‖A-C‖·⟪B-A, D-A⟫ = ‖A-B‖·⟪C-A, D-A⟫`. Upgrades the previous lemma from a
  stipulated-ratio cevian to the actual internal bisector.

The geometric content (BD = s·a, DC = (1 - s)·a) is what makes `m + n = a`; here
that is encoded directly so the algebraic identity holds with no sign hypotheses.

Tags: geometry, stewarts-theorem, cevian, inner-product-space, law-of-cosines
0 axioms, 0 sorries.
-/

namespace StewartsTheoremInner

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Squared norm of a linear combination of two vectors, expanded bilinearly:
    ‖p • u + q • v‖² = p²‖u‖² + q²‖v‖² + 2pq⟪u, v⟫. -/
theorem norm_smul_add_smul_sq (p q : ℝ) (u v : V) :
    ‖p • u + q • v‖ ^ 2 =
      p ^ 2 * ‖u‖ ^ 2 + q ^ 2 * ‖v‖ ^ 2 + 2 * (p * q) * ⟪u, v⟫ := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **Stewart's theorem, coordinate-free form.**

    For points `A, B, C` in a real inner product space and the affine cevian foot
    `D = (1 - s) • B + s • C`, the squared cevian length is

      ‖A - D‖² = (1 - s)‖A - B‖² + s‖A - C‖² − s(1 - s)‖B - C‖².

    Proof: write `A - D = (1 - s)(A - B) + s(A - C)` and `B - C = (A - C) - (A - B)`,
    then expand both sides bilinearly. -/
theorem stewart_cevian_inner (A B C : V) (s : ℝ) :
    ‖A - ((1 - s) • B + s • C)‖ ^ 2 =
      (1 - s) * ‖A - B‖ ^ 2 + s * ‖A - C‖ ^ 2 - s * (1 - s) * ‖B - C‖ ^ 2 := by
  have hAD : A - ((1 - s) • B + s • C) = (1 - s) • (A - B) + s • (A - C) := by
    module
  have hBC : B - C = (A - C) - (A - B) := by module
  rw [hAD, hBC]
  generalize A - B = u
  generalize A - C = v
  rw [norm_smul_add_smul_sq, norm_sub_sq_real, real_inner_comm v u]
  ring

/-- **Stewart's theorem, classical form** `b²m + c²n = a(d² + mn)`.

    With `a = ‖B - C‖`, `m = s·a`, `n = (1 - s)·a`, `b = ‖A - C‖`, `c = ‖A - B‖`,
    and `d = ‖A - D‖` where `D = (1 - s) • B + s • C`, we recover the 1746 identity.
    Here `m + n = a` holds by construction (see `stewart_m_add_n`). -/
theorem stewarts_theorem_inner (A B C : V) (s a : ℝ) (ha : a = ‖B - C‖) :
    ‖A - C‖ ^ 2 * (s * a) + ‖A - B‖ ^ 2 * ((1 - s) * a) =
      a * (‖A - ((1 - s) • B + s • C)‖ ^ 2 + (s * a) * ((1 - s) * a)) := by
  rw [stewart_cevian_inner A B C s, ha]
  ring

/-- The two cevian segments sum to the full side: `m + n = a`. -/
theorem stewart_m_add_n (s a : ℝ) : s * a + (1 - s) * a = a := by ring

/-- **Apollonius' median theorem** (the `s = 1/2` case of Stewart):

      ‖A - midpoint(B,C)‖² = ½‖A - B‖² + ½‖A - C‖² − ¼‖B - C‖². -/
theorem apollonius_median_inner (A B C : V) :
    ‖A - ((1 / 2 : ℝ) • B + (1 / 2 : ℝ) • C)‖ ^ 2 =
      (1 / 2) * ‖A - B‖ ^ 2 + (1 / 2) * ‖A - C‖ ^ 2 - (1 / 4) * ‖B - C‖ ^ 2 := by
  have h := stewart_cevian_inner A B C (1 / 2)
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e] at h
  rw [h]; ring

/-- **Angle-bisector length formula** (a further specialization of Stewart).

    If the cevian foot `D = (1 - s) • B + s • C` divides `BC` in the ratio
    `BD : DC = AB : AC`, i.e. `s · (‖A-C‖ + ‖A-B‖) = ‖A-B‖` (equivalently
    `s / (1-s) = ‖A-B‖ / ‖A-C‖`), then the squared cevian length satisfies

      (b + c)² · ‖A - D‖² = b·c·((b + c)² − a²),    with a = ‖B-C‖, b = ‖A-C‖, c = ‖A-B‖,

    i.e. `‖A-D‖² = bc(1 − a²/(b+c)²)`, the classical internal-bisector length.

    The hypothesis `hs` encodes only the segment ratio `BD:DC = c:b`; that this
    ratio is the one realized by the actual *angle* bisector (equal angles at `A`)
    is a separate geometric fact, not used or proved here.  Stated in cleared
    `(b+c)²`-multiplied form to avoid division. -/
theorem angle_bisector_length_inner (A B C : V) (s : ℝ)
    (hs : s * (‖A - C‖ + ‖A - B‖) = ‖A - B‖) :
    (‖A - C‖ + ‖A - B‖) ^ 2 * ‖A - ((1 - s) • B + s • C)‖ ^ 2 =
      ‖A - B‖ * ‖A - C‖ * ((‖A - C‖ + ‖A - B‖) ^ 2 - ‖B - C‖ ^ 2) := by
  rw [stewart_cevian_inner A B C s]
  linear_combination
    ((‖A - C‖ + ‖A - B‖) ^ 2 * (‖A - C‖ - ‖A - B‖) +
        ‖B - C‖ ^ 2 * (s * (‖A - C‖ + ‖A - B‖) - ‖A - C‖)) * hs

/-- **Angle-bisector property** (equal half-angle cosines).

    The companion `angle_bisector_length_inner` only used the segment ratio
    `BD : DC = c : b`; it did *not* establish that this ratio is the one cut by
    the genuine internal angle bisector at `A`.  This lemma supplies exactly
    that geometric content: for the cevian foot `D = (1 - s) • B + s • C` with
    the same ratio hypothesis `hs : s · (b + c) = c` (`b = ‖A-C‖`, `c = ‖A-B‖`),
    ray `AD` bisects `∠BAC` — the two half-angles have equal cosine.  Stated in
    the cleared, division-free cross-multiplied form

      ‖A-C‖ · ⟪B-A, D-A⟫ = ‖A-B‖ · ⟪C-A, D-A⟫,

    which is `cos∠BAD = cos∠DAC` with the common `‖D-A‖` and the norms
    `‖B-A‖ = c`, `‖C-A‖ = b` cleared.  Valid in any real inner product space and
    any dimension; certified numerically over dims 2–8 by
    `verify_bisector_theorem.py`.

    Proof: expand both inner products bilinearly to the scalar shape
    `b·((1-s)c² + s·w) = c·((1-s)w + s·b²)` with `w = ⟪B-A, C-A⟫`, then close by
    `linear_combination · hs` since the difference factors as
    `(w − bc)·(s(b+c) − c)`. -/
theorem angle_bisector_ratio_inner (A B C : V) (s : ℝ)
    (hs : s * (‖A - C‖ + ‖A - B‖) = ‖A - B‖) :
    ‖A - C‖ * ⟪B - A, ((1 - s) • B + s • C) - A⟫_ℝ
      = ‖A - B‖ * ⟪C - A, ((1 - s) • B + s • C) - A⟫_ℝ := by
  have hD : ((1 - s) • B + s • C) - A = (1 - s) • (B - A) + s • (C - A) := by
    module
  rw [hD, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm (C - A) (B - A), norm_sub_rev B A,
    norm_sub_rev C A]
  linear_combination (⟪B - A, C - A⟫_ℝ - ‖A - C‖ * ‖A - B‖) * hs

/-
## Summary

This file lifts Stewart's theorem from the scalar law-of-cosines derivation of
`LawOfCosinesOQ04.lean` to genuine inner-product geometry.  The master identity
`stewart_cevian_inner` holds in any real inner product space and any dimension,
with the cevian foot given as an affine combination of the endpoints.  The
classical `b²m + c²n = a(d² + mn)` form and Apollonius' median theorem follow as
specializations.

0 axioms, 0 sorries.
-/

end StewartsTheoremInner
