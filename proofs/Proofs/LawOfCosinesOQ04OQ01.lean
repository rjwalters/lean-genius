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

* `stewart_angle_bisector_inner` / `stewart_angle_bisector_segments` — the
  internal angle-bisector special case, where `s·‖A - C‖ = (1 - s)·‖A - B‖`
  encodes the ratio `BD : DC = AB : AC`.  Stewart's identity then collapses to
  the classical bisector-length law `t² = bc − mn`:
    ‖A - D‖² = ‖A - B‖·‖A - C‖ − (BD)·(DC).

The geometric content (BD = s·a, DC = (1 - s)·a) is what makes `m + n = a`; here
that is encoded directly so the algebraic identity holds with no sign hypotheses.

Tags: geometry, stewarts-theorem, cevian, inner-product-space, law-of-cosines
0 axioms, 0 sorries.
-/

namespace StewartsTheoremInner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Squared norm of a linear combination of two vectors, expanded bilinearly:
    ‖p • u + q • v‖² = p²‖u‖² + q²‖v‖² + 2pq⟪u, v⟫. -/
theorem norm_smul_add_smul_sq (p q : ℝ) (u v : V) :
    ‖p • u + q • v‖ ^ 2 =
      p ^ 2 * ‖u‖ ^ 2 + q ^ 2 * ‖v‖ ^ 2 + 2 * (p * q) * (inner u v : ℝ) := by
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
  rw [hAD, hBC, norm_smul_add_smul_sq, norm_sub_sq_real,
    real_inner_comm (A - C) (A - B)]
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

/-- **Angle-bisector length theorem** (`t² = bc − s(1−s)·a²`).

    When `D = (1 - s) • B + s • C` is the foot of the *internal angle bisector*
    from `A`, the parameter `s` satisfies the ratio `BD : DC = AB : AC`.  Since
    `BD = s·‖B - C‖` and `DC = (1 - s)·‖B - C‖`, that ratio is
    `s : (1 - s) = ‖A - B‖ : ‖A - C‖`, i.e. `s·‖A - C‖ = (1 - s)·‖A - B‖`.

    Under this bisector condition the master cevian identity collapses: the
    `‖A - B‖²` and `‖A - C‖²` terms combine into the single product
    `‖A - B‖·‖A - C‖`, giving

      ‖A - D‖² = ‖A - B‖·‖A - C‖ − s(1 - s)·‖B - C‖².

    Proof: rewrite with `stewart_cevian_inner`; the remaining scalar identity
    `(1 - s)c² + s·b² = b·c` follows from the bisector relation `s·b = (1 - s)·c`
    via `linear_combination (b - c) · hbis`. -/
theorem stewart_angle_bisector_inner (A B C : V) (s : ℝ)
    (hbis : s * ‖A - C‖ = (1 - s) * ‖A - B‖) :
    ‖A - ((1 - s) • B + s • C)‖ ^ 2 =
      ‖A - B‖ * ‖A - C‖ - s * (1 - s) * ‖B - C‖ ^ 2 := by
  rw [stewart_cevian_inner A B C s]
  linear_combination (‖A - C‖ - ‖A - B‖) * hbis

/-- **Angle-bisector length, classical segment form** `t² = bc − mn`.

    With the two cevian segments written explicitly as `m = BD = s·‖B - C‖` and
    `n = DC = (1 - s)·‖B - C‖`, the squared angle-bisector length is the product
    of the two adjacent sides minus the product of the two segments it cuts on
    the opposite side:

      ‖A - D‖² = ‖A - B‖·‖A - C‖ − (BD)·(DC). -/
theorem stewart_angle_bisector_segments (A B C : V) (s : ℝ)
    (hbis : s * ‖A - C‖ = (1 - s) * ‖A - B‖) :
    ‖A - ((1 - s) • B + s • C)‖ ^ 2 =
      ‖A - B‖ * ‖A - C‖ - (s * ‖B - C‖) * ((1 - s) * ‖B - C‖) := by
  rw [stewart_angle_bisector_inner A B C s hbis]
  ring

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
