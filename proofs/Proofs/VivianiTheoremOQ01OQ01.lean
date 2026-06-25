import Mathlib

/-
# Viviani's Theorem — OQ-01-OQ-01: the converse

## Research Problem: viviani-theorem-oq-01-oq-01

Viviani's theorem (parent `viviani-theorem-oq-01`) proves the *forward* direction:
inside an equilateral triangle the sum of the perpendicular distances from an
interior point to the three sides is constant (the altitude). Here we prove the
**converse**, turning the theorem into a characterisation:

    the distance-sum S(P) is independent of P   ⇔   the triangle is equilateral.

Following the problem's own reduction, the proof has two crisp parts.

* **Affine / gradient reduction.** Each signed distance `d_i(P) = ⟪n_i, P⟫ + cᵢ`
  is affine with gradient the inward unit normal `n_i`, so the distance sum
  `S(P) = ⟪n_a + n_b + n_c, P⟫ + K` is constant in `P` **iff** the normal sum
  `n_a + n_b + n_c` is the zero vector.

* **Normal-vector lemma.** For the three inward unit normals of a non-degenerate
  triangle, `n_a + n_b + n_c = 0` **iff** `a = b = c`. The input is the classical
  polygon closing-normal identity `a·n_a + b·n_b + c·n_c = 0` (here free: the
  normals are `90°` rotations of the directed edges, whose vector sum is zero)
  together with the linear independence of two of the normals (non-degeneracy).

We model the Euclidean plane as `ℂ`; rotation by `90°` is multiplication by `I`,
which makes the closing identity `a·n_a + b·n_b + c·n_c = (rotation of)
(edge sum) = 0` immediate.  The signed-distance sum is built from an explicit real
inner product `rdot` on `ℂ`.  The converse is proved for the signed distance sum
over the whole plane; on the interior of the triangle all three inward distances
are positive, so the signed sum equals the perpendicular-distance sum there and
the characterisation transfers verbatim.

Tags: geometry, viviani, converse, equilateral-triangle, inner-product, normals
-/

namespace VivianiTheoremOQ01OQ01

open Complex

/-! ## A real inner product on the plane `ℂ` -/

/-- The standard real inner product on the Euclidean plane `ℂ`. -/
def rdot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

@[simp] lemma rdot_add_left (x y w : ℂ) : rdot (x + y) w = rdot x w + rdot y w := by
  simp only [rdot, Complex.add_re, Complex.add_im]; ring

@[simp] lemma rdot_add_right (x y w : ℂ) : rdot w (x + y) = rdot w x + rdot w y := by
  simp only [rdot, Complex.add_re, Complex.add_im]; ring

@[simp] lemma rdot_sub_right (x y w : ℂ) : rdot w (x - y) = rdot w x - rdot w y := by
  simp only [rdot, Complex.sub_re, Complex.sub_im]; ring

@[simp] lemma rdot_smul_left (r : ℝ) (z w : ℂ) : rdot (r • z) w = r * rdot z w := by
  simp only [rdot, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]; ring

/-- `rdot` is positive definite: `rdot z z = 0 ↔ z = 0`. -/
lemma rdot_self_eq_zero {z : ℂ} : rdot z z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hre : z.re = 0 ∧ z.im = 0 := by
      have h1 : z.re ^ 2 + z.im ^ 2 = 0 := by simpa [rdot, sq] using h
      constructor
      · nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      · nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact Complex.ext hre.1 hre.2
  · rintro rfl; simp [rdot]

/-! ## Linear independence from a non-zero determinant -/

/-- Two plane vectors `u, v` with non-zero determinant `uₓvy − uy vₓ` are
`ℝ`-linearly independent: the only real combination summing to `0` is trivial. -/
lemma indep_of_det {u v : ℂ} (h : u.re * v.im - u.im * v.re ≠ 0) :
    ∀ s t : ℝ, s • u + t • v = 0 → s = 0 ∧ t = 0 := by
  intro s t hst
  have e1 : s * u.re + t * v.re = 0 := by
    have := congrArg Complex.re hst
    simpa [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im] using this
  have e2 : s * u.im + t * v.im = 0 := by
    have := congrArg Complex.im hst
    simpa [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] using this
  constructor
  · have : s * (u.re * v.im - u.im * v.re) = 0 := by
      linear_combination v.im * e1 - v.re * e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' h
  · have : t * (u.re * v.im - u.im * v.re) = 0 := by
      linear_combination u.re * e2 - u.im * e1
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## The normal-vector heart: `n_a + n_b + n_c = 0 ⇔ a = b = c` -/

/-- **Normal-sum lemma.** Let `Na, Nb, Nc` be the (un-normalised, equal-length to
the sides) inward normals of a triangle, with positive side lengths `a, b, c` and
unit normals `nᵢ = ‖Nᵢ‖⁻¹ • Nᵢ = aᵢ⁻¹ • Nᵢ`. Given the closing-normal identity
`Na + Nb + Nc = 0` and the linear independence of two of the normals
(non-degeneracy), the unit normals sum to zero **iff** the triangle is
equilateral. This is the algebraic core of the converse of Viviani's theorem. -/
theorem normalSum_zero_iff_equilateral
    {Na Nb Nc : ℂ} {a b c : ℝ}
    (hclose : Na + Nb + Nc = 0)
    (hindep : ∀ s t : ℝ, s • Na + t • Nb = 0 → s = 0 ∧ t = 0) :
    ((a⁻¹ • Na + b⁻¹ • Nb + c⁻¹ • Nc : ℂ) = 0) ↔ (a = b ∧ b = c) := by
  constructor
  · intro h
    -- Subtract `c⁻¹ • (closing identity)` to kill `Nc`.
    have h2 : (a⁻¹ - c⁻¹) • Na + (b⁻¹ - c⁻¹) • Nb = 0 := by
      have key : (a⁻¹ - c⁻¹) • Na + (b⁻¹ - c⁻¹) • Nb
          = (a⁻¹ • Na + b⁻¹ • Nb + c⁻¹ • Nc) - c⁻¹ • (Na + Nb + Nc) := by
        module
      rw [key, h, hclose, smul_zero, sub_zero]
    obtain ⟨h3, h4⟩ := hindep _ _ h2
    have hac : a⁻¹ = c⁻¹ := by linarith
    have hbc : b⁻¹ = c⁻¹ := by linarith
    have ha_eq_c : a = c := inv_inj.mp hac
    have hb_eq_c : b = c := inv_inj.mp hbc
    exact ⟨ha_eq_c.trans hb_eq_c.symm, hb_eq_c⟩
  · rintro ⟨hab, hbc⟩
    have hba : b = a := hab.symm
    have hca : c = a := (hbc.symm).trans hab.symm
    rw [hba, hca]
    have hcollect : a⁻¹ • Na + a⁻¹ • Nb + a⁻¹ • Nc = a⁻¹ • (Na + Nb + Nc) := by
      module
    rw [hcollect, hclose, smul_zero]

/-! ## The affine / gradient reduction -/

/-- The difference of the signed distance sums at two points `P, Q` depends only on
the normal sum: it equals `⟪n_a + n_b + n_c, P − Q⟫`. -/
lemma sumDist_sub (na nb nc B C A P Q : ℂ) :
    (rdot na (P - B) + rdot nb (P - C) + rdot nc (P - A))
      - (rdot na (Q - B) + rdot nb (Q - C) + rdot nc (Q - A))
      = rdot (na + nb + nc) (P - Q) := by
  simp only [rdot, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- **Affine reduction.** The signed distance sum `P ↦ ∑ ⟪nᵢ, P − vᵢ⟫` is constant
on the whole plane **iff** the normal sum `n_a + n_b + n_c` vanishes. -/
lemma const_iff_normalSum_zero (na nb nc B C A : ℂ) :
    (∀ P Q : ℂ,
        rdot na (P - B) + rdot nb (P - C) + rdot nc (P - A)
          = rdot na (Q - B) + rdot nb (Q - C) + rdot nc (Q - A))
      ↔ na + nb + nc = 0 := by
  constructor
  · intro hconst
    have hsub := sumDist_sub na nb nc B C A (na + nb + nc) 0
    rw [hconst (na + nb + nc) 0, sub_self] at hsub
    have : rdot (na + nb + nc) (na + nb + nc) = 0 := by
      simpa using hsub.symm
    exact rdot_self_eq_zero.mp this
  · intro h P Q
    have hsub := sumDist_sub na nb nc B C A P Q
    rw [h] at hsub
    have hz : rdot (0 : ℂ) (P - Q) = 0 := by simp [rdot]
    rw [hz] at hsub
    linarith [hsub]

/-! ## The converse of Viviani's theorem -/

/-- Inward unit normal to side `BC` (opposite `A`): the directed edge `C − B`
rotated by `90°` (multiplication by `I`) and normalised. -/
noncomputable def nA (A B C : ℂ) : ℂ := ‖C - B‖⁻¹ • (Complex.I * (C - B))

/-- Inward unit normal to side `CA` (opposite `B`). -/
noncomputable def nB (A B C : ℂ) : ℂ := ‖A - C‖⁻¹ • (Complex.I * (A - C))

/-- Inward unit normal to side `AB` (opposite `C`). -/
noncomputable def nC (A B C : ℂ) : ℂ := ‖B - A‖⁻¹ • (Complex.I * (B - A))

/-- The signed perpendicular-distance sum from a point `P` to the three sides of
the triangle `A B C`. (Each summand is the signed distance to a side; on the
interior, where all three inward distances are positive, this equals the
perpendicular-distance sum of the classical statement.) -/
noncomputable def sumDist (A B C P : ℂ) : ℝ :=
  rdot (nA A B C) (P - B) + rdot (nB A B C) (P - C) + rdot (nC A B C) (P - A)

/-- **Converse of Viviani's theorem.** For a non-degenerate planar triangle
`A B C` (encoded by the non-vanishing of the signed area / edge determinant), the
signed perpendicular-distance sum `sumDist` is independent of the point **iff** the
triangle is equilateral, i.e. its three sides have equal length. Combined with the
parent's forward direction this is the full characterisation:

    the distance-sum is constant   ⇔   the triangle is equilateral. -/
theorem viviani_converse {A B C : ℂ}
    (hnd : (C - B).re * (A - C).im - (C - B).im * (A - C).re ≠ 0) :
    (∀ P Q : ℂ, sumDist A B C P = sumDist A B C Q)
      ↔ (‖C - B‖ = ‖A - C‖ ∧ ‖A - C‖ = ‖B - A‖) := by
  -- closing-normal identity: the rotated directed edges sum to zero
  have hclose :
      Complex.I * (C - B) + Complex.I * (A - C) + Complex.I * (B - A) = 0 := by
    ring
  -- linear independence of two normals from the non-zero determinant
  have hdet :
      (Complex.I * (C - B)).re * (Complex.I * (A - C)).im
        - (Complex.I * (C - B)).im * (Complex.I * (A - C)).re
      = (C - B).re * (A - C).im - (C - B).im * (A - C).re := by
    simp only [Complex.I_mul_re, Complex.I_mul_im]; ring
  have hindep :
      ∀ s t : ℝ, s • (Complex.I * (C - B)) + t • (Complex.I * (A - C)) = 0
        → s = 0 ∧ t = 0 :=
    indep_of_det (by rw [hdet]; exact hnd)
  -- the heart, instantiated at the rotated edges and the side lengths
  have heart := normalSum_zero_iff_equilateral
    (Na := Complex.I * (C - B)) (Nb := Complex.I * (A - C)) (Nc := Complex.I * (B - A))
    (a := ‖C - B‖) (b := ‖A - C‖) (c := ‖B - A‖) hclose hindep
  -- chain: constancy ⇔ normal sum zero ⇔ equilateral
  refine (const_iff_normalSum_zero (nA A B C) (nB A B C) (nC A B C) B C A).trans ?_
  simpa only [nA, nB, nC] using heart

end VivianiTheoremOQ01OQ01
