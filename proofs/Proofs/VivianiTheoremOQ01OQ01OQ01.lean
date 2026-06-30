import Mathlib

/-
# Viviani's Theorem — OQ-01-OQ-01-OQ-01: the convex n-gon characterisation

## Research Problem: viviani-theorem-oq-01-oq-01-oq-01

The parent leaf `viviani-theorem-oq-01-oq-01` proved the *triangle converse*: the
signed perpendicular-distance sum is constant iff the three inward unit normals sum
to zero, iff the triangle is equilateral. This leaf removes the triangle-specific
"equilateral" half and isolates the genuinely general phenomenon — valid for an
arbitrary finite family of edges (a convex n-gon, but in fact any indexed family of
normals).

For a polygon whose edge `i` lies on the line `{x : ⟪x, νᵢ⟫ = cᵢ}` with outward
unit normal `νᵢ`, the signed distance from an interior point `x` to edge `i` is
`dᵢ(x) = cᵢ − ⟪x, νᵢ⟫`, so the total distance-sum is

    S(x) = ∑ᵢ (cᵢ − ⟪x, νᵢ⟫) = (∑ᵢ cᵢ) − ⟪x, ∑ᵢ νᵢ⟫ .

This is an *affine* function of `x` with gradient `−∑ᵢ νᵢ`, so

    S is constant on the plane   ⇔   ∑ᵢ νᵢ = 0.                       (★)

The headline corollary is that every **regular n-gon** has the Viviani property:
its outward unit normals are the `n`-th roots of unity `ζ⁰, ζ¹, …, ζⁿ⁻¹` with
`ζ = exp(2πi/n)`, and these sum to zero for `n ≥ 2`. The characterisation (★) is
sharp and captures a *strictly larger* class than the regular polygons (any family
of unit vectors closing up to zero, e.g. equiangular polygons).

We model the Euclidean plane as `ℂ` and reuse the parent's explicit real inner
product `rdot z w = z.re·w.re + z.im·w.im`. The whole argument is elementary linear
algebra over a finite index set; no triangle non-degeneracy hypothesis is needed.

Tags: geometry, viviani, n-gon, inner-product, normals, roots-of-unity, affine
-/

namespace VivianiTheoremOQ01OQ01OQ01

open Complex Finset

/-! ## A real inner product on the plane `ℂ` (after the parent) -/

/-- The standard real inner product on the Euclidean plane `ℂ`. -/
def rdot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

@[simp] lemma rdot_zero_left (w : ℂ) : rdot 0 w = 0 := by simp [rdot]

@[simp] lemma rdot_add_left (x y w : ℂ) : rdot (x + y) w = rdot x w + rdot y w := by
  simp only [rdot, Complex.add_re, Complex.add_im]; ring

@[simp] lemma rdot_sub_right (x y w : ℂ) : rdot w (x - y) = rdot w x - rdot w y := by
  simp only [rdot, Complex.sub_re, Complex.sub_im]; ring

/-- `rdot` is positive definite: `rdot z z = 0 ↔ z = 0`. -/
lemma rdot_self_eq_zero {z : ℂ} : rdot z z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hre : z.re = 0 ∧ z.im = 0 := by
      have h1 : z.re ^ 2 + z.im ^ 2 = 0 := by simpa [rdot, sq] using h
      exact ⟨by nlinarith [sq_nonneg z.re, sq_nonneg z.im],
             by nlinarith [sq_nonneg z.re, sq_nonneg z.im]⟩
    exact Complex.ext hre.1 hre.2
  · rintro rfl; simp [rdot]

/-- `rdot` is additive in its first slot over a finite sum: bundled as an
`AddMonoidHom` so `map_sum` gives `rdot (∑ᵢ fᵢ) w = ∑ᵢ rdot fᵢ w`. -/
def rdotHom (w : ℂ) : ℂ →+ ℝ where
  toFun z := rdot z w
  map_zero' := rdot_zero_left w
  map_add' x y := rdot_add_left x y w

@[simp] lemma rdotHom_apply (z w : ℂ) : rdotHom w z = rdot z w := rfl

lemma rdot_sum_left {ι : Type*} (s : Finset ι) (f : ι → ℂ) (w : ℂ) :
    rdot (∑ i ∈ s, f i) w = ∑ i ∈ s, rdot (f i) w := by
  simp only [← rdotHom_apply]; exact map_sum (rdotHom w) f s

/-! ## The signed distance-sum and the affine reduction -/

/-- The signed distance-sum from a point `x` to the edges indexed by `s`, where
edge `i` has outward unit normal `ν i` and offset `c i` (its line is
`{y : ⟪y, ν i⟫ = c i}`). Each summand is the signed distance `c i − ⟪x, ν i⟫`. -/
def distSum {ι : Type*} (s : Finset ι) (ν : ι → ℂ) (c : ι → ℝ) (x : ℂ) : ℝ :=
  ∑ i ∈ s, (c i - rdot (ν i) x)

/-- The difference of the distance-sums at two points depends only on the normal
sum: `S(x) − S(y) = ⟪∑ᵢ νᵢ, y − x⟫`. This is the affine/gradient identity. -/
lemma distSum_sub {ι : Type*} (s : Finset ι) (ν : ι → ℂ) (c : ι → ℝ) (x y : ℂ) :
    distSum s ν c x - distSum s ν c y = rdot (∑ i ∈ s, ν i) (y - x) := by
  rw [distSum, distSum, rdot_sum_left, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [rdot_sub_right]
  ring

/-- **Affine reduction (the heart of the n-gon Viviani theorem).** The signed
distance-sum `x ↦ ∑ᵢ (cᵢ − ⟪x, νᵢ⟫)` is constant over the whole plane **iff** the
outward normals sum to the zero vector. -/
theorem distSum_const_iff_normalSum_zero {ι : Type*}
    (s : Finset ι) (ν : ι → ℂ) (c : ι → ℝ) :
    (∀ x y : ℂ, distSum s ν c x = distSum s ν c y) ↔ ∑ i ∈ s, ν i = 0 := by
  constructor
  · intro hconst
    set V := ∑ i ∈ s, ν i with hV
    have hsub := distSum_sub s ν c V 0
    rw [hconst V 0, sub_self, ← hV, rdot_sub_right] at hsub
    -- hsub : 0 = rdot V 0 - rdot V V
    have hV0 : rdot V (0 : ℂ) = 0 := by simp [rdot]
    rw [hV0] at hsub
    have hVV : rdot V V = 0 := by linarith
    exact rdot_self_eq_zero.mp hVV
  · intro hzero x y
    have hsub := distSum_sub s ν c x y
    rw [hzero, rdot_zero_left] at hsub
    linarith

/-! ## The regular n-gon corollary: outward normals are roots of unity -/

/-- The outward unit normals of a regular `n`-gon, as the `n`-th roots of unity
`ζ^k` for `k = 0, …, n−1`, where `ζ = exp(2πi/n)`. -/
noncomputable def regularNormal (n : ℕ) (k : ℕ) : ℂ :=
  (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k

/-- **The normals of a regular n-gon close up.** For `n ≥ 2` the outward unit
normals of a regular `n`-gon sum to zero — the `n`-th roots of unity cancel. -/
theorem regularNormal_sum_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range n, regularNormal n k = 0 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n (by omega)
  simpa [regularNormal] using hζ.geom_sum_eq_zero (by omega)

/-- **Viviani for regular n-gons (headline corollary).** Every regular `n`-gon
with `n ≥ 2` has the Viviani property: the signed distance-sum from an interior
point to its sides is the same for every point. Proved by feeding the
roots-of-unity cancellation into the affine reduction. -/
theorem regular_ngon_distSum_const (n : ℕ) (hn : 2 ≤ n) (c : ℕ → ℝ) :
    ∀ x y : ℂ, distSum (Finset.range n) (regularNormal n) c x
             = distSum (Finset.range n) (regularNormal n) c y :=
  (distSum_const_iff_normalSum_zero (Finset.range n) (regularNormal n) c).mpr
    (regularNormal_sum_zero n hn)

/-- **Sharpness / converse for the regular case is genuine.** The Viviani property
for *any* convex `n`-gon is exactly the closing-up condition `∑ᵢ νᵢ = 0` on its
outward unit normals — neither regularity nor any metric symmetry is required. This
restates the affine reduction as the precise characterisation. -/
theorem viviani_ngon_characterisation {ι : Type*}
    (s : Finset ι) (ν : ι → ℂ) (c : ι → ℝ) :
    (∀ x y : ℂ, distSum s ν c x = distSum s ν c y) ↔ ∑ i ∈ s, ν i = 0 :=
  distSum_const_iff_normalSum_zero s ν c

end VivianiTheoremOQ01OQ01OQ01
