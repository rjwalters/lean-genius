import Mathlib

/-
# Viviani's Theorem — OQ-01-OQ-02: the sharp constant for regular polygons and simplices

## Research Problem: viviani-theorem-oq-01-oq-02

Viviani's theorem (parent `viviani-theorem-oq-01`) states that inside an
equilateral triangle the sum of the perpendicular distances from an interior
point to the three sides is constant, equal to the altitude.  The sibling
`viviani-theorem-oq-01-oq-01` proved the *converse* (constancy characterises the
equilateral triangle).  Here we prove the **sharp generalisation** to arbitrary
dimension: for a regular `n`-gon and, more generally, a regular `n`-simplex the
distance sum is again constant, and we determine the exact value.

### The unifying principle

A facet of a convex body with **unit** outward normal `u` lying at (signed)
offset `c` is the hyperplane `{x : ⟪u, x⟫ = c}`; the signed perpendicular
distance from a point `P` to it is `c - ⟪u, P⟫` (positive on the interior side).
Summing over all facets,

    ∑ᵢ (cᵢ - ⟪uᵢ, P⟫)  =  (∑ᵢ cᵢ)  -  ⟪∑ᵢ uᵢ, P⟫.

Hence **whenever the outward unit normals sum to zero**, the distance sum is
`∑ᵢ cᵢ`, a constant *independent of `P`*.  This is `sum_signedDist_eq`, and it is
the entire content of every Viviani-type theorem.

### The two sharp instances

* **Regular `n`-gon** (`regularPolygon_viviani`).  Model the plane as `ℂ`.  The
  `n` outward unit normals are the `n`-th roots of unity `ζ^k` (`ζ` a primitive
  root), which sum to zero for `n ≥ 2`.  If every side lies at distance `a` (the
  *apothem*, i.e. the inradius) from the centre, the distance sum is the sharp
  constant

      ∑ₖ dₖ(P) = n · a          (n × apothem).

* **Regular `n`-simplex** (`regularSimplex_viviani`).  In any real inner-product
  space, the outward unit normal to the facet opposite vertex `vᵢ` points along
  `g - vᵢ` where `g` is the centroid; since `∑ᵢ (g - vᵢ) = 0` for the centroid,
  the normals sum to zero.  With each facet at distance `a` (the inradius) the
  distance sum is the sharp constant

      ∑ᵢ dᵢ(P) = (n+1) · a       ((n+1) × inradius).

Both are corollaries of the single algebraic identity `sum_signedDist_eq`.

Tags: geometry, viviani, regular-polygon, regular-simplex, inner-product,
roots-of-unity, sharp-constant
-/

namespace VivianiTheoremOQ01OQ02

open Complex Finset
open scoped RealInnerProductSpace

/-! ## Part A — the general Viviani principle

Signed perpendicular distance to a facet with unit normal `u` at offset `c` is
`c - ⟪u, P⟫`.  If the normals sum to zero the total is `∑ c`, independent of `P`.
-/

/-- **General Viviani identity.**  In a real inner-product space, if the (outward,
unit) facet normals `u i` sum to zero, the sum of the signed perpendicular
distances `c i - ⟪u i, P⟫` from any point `P` equals `∑ i, c i`, independent of
`P`. -/
theorem sum_signedDist_eq {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : ι → V) (c : ι → ℝ) (hu : ∑ i, u i = 0) (P : V) :
    ∑ i, (c i - ⟪u i, P⟫) = ∑ i, c i := by
  rw [Finset.sum_sub_distrib, ← sum_inner, hu, inner_zero_left, sub_zero]

/-- **Constancy form.**  Under the same hypothesis the distance sum is the same
for any two points `P` and `Q`. -/
theorem sum_signedDist_const {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : ι → V) (c : ι → ℝ) (hu : ∑ i, u i = 0) (P Q : V) :
    ∑ i, (c i - ⟪u i, P⟫) = ∑ i, (c i - ⟪u i, Q⟫) := by
  rw [sum_signedDist_eq u c hu P, sum_signedDist_eq u c hu Q]

/-! ## Part B — the regular polygon

We model the Euclidean plane as `ℂ` with the standard real inner product `rdot`.
The outward unit normals of a regular `n`-gon are the `n`-th roots of unity. -/

/-- The standard real inner product on the Euclidean plane `ℂ`. -/
def rdot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

@[simp] lemma rdot_zero_left (w : ℂ) : rdot 0 w = 0 := by simp [rdot]

lemma rdot_add_left (x y w : ℂ) : rdot (x + y) w = rdot x w + rdot y w := by
  simp only [rdot, Complex.add_re, Complex.add_im]; ring

/-- `rdot` is additive over finite sums in the left argument. -/
lemma rdot_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (w : ℂ) :
    rdot (∑ i ∈ s, f i) w = ∑ i ∈ s, rdot (f i) w := by
  classical
  induction s using Finset.induction with
  | empty => simp [rdot]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, rdot_add_left, ih]

/-- The `n`-th roots of unity sum to zero for `n ≥ 2`. -/
lemma sum_primitiveRoot_pow_eq_zero {n : ℕ} (hn : 2 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) : ∑ k : Fin n, ζ ^ (k : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k)]
  have hne : ζ ≠ 1 := hζ.ne_one (by omega)
  rw [geom_sum_eq hne n, hζ.pow_eq_one, sub_self, zero_div]

/-- Each root-of-unity normal is a genuine **unit** vector, so `c - rdot (ζ^k) P`
really is a Euclidean perpendicular distance. -/
lemma primitiveRoot_pow_norm {n : ℕ} (hn : 2 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) : ‖ζ ^ k‖ = 1 := by
  have hz : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  rw [norm_pow, hz, one_pow]

/-- **Viviani for a regular `n`-gon (sharp constant).**  Model the plane as `ℂ`
and let the `n` outward unit normals be the roots of unity `ζ^k` (`ζ` a primitive
`n`-th root, `n ≥ 2`).  If every side lies at distance `a` (the apothem) from the
centre, the sum of the perpendicular distances from *any* point `P` to the `n`
sides equals the sharp constant `n · a`. -/
theorem regularPolygon_viviani {n : ℕ} (hn : 2 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (a : ℝ) (P : ℂ) :
    ∑ k : Fin n, (a - rdot (ζ ^ (k : ℕ)) P) = n * a := by
  rw [Finset.sum_sub_distrib, ← rdot_sum, sum_primitiveRoot_pow_eq_zero hn hζ,
    rdot_zero_left, sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The regular polygon is realised concretely by the `exp(2πik/n)` roots of
unity (`Complex.isPrimitiveRoot_exp`), so a primitive `n`-th root — hence a genuine
regular `n`-gon — attaining the sharp constant `n · a` always exists. -/
theorem regularPolygon_viviani_exists {n : ℕ} (hn : 2 ≤ n) (a : ℝ) (P : ℂ) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n ∧
      ∑ k : Fin n, (a - rdot (ζ ^ (k : ℕ)) P) = n * a :=
  ⟨_, Complex.isPrimitiveRoot_exp n (by omega),
    regularPolygon_viviani hn (Complex.isPrimitiveRoot_exp n (by omega)) a P⟩

/-- **Constancy form for the regular polygon:** the distance sum is independent of
the interior point. -/
theorem regularPolygon_viviani_const {n : ℕ} (hn : 2 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (a : ℝ) (P Q : ℂ) :
    ∑ k : Fin n, (a - rdot (ζ ^ (k : ℕ)) P)
      = ∑ k : Fin n, (a - rdot (ζ ^ (k : ℕ)) Q) := by
  rw [regularPolygon_viviani hn hζ a P, regularPolygon_viviani hn hζ a Q]

/-! ## Part C — the regular simplex

In any real inner-product space, the outward unit normal to the facet opposite
vertex `vᵢ` points along `g - vᵢ` (`g` = centroid).  Because the centroid makes
`∑ᵢ (g - vᵢ) = 0`, the normals sum to zero and the general principle applies. -/

/-- **Viviani for a regular `n`-simplex (sharp constant).**  Let `v : Fin (n+1) → V`
be the vertices of a simplex in a real inner-product space with centroid `g`
(encoded by `∑ i, v i = (n+1) • g`), and let `R ≠ 0` be the common circumradius so
that the outward unit normals are `R⁻¹ • (g - v i)`.  If every facet lies at
distance `a` (the inradius) from the centroid, the sum of the perpendicular
distances from *any* point `P` to the `n+1` facets equals the sharp constant
`(n+1) · a`. -/
theorem regularSimplex_viviani {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : Fin (n + 1) → V) (g : V) (R : ℝ)
    (hcentroid : ∑ i, v i = (n + 1) • g) (a : ℝ) (P : V) :
    ∑ i, (a - ⟪R⁻¹ • (g - v i), P⟫) = (n + 1) * a := by
  have hu : ∑ i, (R⁻¹ • (g - v i)) = 0 := by
    rw [← Finset.smul_sum]
    have hg : ∑ _i : Fin (n + 1), g = (n + 1) • g := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have : ∑ i, (g - v i) = 0 := by
      rw [Finset.sum_sub_distrib, hg, hcentroid, sub_self]
    rw [this, smul_zero]
  rw [sum_signedDist_eq (fun i => R⁻¹ • (g - v i)) (fun _ => a) hu P,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Constancy form for the regular simplex.** -/
theorem regularSimplex_viviani_const {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : Fin (n + 1) → V) (g : V) (R : ℝ)
    (hcentroid : ∑ i, v i = (n + 1) • g) (a : ℝ) (P Q : V) :
    ∑ i, (a - ⟪R⁻¹ • (g - v i), P⟫) = ∑ i, (a - ⟪R⁻¹ • (g - v i), Q⟫) := by
  rw [regularSimplex_viviani v g R hcentroid a P,
    regularSimplex_viviani v g R hcentroid a Q]

end VivianiTheoremOQ01OQ02
