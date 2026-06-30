import Proofs.CevasTheoremOQ02OQ04
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-
# Menelaus in Higher Dimensions: The Signed Twisted-Cocycle Criterion

## What This Proves

The parent file `CevasTheoremOQ02OQ04.lean` answers the open question of when cevian
hypersurfaces *concur* in a simplex: the (positive) edge ratios `w j / w i` of a
common interior point form a **1-cocycle**, and around every triangular 2-face the
classical Ceva product equals `+1`.

This file develops the **dual / transversal** story — Menelaus's theorem in higher
dimensions. A hyperplane crossing the edges of an n-simplex is the natural opposite
of a concurrency point: instead of `+1` the signed ratios multiply to `-1` around
each face, and the cocycle picks up a sign.

### Setup

A hyperplane `H = {x : ℓ(x) = c}` missing every vertex of the simplex assigns to
each vertex `i` the nonzero value `a i = ℓ(Vᵢ) - c`. The point where `H` meets the
edge from `Vᵢ` to `Vⱼ` divides that edge in the **signed ratio**

  `menelausRatio a i j = - a i / a j`.

(The point on `(1-t)Vᵢ + tVⱼ` with `ℓ = c` sits at `t = aᵢ/(aᵢ - aⱼ)`, giving the
signed division ratio `t/(1-t) = -aᵢ/aⱼ`.)

### The theorems

1. **Forward (a hyperplane ⟹ relations).**
   - `menelausRatio_self`     : `m i i = -1`
   - `menelausRatio_swap`     : `m i j · m j i = 1`
   - `menelausRatio_twisted_cocycle` : `m i j · m j k = - m i k`  (cocycle with a sign)
   - `menelausRatio_triangle` : `m i j · m j k · m k i = -1`  (Menelaus on every 2-face)
   - `menelausRatio_cycle_prod` : around a closed walk of length `L` the product is
     `(-1)^L`. The triangle case `L = 3` is `-1`.

2. **Converse (relations ⟹ a hyperplane).** Any nonzero signed assignment satisfying
   the twisted cocycle law arises from vertex values: `exists_values_of_twisted_cocycle`
   reconstructs `a i = 1 / m b i`.

3. **The criterion** (`twisted_cocycle_iff_triangles`, `menelaus_criterion`). For a
   nonzero `m`, the following are equivalent:
   - `∃` vertex values `a` with `m i j = - a i / a j` (a transversal hyperplane exists),
   - the twisted cocycle law `m i j · m j k = - m i k`,
   - the Menelaus product `-1` on every triangular 2-face.

4. **Ceva–Menelaus duality** (`menelausRatio_eq_neg_edgeRatio`,
   `menelaus_triangle_eq_neg_ceva`). The signed ratio is literally the negated parent
   edge ratio with reversed orientation, and the Menelaus face product is the negation
   of the Ceva face product: `-1` (collinear/transversal) versus `+1` (concurrent).
   The *sign* is the entire difference between the two classical theorems.

Everything is fully machine-checked: no `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.unusedVariables false

namespace MenelausHigherDim

variable {ι : Type*}

/-- The **signed division ratio** `- a i / a j` in which a hyperplane with vertex
    values `a` meets the edge from vertex `i` to vertex `j` of a simplex. -/
noncomputable def menelausRatio (a : ι → ℝ) (i j : ι) : ℝ := - a i / a j

-- ============================================================
-- PART 1: Forward direction — signed ratios of a hyperplane
-- ============================================================

/-- A signed ratio is never zero when the hyperplane misses the vertices. -/
theorem menelausRatio_ne_zero (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (i j : ι) :
    menelausRatio a i j ≠ 0 := by
  unfold menelausRatio
  exact div_ne_zero (neg_ne_zero.mpr (ha i)) (ha j)

/-- The signed self-ratio is `-1`: a hyperplane "crosses" the degenerate edge `i → i`
    with the orientation-reversing factor that drives the whole sign bookkeeping. -/
theorem menelausRatio_self (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (i : ι) :
    menelausRatio a i i = -1 := by
  unfold menelausRatio
  rw [neg_div, div_self (ha i)]

/-- **Twisted cocycle law.** Chaining two signed ratios introduces one sign:
    `m i j · m j k = - m i k`. This is the Menelaus analogue of the Ceva cocycle
    `r i j · r j k = r i k`; the extra `-` is what turns face products from `+1`
    into `-1`. -/
theorem menelausRatio_twisted_cocycle (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (i j k : ι) :
    menelausRatio a i j * menelausRatio a j k = - menelausRatio a i k := by
  unfold menelausRatio
  have hi := ha i; have hj := ha j; have hk := ha k
  field_simp

/-- **Reciprocity.** Traversing a signed edge and back gives `+1` (the two signs
    cancel): `m i j · m j i = 1`. -/
theorem menelausRatio_swap (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (i j : ι) :
    menelausRatio a i j * menelausRatio a j i = 1 := by
  unfold menelausRatio
  have hi := ha i; have hj := ha j
  field_simp

/-- **Menelaus product on a 2-face.** Around any triangle `i → j → k → i` of the
    simplex, the product of signed ratios is `-1`. For the planar triangle this is
    precisely the classical Menelaus criterion for the three division points to be
    collinear (a transversal line). -/
theorem menelausRatio_triangle (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (i j k : ι) :
    menelausRatio a i j * menelausRatio a j k * menelausRatio a k i = -1 := by
  unfold menelausRatio
  have hi := ha i; have hj := ha j; have hk := ha k
  field_simp

/-- The classical planar Menelaus product, in the conventional cyclic order
    `B → C → A`, recovered as the 2-face product for vertices `A, B, C`. -/
theorem planar_menelaus_product (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (A B C : ι) :
    menelausRatio a B C * menelausRatio a C A * menelausRatio a A B = -1 :=
  menelausRatio_triangle a ha B C A

-- ============================================================
-- PART 2: Telescoping — product around any closed walk is (-1)^L
-- ============================================================

/-- Telescoping product of successive ratios (forward orientation): for nonzero `f`,
    `∏_{t<m} f t / f (t+1) = f 0 / f m`. -/
theorem prod_div_telescope (f : ℕ → ℝ) (hf : ∀ i, f i ≠ 0) (m : ℕ) :
    ∏ t ∈ Finset.range m, (f t / f (t + 1)) = f 0 / f m := by
  induction m with
  | zero => simp [div_self (hf 0)]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have h0 := hf 0
      have hn := hf n
      have hn1 := hf (n + 1)
      field_simp

/-- **General higher-dimensional Menelaus (closed-walk form).** For the signed ratios
    of a transversal hyperplane and any closed walk `v 0 → v 1 → ⋯ → v L = v 0`, the
    product of signed ratios along the walk is `(-1)^L`. The triangle case `L = 3`
    gives the `-1` of `menelausRatio_triangle`; an even cycle returns to `+1`. -/
theorem menelausRatio_cycle_prod (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (v : ℕ → ι) (L : ℕ) (hclosed : v L = v 0) :
    ∏ t ∈ Finset.range L, menelausRatio a (v t) (v (t + 1)) = (-1) ^ L := by
  have hfac : ∀ t, menelausRatio a (v t) (v (t + 1))
      = (-1) * (a (v t) / a (v (t + 1))) := by
    intro t; unfold menelausRatio; rw [neg_div]; ring
  rw [Finset.prod_congr rfl (fun t _ => hfac t),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hne : ∀ i, a (v i) ≠ 0 := fun i => ha (v i)
  rw [prod_div_telescope (fun i => a (v i)) hne L]
  simp only [hclosed]
  rw [div_self (ha (v 0)), mul_one]

-- ============================================================
-- PART 3: Converse — reconstructing the transversal hyperplane
-- ============================================================

/-- From the twisted cocycle law alone, a self-ratio is forced to be `-1`. -/
theorem twisted_self (m : ι → ι → ℝ) (h0 : ∀ i j, m i j ≠ 0)
    (hcoc : ∀ i j k, m i j * m j k = - m i k) (i : ι) :
    m i i = -1 := by
  have h := hcoc i i i        -- m i i * m i i = - m i i
  have hne := h0 i i
  have hfac : m i i * (m i i + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd h1 hne
  · linarith

/-- **Converse / reconstruction.** A nonzero signed assignment obeying the twisted
    cocycle law `m i j · m j k = - m i k` comes from vertex values: there exist
    nonzero `a` with `m i j = - a i / a j`. The values are reconstructed as
    `a i = 1 / m b i` for any base vertex `b` — these are the (reciprocal) functional
    values of the transversal hyperplane. -/
theorem exists_values_of_twisted_cocycle (m : ι → ι → ℝ) (b : ι)
    (h0 : ∀ i j, m i j ≠ 0)
    (hcoc : ∀ i j k, m i j * m j k = - m i k) :
    ∃ a : ι → ℝ, (∀ i, a i ≠ 0) ∧ ∀ i j, m i j = - a i / a j := by
  refine ⟨fun i => 1 / m b i, fun i => ?_, fun i j => ?_⟩
  · exact one_div_ne_zero (h0 b i)
  · have hc := hcoc b i j      -- m b i * m i j = - m b j
    have hbi := h0 b i
    have hbj := h0 b j
    field_simp
    linear_combination hc

-- ============================================================
-- PART 4: The criterion — twisted cocycle ⟺ Menelaus face products
-- ============================================================

/-- Over ℝ, the only cube root of `-1` is `-1`. -/
theorem cube_eq_neg_one (x : ℝ) (hx : x * x * x = -1) : x = -1 := by
  have hpos : x * x - x + 1 > 0 := by nlinarith [sq_nonneg (2 * x - 1)]
  have hfac : (x + 1) * (x * x - x + 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · linarith

/-- **The Menelaus criterion (cocycle form).** For a nonzero signed assignment `m`,
    the twisted cocycle law holds on all triples *iff* the Menelaus product is `-1`
    on every triangular 2-face. The face conditions generate the whole cocycle —
    the higher-dimensional analogue of "check Menelaus on each triangle". -/
theorem twisted_cocycle_iff_triangles (m : ι → ι → ℝ) (h0 : ∀ i j, m i j ≠ 0) :
    (∀ i j k, m i j * m j k = - m i k) ↔
    (∀ i j k, m i j * m j k * m k i = -1) := by
  constructor
  · -- twisted cocycle ⟹ Menelaus product -1 on every face
    intro hcoc i j k
    have hself : m i i = -1 := twisted_self m h0 hcoc i
    have hsw : m i k * m k i = 1 := by
      have hik := hcoc i k i        -- m i k * m k i = - m i i
      rw [hik, twisted_self m h0 hcoc i]; ring
    rw [hcoc i j k]                  -- m i j * m j k ↦ - m i k
    linear_combination -hsw
  · -- Menelaus product -1 on every face ⟹ twisted cocycle
    intro htri i j k
    have hself : ∀ x, m x x = -1 := fun x => cube_eq_neg_one (m x x) (htri x x x)
    have hsw : ∀ p q, m p q * m q p = 1 := by
      intro p q
      have h := htri p q p           -- m p q * m q p * m p p = -1
      rw [hself p] at h
      linear_combination -h
    have e := htri i j k             -- m i j * m j k * m k i = -1
    have hik := hsw i k              -- m i k * m k i = 1
    have hcancel : (m i j * m j k) * m k i = (- m i k) * m k i := by
      linear_combination e + hik
    exact mul_right_cancel₀ (h0 k i) hcancel

/-- **The transversal-hyperplane criterion.** For a nonzero signed assignment `m`,
    a transversal hyperplane realizing it exists *iff* the Menelaus product is `-1`
    on every triangular 2-face of the simplex. This is the Menelaus mirror of the
    parent's `concurrency_criterion`. -/
theorem menelaus_criterion (m : ι → ι → ℝ) (b : ι) (h0 : ∀ i j, m i j ≠ 0) :
    (∃ a : ι → ℝ, (∀ i, a i ≠ 0) ∧ ∀ i j, m i j = - a i / a j) ↔
    (∀ i j k, m i j * m j k * m k i = -1) := by
  constructor
  · rintro ⟨a, ha, hrep⟩ i j k
    rw [hrep i j, hrep j k, hrep k i]
    have hi := ha i; have hj := ha j; have hk := ha k
    field_simp
  · intro htri
    exact exists_values_of_twisted_cocycle m b h0
      ((twisted_cocycle_iff_triangles m h0).mpr htri)

-- ============================================================
-- PART 5: Ceva–Menelaus duality (the sign signature)
-- ============================================================

/-- **Duality bridge.** The signed Menelaus ratio is exactly the negated parent edge
    ratio with reversed orientation: `m i j = - r j i`. Collinearity (transversal)
    and concurrency differ only by this sign. -/
theorem menelausRatio_eq_neg_edgeRatio (a : ι → ℝ) (i j : ι) :
    menelausRatio a i j = - CevaHigherDim.edgeRatio a j i := by
  unfold menelausRatio CevaHigherDim.edgeRatio
  rw [neg_div]

/-- **The sign signature.** Around any 2-face, the Menelaus product is the *negation*
    of the Ceva product: `-1` for a transversal hyperplane versus `+1` for a
    concurrency point. The two classical theorems are one identity up to sign. -/
theorem menelaus_triangle_eq_neg_ceva (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (i j k : ι) :
    menelausRatio a i j * menelausRatio a j k * menelausRatio a k i =
      - (CevaHigherDim.edgeRatio a i j * CevaHigherDim.edgeRatio a j k
          * CevaHigherDim.edgeRatio a k i) := by
  have hce : CevaHigherDim.edgeRatio a i j * CevaHigherDim.edgeRatio a j k
      * CevaHigherDim.edgeRatio a k i = 1 := by
    unfold CevaHigherDim.edgeRatio
    have hi := ha i; have hj := ha j; have hk := ha k
    field_simp
  rw [menelausRatio_triangle a ha, hce]

-- ============================================================
-- PART 6: The tetrahedron (3-simplex), explicitly
-- ============================================================

/-- A transversal hyperplane meets face `0,1,2` of a tetrahedron with Menelaus
    product `-1`. -/
theorem tetra_face_menelaus (a : Fin 4 → ℝ) (ha : ∀ i, a i ≠ 0) :
    menelausRatio a 0 1 * menelausRatio a 1 2 * menelausRatio a 2 0 = -1 :=
  menelausRatio_triangle a ha 0 1 2

/-- The same hyperplane meets face `0,1,3` with Menelaus product `-1`. -/
theorem tetra_other_face_menelaus (a : Fin 4 → ℝ) (ha : ∀ i, a i ≠ 0) :
    menelausRatio a 0 1 * menelausRatio a 1 3 * menelausRatio a 3 0 = -1 :=
  menelausRatio_triangle a ha 0 1 3

/-- Going once around the closed quadrilateral walk `0 → 1 → 2 → 3 → 0` of the
    tetrahedron returns the even-length product `+1`. -/
theorem tetra_four_cycle (a : Fin 4 → ℝ) (ha : ∀ i, a i ≠ 0) :
    menelausRatio a 0 1 * menelausRatio a 1 2
      * menelausRatio a 2 3 * menelausRatio a 3 0 = 1 := by
  unfold menelausRatio
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2; have h3 := ha 3
  field_simp

end MenelausHigherDim
