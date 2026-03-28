/-
  Union Avoidance Fails over Finite Fields — But Cyclic Vectors Still Exist

  Over infinite fields, the nonderogatory → cyclic vector proof uses union
  avoidance: finitely many proper subspaces cannot cover the whole space.
  Over small finite fields F_q with q ≤ n, this FAILS: the space CAN be
  covered by proper subspaces.

  COUNTEREXAMPLE (Section I): Over F_2, the vector space F_2^2 has exactly
  3 one-dimensional subspaces (lines through the origin): {(0,0),(1,0)},
  {(0,0),(0,1)}, {(0,0),(1,1)}. Their union covers all 4 elements of F_2^2.

  DESPITE THIS (Section II): The cyclic vector theorem STILL HOLDS for all
  fields, including finite ones. The correct proof uses module theory
  (structure theorem for f.g. modules over PIDs) rather than union avoidance.

  KEY INSIGHT: For a nonderogatory matrix M (minpoly = charpoly), the
  annihilator of a vector v (the ideal {p : p(M)v = 0}) characterizes
  cyclicity: v is cyclic iff ann(v) = (minpoly M). This works over any field.

  REFERENCES:
  - CayleyHamiltonMinpolyOQ05OQ01.lean: infinite field proof (union avoidance)
  - CayleyHamiltonMinpolyOQ05OQ01OQ03.lean: module-theoretic framework
-/
import Mathlib

noncomputable section

namespace FiniteFieldCyclicVector

open Polynomial Matrix

-- ============================================================
-- SECTION I: Union Avoidance Fails over F_2
-- ============================================================

/-- Over F_2, the three 1-dimensional subspaces of F_2^2 cover the
    entire space. This shows union avoidance fails for |K| ≤ n. -/
section F2Counterexample

/-- The three nonzero elements of F_2^2. -/
def e1 : Fin 2 → ZMod 2 := ![1, 0]
def e2 : Fin 2 → ZMod 2 := ![0, 1]
def e12 : Fin 2 → ZMod 2 := ![1, 1]

/-- F_2^2 has exactly 4 elements: 0, e1, e2, e1+e2. -/
theorem F2_sq_elements (v : Fin 2 → ZMod 2) :
    v = 0 ∨ v = e1 ∨ v = e2 ∨ v = e12 := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  simp only [ZMod.card] at h0 h1
  -- Each component is 0 or 1 in F_2
  have hv0 : v 0 = 0 ∨ v 0 = 1 := by omega
  have hv1 : v 1 = 0 ∨ v 1 = 1 := by omega
  rcases hv0 with h0 | h0 <;> rcases hv1 with h1 | h1
  · left; ext i; fin_cases i <;> simp_all
  · right; right; left; ext i; fin_cases i <;> simp_all [e2]
  · right; left; ext i; fin_cases i <;> simp_all [e1]
  · right; right; right; ext i; fin_cases i <;> simp_all [e12]

/-- The subspace spanned by e1 = (1,0). -/
def L1 : Submodule (ZMod 2) (Fin 2 → ZMod 2) :=
  Submodule.span (ZMod 2) {e1}

/-- The subspace spanned by e2 = (0,1). -/
def L2 : Submodule (ZMod 2) (Fin 2 → ZMod 2) :=
  Submodule.span (ZMod 2) {e2}

/-- The subspace spanned by e12 = (1,1). -/
def L3 : Submodule (ZMod 2) (Fin 2 → ZMod 2) :=
  Submodule.span (ZMod 2) {e12}

/-- Each of L1, L2, L3 is a proper subspace. -/
theorem L1_ne_top : L1 ≠ ⊤ := by
  intro h
  have : e2 ∈ L1 := h ▸ Submodule.mem_top
  rw [L1, Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  have h0 : (a • e1) 1 = e2 1 := congr_fun ha 1
  simp [e1, e2] at h0

theorem L2_ne_top : L2 ≠ ⊤ := by
  intro h
  have : e1 ∈ L2 := h ▸ Submodule.mem_top
  rw [L2, Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  have h0 : (a • e2) 0 = e1 0 := congr_fun ha 0
  simp [e1, e2] at h0

theorem L3_ne_top : L3 ≠ ⊤ := by
  intro h
  have : e1 ∈ L3 := h ▸ Submodule.mem_top
  rw [L3, Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  have h0 : (a • e12) 0 = e1 0 := congr_fun ha 0
  have h1 : (a • e12) 1 = e1 1 := congr_fun ha 1
  simp [e1, e12] at h0 h1
  -- a = 1 from component 0, but then component 1 gives 1 = 0
  subst h0; simp at h1

/-- The union of L1, L2, L3 covers all of F_2^2.
    This is the counterexample: union avoidance fails over F_2. -/
theorem F2_union_covers :
    ∀ v : Fin 2 → ZMod 2,
      v ∈ L1 ∨ v ∈ L2 ∨ v ∈ L3 := by
  intro v
  rcases F2_sq_elements v with rfl | rfl | rfl | rfl
  · left; exact Submodule.zero_mem _
  · left; exact Submodule.subset_span (Set.mem_singleton _)
  · right; left; exact Submodule.subset_span (Set.mem_singleton _)
  · right; right; exact Submodule.subset_span (Set.mem_singleton _)

end F2Counterexample

-- ============================================================
-- SECTION II: Annihilator Characterization (Any Field)
-- ============================================================

section AnnihilatorChar

variable {K : Type*} [Field K] {n : ℕ}

/-- The annihilator polynomial of v under M: the monic generator of
    the ideal {p : p(M)v = 0}. This equals the minimal polynomial
    of v viewed as an element of the K[X]-module K^n (via M). -/
def annPoly (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : K[X] :=
  minpoly K (⟨v, Submodule.mem_top⟩ : (⊤ : Submodule K (Fin n → K)))

/-- The annihilator polynomial divides the minimal polynomial of M.
    This holds because minpoly(M) annihilates ALL vectors. -/
theorem annPoly_dvd_minpoly (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    annPoly M v ∣ minpoly K M := by
  sorry -- Requires connecting module-element minpoly to matrix minpoly

/-- If p(M)v = 0, then annPoly v divides p.
    The annihilator polynomial is the minimal-degree annihilator. -/
theorem annPoly_dvd_of_aeval_eq_zero (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (p : K[X]) (hp : (aeval M p).mulVec v = 0) :
    annPoly M v ∣ p := by
  sorry -- Requires connecting mulVec annihilation to module minpoly

/-- Forward direction: if v is cyclic (in the matrix sense from OQ05OQ01),
    then annPoly(v) = minpoly(M) (up to units).

    Proof: If v is cyclic, no nonzero p of deg < n = deg(minpoly) annihilates v.
    So annPoly(v) has degree ≥ deg(minpoly). Combined with annPoly | minpoly,
    we get annPoly = minpoly (both monic). -/
theorem cyclic_implies_ann_eq_minpoly (M : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (hM : minpoly K M = M.charpoly)
    (v : Fin n → K) (hv : ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0) :
    annPoly M v = minpoly K M := by
  sorry -- Requires degree comparison + divisibility

-- ============================================================
-- SECTION III: Main Theorem (Any Field)
-- ============================================================

/-- The cyclic vector theorem holds over ANY field K, not just infinite ones.
    If M is nonderogatory (minpoly = charpoly), then M has a cyclic vector.

    Over infinite fields: proved via union avoidance (OQ05OQ01.lean).
    Over finite fields: union avoidance fails, but the structure theorem
    for f.g. modules over the PID K[X] shows: nonderogatory forces the
    module K^n ≅ K[X]/(charpoly) to have a single invariant factor,
    making it cyclic. Any generator of this cyclic module is a cyclic vector.

    The finite-field case requires the structure theorem for finitely
    generated modules over a PID, which is not yet available in Mathlib. -/
theorem nonderogatory_has_cyclic_vector_any_field
    (M : Matrix (Fin n) (Fin n) K) (hn : 0 < n) (hM : minpoly K M = M.charpoly) :
    ∃ v : Fin n → K, ∀ p : K[X],
      p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0 := by
  sorry -- Requires structure theorem for f.g. modules over PIDs

-- ============================================================
-- SECTION IV: Threshold Characterization
-- ============================================================

/-- Union avoidance DOES hold when |K| > number of irreducible factors.

    For a nonderogatory M ∈ M_n(K), the minimal polynomial μ = charpoly
    has at most n irreducible factors (since deg μ = n). The union avoidance
    argument from OQ05OQ01 works when |K| ≥ n (more precisely, when
    |K| > number of distinct irreducible factors of μ).

    So the union avoidance proof covers:
    - All infinite fields (|K| = ∞ > n)
    - Finite fields F_q with q > n
    Only F_q with q ≤ n requires the module-theoretic approach. -/
theorem nonderogatory_cyclic_large_field [Infinite K]
    (M : Matrix (Fin n) (Fin n) K) (hn : 0 < n) (hM : minpoly K M = M.charpoly) :
    ∃ v : Fin n → K, ∀ p : K[X],
      p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0 := by
  -- This is exactly the theorem from CayleyHamiltonMinpolyOQ05OQ01.lean
  -- (nonderogatory_has_cyclic_vector) using union avoidance.
  sorry

end AnnihilatorChar

end FiniteFieldCyclicVector

end
