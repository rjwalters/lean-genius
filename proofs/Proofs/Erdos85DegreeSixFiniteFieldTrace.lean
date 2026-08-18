import Proofs.Erdos85TriangleDefectPolynomial
import Proofs.Erdos85SecondOrderQuotient
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField

/-!
# Finite-field trace certificate for the eleven-component quotient

For the all-triangle degree-six quotient, `Q²=3I+3J` and
`QJ=JQ=6J`.  Frobenius invariance of trace modulo 5 and 7 forces its
trace to be congruent to 6 modulo both primes.
-/

namespace Erdos85

open Matrix

def ffOnesMatrix (R : Type*) [OfNat R 1] (ι : Type*) : Matrix ι ι R :=
  fun _ _ => 1

theorem ffOnesMatrix_sq
    {R ι : Type*} [CommRing R] [Fintype ι]
    (J : Matrix ι ι R) (hJ : J = ffOnesMatrix R ι) :
    J * J = (Fintype.card ι : R) • J := by
  subst J
  ext i j
  simp [ffOnesMatrix, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]

theorem ffOnesMatrix_trace
    {R ι : Type*} [CommRing R] [Fintype ι]
    (J : Matrix ι ι R) (hJ : J = ffOnesMatrix R ι) :
    Matrix.trace J = (Fintype.card ι : R) := by
  subst J
  simp [ffOnesMatrix, Matrix.trace]

theorem degreeSixQuotient_pow_five
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q J : Matrix ι ι (ZMod 5))
    (hcard : Fintype.card ι = 11)
    (hQ2 : Q * Q = (3 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) +
      (3 : ZMod 5) • J)
    (hQJ : Q * J = (6 : ZMod 5) • J)
    (hJQ : J * Q = (6 : ZMod 5) • J)
    (hJ : J = ffOnesMatrix (ZMod 5) ι) :
    Q ^ 5 = -Q + (2 : ZMod 5) • J := by
  have hJ2 := ffOnesMatrix_sq J hJ
  rw [hcard] at hJ2
  have hQ4 : Q ^ 4 = (4 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) +
      (2 : ZMod 5) • J := by
    rw [show Q ^ 4 = (Q * Q) * (Q * Q) by noncomm_ring, hQ2]
    calc
      ((3 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) + (3 : ZMod 5) • J) *
          ((3 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) + (3 : ZMod 5) • J) =
          (9 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) +
            (18 : ZMod 5) • J + (9 : ZMod 5) • (J * J) := by
            simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
              Matrix.one_mul, Matrix.mul_one]
            module
      _ = (9 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) +
          (117 : ZMod 5) • J := by
        rw [hJ2]
        module
      _ = (4 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) +
          (2 : ZMod 5) • J := by
        rw [show (9 : ZMod 5) = 4 by decide,
          show (117 : ZMod 5) = 2 by decide]
  rw [show Q ^ 5 = Q ^ 4 * Q by noncomm_ring, hQ4]
  calc
    ((4 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) + (2 : ZMod 5) • J) * Q =
        (4 : ZMod 5) • Q + (2 : ZMod 5) • (J * Q) := by noncomm_ring
    _ = (4 : ZMod 5) • Q + (12 : ZMod 5) • J := by
      rw [hJQ]
      module
    _ = -Q + (2 : ZMod 5) • J := by
      rw [show (4 : ZMod 5) = -1 by decide,
        show (12 : ZMod 5) = 2 by decide]
      simp

theorem degreeSixQuotient_pow_seven
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q J : Matrix ι ι (ZMod 7))
    (hcard : Fintype.card ι = 11)
    (hQ2 : Q * Q = (3 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
      (3 : ZMod 7) • J)
    (hQJ : Q * J = (6 : ZMod 7) • J)
    (hJQ : J * Q = (6 : ZMod 7) • J)
    (hJ : J = ffOnesMatrix (ZMod 7) ι) :
    Q ^ 7 = -Q + (3 : ZMod 7) • J := by
  have hJ2 := ffOnesMatrix_sq J hJ
  rw [hcard] at hJ2
  have hQ4 : Q ^ 4 = (2 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
      (5 : ZMod 7) • J := by
    rw [show Q ^ 4 = (Q * Q) * (Q * Q) by noncomm_ring, hQ2]
    calc
      ((3 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) + (3 : ZMod 7) • J) *
          ((3 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) + (3 : ZMod 7) • J) =
          (9 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
            (18 : ZMod 7) • J + (9 : ZMod 7) • (J * J) := by
            simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
              Matrix.one_mul, Matrix.mul_one]
            module
      _ = (9 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
          (117 : ZMod 7) • J := by
        rw [hJ2]
        module
      _ = (2 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
          (5 : ZMod 7) • J := by
        rw [show (9 : ZMod 7) = 2 by decide,
          show (117 : ZMod 7) = 5 by decide]
  have hQ6 : Q ^ 6 = (6 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
      (4 : ZMod 7) • J := by
    rw [show Q ^ 6 = Q ^ 4 * (Q * Q) by noncomm_ring, hQ4, hQ2]
    calc
      ((2 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) + (5 : ZMod 7) • J) *
          ((3 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) + (3 : ZMod 7) • J) =
          (6 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
            (21 : ZMod 7) • J + (15 : ZMod 7) • (J * J) := by
            simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
              Matrix.one_mul, Matrix.mul_one]
            module
      _ = (6 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
          (186 : ZMod 7) • J := by
        rw [hJ2]
        module
      _ = (6 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
          (4 : ZMod 7) • J := by
        rw [show (186 : ZMod 7) = 4 by decide]
  rw [show Q ^ 7 = Q ^ 6 * Q by noncomm_ring, hQ6]
  calc
    ((6 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) + (4 : ZMod 7) • J) * Q =
        (6 : ZMod 7) • Q + (4 : ZMod 7) • (J * Q) := by noncomm_ring
    _ = (6 : ZMod 7) • Q + (24 : ZMod 7) • J := by
      rw [hJQ]
      module
    _ = -Q + (3 : ZMod 7) • J := by
      rw [show (6 : ZMod 7) = -1 by decide,
        show (24 : ZMod 7) = 3 by decide]
      simp

/-- The quotient trace is `6` modulo five. -/
theorem degreeSixQuotient_trace_mod_five
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q J : Matrix ι ι (ZMod 5))
    (hcard : Fintype.card ι = 11)
    (hQ2 : Q * Q = (3 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) +
      (3 : ZMod 5) • J)
    (hQJ : Q * J = (6 : ZMod 5) • J)
    (hJQ : J * Q = (6 : ZMod 5) • J)
    (hJ : J = ffOnesMatrix (ZMod 5) ι) :
    Matrix.trace Q = (6 : ZMod 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp := degreeSixQuotient_pow_five Q J hcard hQ2 hQJ hJQ hJ
  have hf := ZMod.trace_pow_card Q
  rw [hp] at hf
  have htrJ := ffOnesMatrix_trace J hJ
  rw [hcard] at htrJ
  rw [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, htrJ] at hf
  rw [ZMod.pow_card] at hf
  have hsolve : ∀ t : ZMod 5,
      -t + (2 : ZMod 5) * (11 : ZMod 5) = t → t = (6 : ZMod 5) := by
    decide
  apply hsolve (Matrix.trace Q)
  simpa [smul_eq_mul] using hf

/-- The quotient trace is `6` modulo seven. -/
theorem degreeSixQuotient_trace_mod_seven
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q J : Matrix ι ι (ZMod 7))
    (hcard : Fintype.card ι = 11)
    (hQ2 : Q * Q = (3 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) +
      (3 : ZMod 7) • J)
    (hQJ : Q * J = (6 : ZMod 7) • J)
    (hJQ : J * Q = (6 : ZMod 7) • J)
    (hJ : J = ffOnesMatrix (ZMod 7) ι) :
    Matrix.trace Q = (6 : ZMod 7) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp := degreeSixQuotient_pow_seven Q J hcard hQ2 hQJ hJQ hJ
  have hf := ZMod.trace_pow_card Q
  rw [hp] at hf
  have htrJ := ffOnesMatrix_trace J hJ
  rw [hcard] at htrJ
  rw [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, htrJ] at hf
  rw [ZMod.pow_card] at hf
  have hsolve : ∀ t : ZMod 7,
      -t + (3 : ZMod 7) * (11 : ZMod 7) = t → t = (6 : ZMod 7) := by
    decide
  apply hsolve (Matrix.trace Q)
  simpa [smul_eq_mul] using hf

/-- The two finite-field certificates determine a natural trace in the
quotient's a priori interval. -/
theorem nat_eq_six_of_le_eleven_of_mod_five_seven
    {t : ℕ} (ht : t ≤ 11)
    (h5 : (t : ZMod 5) = (6 : ZMod 5))
    (h7 : (t : ZMod 7) = (6 : ZMod 7)) : t = 6 := by
  have hm5 : t % 5 = 6 % 5 :=
    (ZMod.natCast_eq_natCast_iff' t 6 5).mp h5
  have hm7 : t % 7 = 6 % 7 :=
    (ZMod.natCast_eq_natCast_iff' t 6 7).mp h7
  omega

/-- If a natural symmetric matrix has each diagonal entry of its square equal
to the corresponding row sum, then all its entries are at most one. -/
theorem natMatrix_entry_le_one_of_sq_diag_eq_row
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℕ)
    (hsymm : ∀ i j, Q i j = Q j i)
    (hdiag : ∀ i, (Q * Q) i i = ∑ j, Q i j) :
    ∀ i j, Q i j ≤ 1 := by
  intro i j
  by_contra hnot
  have htwo : 2 ≤ Q i j := by omega
  have hle : ∀ k ∈ (Finset.univ : Finset ι),
      Q i k ≤ Q i k * Q k i := by
    intro k hk
    rw [← hsymm i k]
    exact Nat.le_mul_self _
  have hlt : Q i j < Q i j * Q j i := by
    rw [← hsymm i j]
    nlinarith
  have hsumlt : (∑ k, Q i k) < ∑ k, Q i k * Q k i :=
    Finset.sum_lt_sum hle ⟨j, Finset.mem_univ j, hlt⟩
  rw [← Matrix.mul_apply, hdiag i] at hsumlt
  omega

/-- An integral eleven-by-eleven quotient satisfying the triangle-component
square equation, with constant row and column sum six and `0/1` entries, has
trace exactly six.  This packages the two finite-field certificates in the
form needed by the graph quotient. -/
theorem degreeSixNatQuotient_trace_eq_six
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℕ)
    (hcard : Fintype.card ι = 11)
    (hQ2 : ∀ i j, (Q * Q) i j = 3 * (if i = j then 1 else 0) + 3)
    (hrow : ∀ i, ∑ j, Q i j = 6)
    (hcol : ∀ j, ∑ i, Q i j = 6)
    (hle : ∀ i j, Q i j ≤ 1) :
    Matrix.trace Q = 6 := by
  let J5 : Matrix ι ι (ZMod 5) := ffOnesMatrix (ZMod 5) ι
  let Q5 : Matrix ι ι (ZMod 5) := fun i j => Q i j
  have hQ2five : Q5 * Q5 =
      (3 : ZMod 5) • (1 : Matrix ι ι (ZMod 5)) + (3 : ZMod 5) • J5 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, J5, Q5, ffOnesMatrix]
    have hcast : (∑ k, (Q i k : ZMod 5) * (Q k j : ZMod 5)) =
        ((Q * Q) i j : ZMod 5) := by
      simp [Matrix.mul_apply]
    rw [hcast, hQ2]
    split_ifs <;> norm_num
  have hQJfive : Q5 * J5 = (6 : ZMod 5) • J5 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, J5, Q5, ffOnesMatrix,
      mul_one]
    rw [← Nat.cast_sum, hrow]
    norm_num
  have hJQfive : J5 * Q5 = (6 : ZMod 5) • J5 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, J5, Q5, ffOnesMatrix,
      one_mul]
    rw [← Nat.cast_sum, hcol]
    norm_num
  have hfive := degreeSixQuotient_trace_mod_five Q5 J5 hcard
    hQ2five hQJfive hJQfive rfl
  let J7 : Matrix ι ι (ZMod 7) := ffOnesMatrix (ZMod 7) ι
  let Q7 : Matrix ι ι (ZMod 7) := fun i j => Q i j
  have hQ2seven : Q7 * Q7 =
      (3 : ZMod 7) • (1 : Matrix ι ι (ZMod 7)) + (3 : ZMod 7) • J7 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, J7, Q7, ffOnesMatrix]
    have hcast : (∑ k, (Q i k : ZMod 7) * (Q k j : ZMod 7)) =
        ((Q * Q) i j : ZMod 7) := by
      simp [Matrix.mul_apply]
    rw [hcast, hQ2]
    split_ifs <;> norm_num
  have hQJseven : Q7 * J7 = (6 : ZMod 7) • J7 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, J7, Q7, ffOnesMatrix,
      mul_one]
    rw [← Nat.cast_sum, hrow]
    norm_num
  have hJQseven : J7 * Q7 = (6 : ZMod 7) • J7 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, J7, Q7, ffOnesMatrix,
      one_mul]
    rw [← Nat.cast_sum, hcol]
    norm_num
  have hseven := degreeSixQuotient_trace_mod_seven Q7 J7 hcard
    hQ2seven hQJseven hJQseven rfl
  have htrace_le : Matrix.trace Q ≤ 11 := by
    rw [Matrix.trace]
    calc
      (∑ i, Q i i) ≤ ∑ _ : ι, 1 := Finset.sum_le_sum fun i _ => hle i i
      _ = Fintype.card ι := by simp
      _ = 11 := hcard
  apply nat_eq_six_of_le_eleven_of_mod_five_seven htrace_le
  · simpa [Matrix.trace, Q5] using hfive
  · simpa [Matrix.trace, Q7] using hseven

/-- A finite graph on 33 vertices whose connected components all have order
three has exactly eleven connected components. -/
theorem card_connectedComponents_eq_eleven_of_all_order_three
    {V : Type*} [Fintype V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    (hcard : Fintype.card V = 33)
    (hthree : ∀ c : D.ConnectedComponent, c.supp.ncard = 3) :
    Fintype.card D.ConnectedComponent = 11 := by
  classical
  have hparts : (∑ c : D.ConnectedComponent, c.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ c : D.ConnectedComponent, c.supp.ncard) =
          ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
            apply Finset.sum_congr rfl
            intro c hc
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
  have hsum : (∑ c : D.ConnectedComponent, c.supp.ncard) =
      3 * Fintype.card D.ConnectedComponent := by
    simp [hthree, Nat.mul_comm]
  rw [hsum, hcard] at hparts
  omega

/-- If the diagonal entry indexed by a vertex depends only on its connected
component, and every component has order three, then the ambient trace is
three times the component trace.  This is the bookkeeping bridge used for
the eleven-triangle quotient. -/
theorem trace_eq_three_mul_component_trace
    {V : Type*} [Fintype V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    (M : Matrix V V ℚ)
    (Q : Matrix D.ConnectedComponent D.ConnectedComponent ℚ)
    (hthree : ∀ c : D.ConnectedComponent, c.supp.ncard = 3)
    (hdiag : ∀ x : V,
      M x x = Q (D.connectedComponentMk x) (D.connectedComponentMk x)) :
    Matrix.trace M = 3 * Matrix.trace Q := by
  classical
  rw [Matrix.trace, Matrix.trace]
  change (∑ i : V, M i i) = 3 * ∑ i : D.ConnectedComponent, Q i i
  have hreindex : (∑ i : V, M i i) =
      ∑ z : Σ c : D.ConnectedComponent, c.supp, M z.2.1 z.2.1 := by
    simpa [vertexConnectedComponentEquiv] using
      (Equiv.sum_comp (vertexConnectedComponentEquiv D)
        (fun z : Σ c : D.ConnectedComponent, c.supp => M z.2.1 z.2.1))
  rw [hreindex]
  simp only [hdiag]
  rw [Fintype.sum_sigma]
  calc
    (∑ c : D.ConnectedComponent, ∑ x : c.supp,
        Q (D.connectedComponentMk x.1) (D.connectedComponentMk x.1)) =
        ∑ c : D.ConnectedComponent, ∑ _x : c.supp, Q c c := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro x hx
      rw [(SimpleGraph.ConnectedComponent.mem_supp_iff c x.1).mp x.2]
    (∑ c : D.ConnectedComponent, ∑ _x : c.supp, Q c c) =
        ∑ c : D.ConnectedComponent, (3 : ℚ) * Q c c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hc3 : Fintype.card c.supp = 3 := by
        calc
          Fintype.card c.supp = c.supp.ncard := by
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp)
          _ = 3 := hthree c
      norm_num [hc3]
    _ = 3 * ∑ c : D.ConnectedComponent, Q c c := by
      rw [Finset.mul_sum]

/-- For an equitable partition into triangular components, the mixed trace
of the original adjacency matrix with the component graph is three times the
trace of the component quotient. -/
theorem trace_adjMatrix_mul_eq_three_mul_componentQuotient_trace
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (hreg : ∀ x : V, D.degree x = 2)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    (hthree : ∀ c : D.ConnectedComponent, c.supp.ncard = 3) :
    Matrix.trace (G.adjMatrix ℚ * D.adjMatrix ℚ) =
      3 * Matrix.trace
        ((componentQuotientMatrix G D).map (Nat.castRingHom ℚ)) := by
  apply trace_eq_three_mul_component_trace D
    (G.adjMatrix ℚ * D.adjMatrix ℚ)
    ((componentQuotientMatrix G D).map (Nat.castRingHom ℚ)) hthree
  intro x
  let c := D.connectedComponentMk x
  rw [D.mul_adjMatrix_apply]
  have hq := componentQuotientMatrix_apply_eq
    G D 2 hreg hcomm c c (x := x) (by rfl)
  change (∑ y ∈ D.neighborFinset x, G.adjMatrix ℚ x y) =
    ((componentQuotientMatrix G D c c : ℕ) : ℚ)
  rw [hq]
  have hsets : (D.neighborFinset x).filter (fun y => G.Adj x y) =
      componentNeighborFinset G D c x := by
    ext y
    rw [Finset.mem_filter]
    simp only [SimpleGraph.mem_neighborFinset, componentNeighborFinset,
      Finset.mem_filter]
    rw [adj_iff_ne_and_connectedComponentMk_eq_of_order_three D hreg hthree]
    constructor
    · rintro ⟨⟨hyx, hcomp⟩, hG⟩
      exact ⟨hG, hcomp.symm⟩
    · rintro ⟨hG, hcomp⟩
      exact ⟨⟨G.ne_of_adj hG, hcomp.symm⟩, hG⟩
  simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole, hsets]

/-- Graph-facing form of the finite-field certificate.  When the degree-six
second-order defect consists of eleven triangles, its equitable quotient has
trace six. -/
theorem secondOrder_componentQuotientMatrix_trace_eq_six_of_eleven_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hthree : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) :
    Matrix.trace (componentQuotientMatrix G (secondOrderDefectGraph G)) = 6 := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hcomponents : Fintype.card D.ConnectedComponent = 11 :=
    card_connectedComponents_eq_eleven_of_all_order_three D hcard hthree
  have hboundary : Fintype.card V = 6 * (6 - 1) + 3 := by
    norm_num [hcard]
  have hsymm : ∀ c e, Q c e = Q e c := by
    intro c e
    change componentQuotientMatrix G (secondOrderDefectGraph G) c e =
      componentQuotientMatrix G (secondOrderDefectGraph G) e c
    have hb := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary c e
    simp only [hthree] at hb
    omega
  have hQ2 : ∀ c e, (Q * Q) c e =
      3 * (if c = e then 1 else 0) + 3 := by
    intro c e
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary c e
    simpa [D, Q, hthree] using hs
  have hrow : ∀ c, ∑ e, Q c e = 6 := by
    intro c
    simpa [D, Q] using
      (sum_secondOrder_componentQuotientMatrix_row_eq_degree
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary c)
  have hcol : ∀ e, ∑ c, Q c e = 6 := by
    intro e
    calc
      (∑ c, Q c e) = ∑ c, Q e c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hsymm c e
      _ = 6 := hrow e
  have hdiag : ∀ c, (Q * Q) c c = ∑ e, Q c e := by
    intro c
    rw [hQ2 c c, hrow c]
    simp
  have hle := natMatrix_entry_le_one_of_sq_diag_eq_row Q hsymm hdiag
  exact degreeSixNatQuotient_trace_eq_six Q hcomponents hQ2 hrow hcol hle

/-- In the eleven-triangle degree-six boundary case, the mixed ambient trace
of the original adjacency matrix and the second-order defect matrix is 18. -/
theorem secondOrder_mixed_trace_eq_eighteen_of_eleven_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hthree : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) :
    Matrix.trace (G.adjMatrix ℚ *
      (secondOrderDefectGraph G).adjMatrix ℚ) = 18 := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hboundary : Fintype.card V = 6 * (6 - 1) + 3 := by
    norm_num [hcard]
  have hreg : ∀ x : V, D.degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two
      G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary
  have hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ :=
    adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary
  have hm := trace_adjMatrix_mul_eq_three_mul_componentQuotient_trace
    G D hreg hcomm hthree
  have hq := secondOrder_componentQuotientMatrix_trace_eq_six_of_eleven_triangles
    G hfree hmin hcard hthree
  have hqcast : Matrix.trace (Q.map (Nat.castRingHom ℚ)) = 6 := by
    change (∑ c, ((Q c c : ℕ) : ℚ)) = 6
    exact_mod_cast hq
  rw [hqcast] at hm
  norm_num at hm
  simpa [D] using hm

end Erdos85
