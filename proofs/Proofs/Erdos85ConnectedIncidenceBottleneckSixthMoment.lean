import Proofs.Erdos85ConnectedIncidenceBottleneckStrictResidue
import Proofs.Erdos85C4FreeFourthMoment

/-!
# Sixth-moment form of the connected incidence bottleneck

This converts the literal Frobenius energy of `E = AD-(J-A)` into a trace
polynomial in the ambient adjacency matrix.  At square order the principal
rank-one correction cancels exactly.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- Squared Frobenius energy is the trace of the square of a symmetric
matrix. -/
theorem sum_sq_eq_trace_sq_of_transpose_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Matrix V V ℤ) (hE : E.transpose = E) :
    (∑ x : V, ∑ y : V, (E x y) ^ 2) = Matrix.trace (E * E) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro y _
  have hsym : E y x = E x y := by
    have := congrFun (congrFun hE y) x
    simpa using this.symm
  rw [hsym, pow_two]

/-- Abstract square of the cubic bottleneck after the principal `J`-space
cancellation. -/
theorem incidenceBottleneck_cubic_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℤ) (q : ℕ)
    (hAJ : A * J = (q : ℤ) • J)
    (hJA : J * A = (q : ℤ) • J)
    (hJJ : J * J = ((q * q : ℕ) : ℤ) • J) :
    let E := (q : ℤ) • A - A * A * A + ((q : ℤ) - 1) • J
    E * E =
      A * A * A * A * A * A -
        (2 * (q : ℤ)) • (A * A * A * A) +
        ((q : ℤ) ^ 2) • (A * A) -
        (((q : ℤ) ^ 2) * ((q : ℤ) - 1) ^ 2) • J := by
  dsimp only
  have hA3J : (A * A * A) * J = ((q : ℤ) ^ 3) • J := by
    calc
      (A * A * A) * J = A * (A * (A * J)) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = A * (A * ((q : ℤ) • J)) := by rw [hAJ]
      _ = ((q : ℤ) ^ 3) • J := by
        simp only [Matrix.mul_smul, hAJ, smul_smul]
        congr 1 <;> ring
  have hJA3 : J * (A * A * A) = ((q : ℤ) ^ 3) • J := by
    calc
      J * (A * A * A) = ((J * A) * A) * A := by
        rw [← Matrix.mul_assoc J (A * A) A,
          ← Matrix.mul_assoc J A A]
      _ = (((q : ℤ) • J) * A) * A := by rw [hJA]
      _ = ((q : ℤ) ^ 3) • J := by
        simp only [Matrix.smul_mul, hJA, smul_smul]
        congr 1 <;> ring
  have hJJ' : J * J = ((q : ℤ) ^ 2) • J := by
    rw [hJJ]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, hAJ, hJA, hA3J, hJA3, hJJ']
  simp only [Matrix.mul_assoc]
  module

/-- Trace expansion of the cubic bottleneck Frobenius energy. -/
theorem incidenceBottleneck_cubic_frobenius_eq_sixthMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℤ) (q : ℕ)
    (hAt : A.transpose = A) (hJt : J.transpose = J)
    (hAJ : A * J = (q : ℤ) • J)
    (hJA : J * A = (q : ℤ) • J)
    (hJJ : J * J = ((q * q : ℕ) : ℤ) • J)
    (htraceJ : Matrix.trace J = (q * q : ℕ)) :
    let E := (q : ℤ) • A - A * A * A + ((q : ℤ) - 1) • J
    (∑ x : V, ∑ y : V, (E x y) ^ 2) =
      Matrix.trace (A * A * A * A * A * A) -
        2 * (q : ℤ) * Matrix.trace (A * A * A * A) +
        (q : ℤ) ^ 2 * Matrix.trace (A * A) -
        (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 := by
  dsimp only
  let E := (q : ℤ) • A - A * A * A + ((q : ℤ) - 1) • J
  have hEt : E.transpose = E := by
    dsimp [E]
    rw [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, hAt, hJt, Matrix.transpose_mul,
      Matrix.transpose_mul, hAt]
    simp only [Matrix.mul_assoc]
  rw [sum_sq_eq_trace_sq_of_transpose_eq E hEt,
    incidenceBottleneck_cubic_sq A J q hAJ hJA hJJ]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, htraceJ]
  push_cast
  ring

/-- Integral algebraic form of the incidence-bottleneck cubic identity. -/
theorem incidenceBottleneck_eq_cubic_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D J : Matrix V V ℤ) (q : ℕ)
    (hsq : A * A = ((q : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D)
    (hAJ : A * J = (q : ℤ) • J) :
    A * D - (J - A) =
      (q : ℤ) • A - A * A * A + ((q : ℤ) - 1) • J := by
  have hD : D = ((q : ℤ) - 1) • (1 : Matrix V V ℤ) + J - A * A := by
    rw [hsq]
    noncomm_ring
  rw [hD, Matrix.mul_sub, Matrix.mul_add, hAJ]
  simp only [Matrix.mul_smul, Matrix.mul_one]
  rw [Matrix.mul_assoc]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Exact graph-facing moment formula for the integral incidence
bottleneck. -/
theorem binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    (∑ x : V, ∑ y : V, (E x y) ^ 2) =
      Matrix.trace (A * A * A * A * A * A) -
        2 * (q : ℤ) * Matrix.trace (A * A * A * A) +
        (q : ℤ) ^ 2 * Matrix.trace (A * A) -
        (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 := by
  dsimp only
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := Matrix.of (fun _ _ : V => (1 : ℤ))
  have hsq : A * A = ((q : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D := by
    simpa [A, D, J, FriendshipTheoremOQ01.onesMatrix] using
      (adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg)
  have hAJ : A * J = (q : ℤ) • J := by
    simpa [A, J, FriendshipTheoremOQ01.onesMatrix] using
      (FriendshipTheoremOQ01.adjMatrix_mul_ones G q hreg)
  have hJA : J * A = (q : ℤ) • J := by
    simpa [A, J, FriendshipTheoremOQ01.onesMatrix] using
      (onesMatrix_mul_adjMatrix_of_regular G q hreg)
  have hJJ : J * J = ((q * q : ℕ) : ℤ) • J := by
    ext i j
    simp [J, Matrix.mul_apply, hcard]
  have hAt : A.transpose = A := by
    ext i j
    simp [A, SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hJt : J.transpose = J := by
    ext i j
    simp [J]
  have htraceJ : Matrix.trace J = (q * q : ℕ) := by
    simp [Matrix.trace, J, hcard]
  have hE := incidenceBottleneck_eq_cubic_int A D J q hsq hAJ
  rw [hE]
  exact incidenceBottleneck_cubic_frobenius_eq_sixthMoment
    A J q hAt hJt hAJ hJA hJJ htraceJ

/-- Using the regular second moment and the C4-free fourth moment, the
bottleneck energy is the sixth trace minus its explicit square-order
baseline. -/
theorem binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthTrace_sub_baseline
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    (∑ x : V, ∑ y : V, (E x y) ^ 2) =
      Matrix.trace (A * A * A * A * A * A) -
        (q : ℤ) ^ 6 - (q : ℤ) ^ 5 + (q : ℤ) ^ 4 := by
  dsimp only
  let A := G.adjMatrix ℤ
  have hmoment :=
    binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthMoment
      G hfree hreg hcard
  dsimp only at hmoment
  have htr2 : Matrix.trace (A * A) = (q * q : ℕ) * (q : ℤ) := by
    rw [← hcard]
    exact FriendshipTheoremOQ01.trace_adjMatrix_sq G q hreg
  have htr4raw := trace_adjMatrix_fourth_of_not_containsC4 G hfree
  have htr4 : Matrix.trace (A * A * A * A) =
      2 * ((q * q : ℕ) : ℤ) * (q : ℤ) ^ 2 -
        ((q * q : ℕ) : ℤ) * (q : ℤ) := by
    simp_rw [hreg] at htr4raw
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htr4raw
    rw [hcard] at htr4raw
    simp only [A, Matrix.mul_assoc] at htr4raw ⊢
    push_cast at htr4raw ⊢
    nlinarith
  rw [htr2, htr4] at hmoment
  push_cast at hmoment ⊢
  nlinarith

/-- Connected square-order binary data forces the sixth adjacency moment
strictly above the cubic-energy baseline in residue class one. -/
theorem connected_binarySquare_sixthMoment_ge_baseline_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 1)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    (q : ℤ) ^ 6 + (q : ℤ) ^ 5 - (q : ℤ) ^ 4 + (q : ℤ) ^ 3 + 2 ≤
      Matrix.trace
        (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ *
          G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) := by
  have henergy := connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_two
    G hfree hq hqeven hqmod hreg hcard hDconn
  have hmoment :=
    binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthTrace_sub_baseline
      G hfree hreg hcard
  dsimp only at henergy hmoment
  rw [hmoment] at henergy
  push_cast at henergy ⊢
  nlinarith

/-- Connected square-order binary data forces the sixth adjacency moment
four units above the cubic-energy baseline in residue class two. -/
theorem connected_binarySquare_sixthMoment_ge_baseline_add_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 2)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    (q : ℤ) ^ 6 + (q : ℤ) ^ 5 - (q : ℤ) ^ 4 + (q : ℤ) ^ 3 + 4 ≤
      Matrix.trace
        (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ *
          G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) := by
  have henergy := connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_four
    G hfree hq hqeven hqmod hreg hcard hDconn
  have hmoment :=
    binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthTrace_sub_baseline
      G hfree hreg hcard
  dsimp only at henergy hmoment
  rw [hmoment] at henergy
  push_cast at henergy ⊢
  nlinarith

end

end Erdos85

#print axioms Erdos85.sum_sq_eq_trace_sq_of_transpose_eq
#print axioms Erdos85.incidenceBottleneck_cubic_sq
#print axioms Erdos85.incidenceBottleneck_cubic_frobenius_eq_sixthMoment
#print axioms Erdos85.incidenceBottleneck_eq_cubic_int
#print axioms Erdos85.binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthMoment
#print axioms Erdos85.binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthTrace_sub_baseline
#print axioms Erdos85.connected_binarySquare_sixthMoment_ge_baseline_add_two
#print axioms Erdos85.connected_binarySquare_sixthMoment_ge_baseline_add_four
