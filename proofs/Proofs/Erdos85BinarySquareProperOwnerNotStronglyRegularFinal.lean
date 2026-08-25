import Proofs.Erdos85BinarySquareProperOwnerNotSRGCapstone
import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity
import Proofs.Erdos85BinarySquareCenteredOwnerTrace
import Proofs.Erdos85BinarySquareProperOwnerSrgBottomRoot

/-!
# Proper binary-square owner colors are not strongly regular

This file assembles the centered-rank obstruction with the strongly-regular
parameter and matrix identities.  The bottom-root scalar relation is kept as
an explicit input until its kernel extraction lemma is connected.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem regular_adjMatrix_mul_ones_real
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) :
    H.adjMatrix ℝ * Matrix.of (fun _ _ => (1 : ℝ)) =
      (k : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
  have hrow := H.adjMatrix_mulVec_const_apply (α := ℝ) (v := x) (a := (1 : ℝ))
  rw [hreg x] at hrow
  rw [Matrix.mulVec, dotProduct] at hrow
  simpa using hrow

private theorem ones_mul_regular_adjMatrix_real
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) :
    Matrix.of (fun _ _ => (1 : ℝ)) * H.adjMatrix ℝ =
      (k : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, one_mul]
  have hrow := H.adjMatrix_mulVec_const_apply (α := ℝ) (v := y) (a := (1 : ℝ))
  rw [hreg y] at hrow
  rw [Matrix.mulVec, dotProduct] at hrow
  simpa [SimpleGraph.adjMatrix_apply, H.adj_comm] using hrow

private theorem onesMatrix_sq_real
    {W : Type*} [Fintype W] [DecidableEq W] :
    (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix W W ℝ) *
        Matrix.of (fun _ _ => (1 : ℝ)) =
      (Fintype.card W : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext x y
  simp [Matrix.mul_apply]

/-- Graph-facing capstone conditional only on the scalar bottom-root relation.
The latter is forced by the already-banked exact `-m` kernel and is isolated
as a separate linear-algebra lemma. -/
theorem false_of_proper_owner_srg_of_bottom_root_relation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m lambda mu : ℕ}
    (hc : c.supp.ncard = q * m) (hm : 2 ≤ m) (hmq : m < q)
    (hSRG : (componentOwnerGraph G (secondOrderDefectGraph G) c).IsSRGWith
      (q * q) (m * (q - 1)) lambda mu)
    (hroot :
      (m : ℤ) * lambda - ((m : ℤ) - 1) * mu =
        (m : ℤ) * ((q : ℤ) - m - 1)) : False := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let A := O.adjMatrix ℝ
  let J : Matrix V V ℝ := Matrix.of fun _ _ => 1
  let M := A + (m : ℝ) • (1 : Matrix V V ℝ)
  let K := (q : ℝ) • M - (m : ℝ) • J
  have hkpos : 0 < m * (q - 1) := Nat.mul_pos (by omega) (by omega)
  have hnonempty : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    positivity
  let x : V := Classical.choice hnonempty
  have hxdeg : O.degree x = m * (q - 1) := hSRG.regular.degree_eq x
  have hxneigh : (O.neighborFinset x).Nonempty := by
    rw [← Finset.card_pos, O.card_neighborFinset_eq_degree, hxdeg]
    exact hkpos
  obtain ⟨y, hy⟩ := hxneigh
  have hxy : O.Adj x y := (O.mem_neighborFinset x y).mp hy
  have hlambda : lambda < m * (q - 1) := by
    rw [← hSRG.of_adj x y hxy, ← hxdeg]
    exact hxy.card_commonNeighbors_lt_degree
  have hparamNat := hSRG.param_eq O (by positivity : 0 < q * q)
  have hdegree_lt : m * (q - 1) < q * q := by
    calc
      m * (q - 1) ≤ m * q := Nat.mul_le_mul_left m (by omega)
      _ < q * q := Nat.mul_lt_mul_of_pos_right hmq (by omega)
  have hparam :
      ((m : ℤ) * ((q : ℤ) - 1)) *
          ((m : ℤ) * ((q : ℤ) - 1) - lambda - 1) =
        ((q : ℤ) * q - (m : ℤ) * ((q : ℤ) - 1) - 1) * mu := by
    have hp :
        ((m * (q - 1) : ℕ) : ℤ) *
            ((m * (q - 1) - lambda - 1 : ℕ) : ℤ) =
          ((q * q - m * (q - 1) - 1 : ℕ) : ℤ) * (mu : ℤ) := by
      exact_mod_cast hparamNat
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_sub (by omega : 1 ≤ m * (q - 1) - lambda),
      Nat.cast_sub (by omega : lambda ≤ m * (q - 1)),
      Nat.cast_sub (by omega : 1 ≤ q * q - m * (q - 1)),
      Nat.cast_sub (by omega : m * (q - 1) ≤ q * q),
      Nat.cast_mul, Nat.cast_one] at hp
    rw [Nat.cast_sub (by omega : 1 ≤ q)] at hp
    simpa using hp
  obtain ⟨hlambda, hmu⟩ := properOwner_srg_parameters_of_bottom_root
    (q := (q : ℤ)) (m := (m : ℤ)) (lambda := (lambda : ℤ))
      (mu := (mu : ℤ)) (by omega) (by omega) hroot hparam
  have hcoeff := properOwner_shifted_srg_coefficients hlambda hmu
  have hA2 := hSRG.matrix_eq (α := ℝ)
  have hcomp : Oᶜ.adjMatrix ℝ = J - 1 - A := by
    have hsum := O.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℝ)
    rw [O.compl_adjMatrix_eq_adjMatrix_compl ℝ] at hsum
    change Oᶜ.adjMatrix ℝ = Matrix.of 1 - 1 - O.adjMatrix ℝ
    rw [← hsum]
    module
  have hMquad : M * M = (q : ℝ) • M +
      ((m * (m - 1) : ℕ) : ℝ) • J := by
    have hA2R : A * A =
        (m * (q - 1) : ℝ) • (1 : Matrix V V ℝ) +
          (lambda : ℝ) • A + (mu : ℝ) • Oᶜ.adjMatrix ℝ := by
      simpa only [A, O, pow_two, ← Nat.cast_smul_eq_nsmul ℝ,
        Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] using hA2
    dsimp [M]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [hA2R, hcomp]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    have hcoeffR1 :
        (m : ℝ) * ((q : ℝ) - 1) - mu + (m : ℝ) * m = q * m := by
      exact_mod_cast hcoeff.1
    have hcoeffR2 :
        (lambda : ℝ) - mu + 2 * m = q := by
      exact_mod_cast hcoeff.2
    have hmuR : (mu : ℝ) = m * (m - 1) := by exact_mod_cast hmu
    have hlambdaR : (lambda : ℝ) = q + m * m - 3 * m := by
      exact_mod_cast hlambda
    rw [hmuR, hlambdaR]
    module
  have hOreg : ∀ z, O.degree z = m * (q - 1) :=
    hSRG.regular.degree_eq
  have hAJ : A * J = ((m * (q - 1) : ℕ) : ℝ) • J := by
    simpa [A, J] using regular_adjMatrix_mul_ones_real O _ hOreg
  have hJA : J * A = ((m * (q - 1) : ℕ) : ℝ) • J := by
    simpa [A, J] using ones_mul_regular_adjMatrix_real O _ hOreg
  have hMJ : M * J = ((q * m : ℕ) : ℝ) • J := by
    dsimp [M]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hAJ]
    rw [← add_smul]
    congr 1
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  have hJM : J * M = ((q * m : ℕ) : ℝ) • J := by
    dsimp [M]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hJA]
    rw [← add_smul]
    congr 1
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  have hJJ : J * J = ((q * q : ℕ) : ℝ) • J := by
    simpa [J, hcard] using (onesMatrix_sq_real (W := V))
  let KZ : Matrix V V ℤ :=
    (q : ℤ) • (O.adjMatrix ℤ + (m : ℤ) • (1 : Matrix V V ℤ)) -
      (m : ℤ) • FriendshipTheoremOQ01.onesMatrix V
  have hK : K = KZ.map (Int.castRingHom ℝ) := by
    ext u v
    simp only [K, KZ, M, A, J, FriendshipTheoremOQ01.onesMatrix,
      Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.of_apply, map_sub, Matrix.one_apply]
    norm_num [SimpleGraph.adjMatrix_apply]
  have hrank : K.rank = q * m - 1 := by
    rw [hK]
    exact binarySquare_regular_real_centeredOwnerGram_rank
      G hfree hq hreg hcard c hc
  have htraceZ := binarySquare_regular_trace_centeredOwnerGram
    G hfree hq hreg hcard c hc
  have htrace : K.trace = ((q * q * (m * (q - 1)) : ℕ) : ℝ) := by
    rw [hK]
    rw [← AddMonoidHom.map_trace (Int.castRingHom ℝ) KZ]
    rw [show KZ.trace = ((m * q * q * (q - 1) : ℕ) : ℤ) by
      simpa [KZ, O] using htraceZ]
    change ((((m * q * q * (q - 1) : ℕ) : ℤ)) : ℝ) = _
    push_cast
    ring
  exact false_of_proper_owner_shifted_srg_matrix_data
    M J (by omega) hm hMquad hMJ hJM hJJ hrank htrace

#print axioms false_of_proper_owner_srg_of_bottom_root_relation

/-- **Proper owner colors are not strongly regular.**  No owner belonging to
a normalized component `q*m` with `2 ≤ m < q` has any strongly-regular
parameter pair. -/
theorem false_of_binarySquare_regular_properOwner_srg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m lambda mu : ℕ}
    (hc : c.supp.ncard = q * m) (hm : 2 ≤ m) (hmq : m < q)
    (hSRG : (componentOwnerGraph G (secondOrderDefectGraph G) c).IsSRGWith
      (q * q) (m * (q - 1)) lambda mu) : False := by
  have hroot := binarySquare_regular_properOwner_srg_bottom_root_equation
    G hfree hq hreg hcard c (by omega : 1 ≤ m) hmq hc hSRG
  exact false_of_proper_owner_srg_of_bottom_root_relation
    G hfree hq hreg hcard c hc hm hmq hSRG hroot

/-- Quantifier-packaged form: a proper owner admits no SRG codegrees. -/
theorem binarySquare_regular_properOwner_not_exists_srg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m) (hm : 2 ≤ m) (hmq : m < q) :
    ¬ ∃ lambda mu,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).IsSRGWith
        (q * q) (m * (q - 1)) lambda mu := by
  rintro ⟨lambda, mu, hSRG⟩
  exact false_of_binarySquare_regular_properOwner_srg
    G hfree hq hreg hcard c hc hm hmq hSRG

#print axioms false_of_binarySquare_regular_properOwner_srg
#print axioms binarySquare_regular_properOwner_not_exists_srg

end

end Erdos85
