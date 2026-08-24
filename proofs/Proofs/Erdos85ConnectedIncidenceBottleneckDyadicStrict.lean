import Proofs.Erdos85ConnectedIncidenceBottleneckStrictResidue

/-!
# Strict connected incidence energy at dyadic parameters

Powers of two alternate between residues one and two modulo three.  Thus the
two strict residue bounds cover every parameter in the binary branch.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every power of two is congruent to one or two modulo three. -/
theorem two_pow_mod_three_eq_one_or_two (k : ℕ) :
    2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rcases ih with hk | hk
      · right
        rw [pow_succ, Nat.mul_mod, hk]
      · left
        rw [pow_succ, Nat.mul_mod, hk]

/-- At every dyadic parameter in the connected binary-square branch, the
incidence bottleneck exceeds its cubic baseline by at least two. -/
theorem connected_binarySquare_dyadic_incidenceBottleneck_energy_ge_cube_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    ((q * q * q + 2 : ℕ) : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    rw [hk0] at hqpow
    simp at hqpow
    omega
  have hqEven : Even q := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    use 2 ^ j
    rw [hqpow, pow_succ]
    ring
  rcases two_pow_mod_three_eq_one_or_two k with hmod | hmod
  · apply connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_two
      G hfree hq hqEven
    · simpa [hqpow] using hmod
    · exact hreg
    · exact hcard
    · exact hDconn
  · have hstrong :=
      connected_binarySquare_incidenceBottleneck_energy_ge_cube_add_four
        G hfree hq hqEven (by simpa [hqpow] using hmod)
          hreg hcard hDconn
    dsimp only at hstrong ⊢
    have hle : ((q * q * q + 2 : ℕ) : ℤ) ≤
        ((q * q * q + 4 : ℕ) : ℤ) := by omega
    exact hle.trans hstrong

end

end Erdos85

#print axioms Erdos85.two_pow_mod_three_eq_one_or_two
#print axioms Erdos85.connected_binarySquare_dyadic_incidenceBottleneck_energy_ge_cube_add_two
