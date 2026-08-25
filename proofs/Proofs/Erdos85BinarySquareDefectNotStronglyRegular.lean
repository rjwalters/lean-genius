import Mathlib

/-!
# A square-order deficiency graph is not primitive strongly regular

The strongly-regular parameter equation is already incompatible with a
connected `(q - 1)`-regular graph on `q²` vertices.  This isolates a genuine
uniform child of the connected A-REG obstruction: its deficiency graph must
have coherent rank at least four.
-/

open SimpleGraph

namespace Erdos85

/-- The strongly-regular parameter equation at order `q²` and degree `q-1`
forces the nonadjacent codegree `μ` to vanish. -/
theorem squareOrder_degree_pred_srg_mu_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {q ℓ μ : ℕ} (hq : 2 ≤ q)
    (hSRG : D.IsSRGWith (q * q) (q - 1) ℓ μ) :
    μ = 0 := by
  have hparam := hSRG.param_eq D (by nlinarith)
  have hleft :
      (q - 1) * (q - 1 - ℓ - 1) ≤ (q - 1) * (q - 2) := by
    apply Nat.mul_le_mul_left
    omega
  have hcoef : q * q - (q - 1) - 1 = q * (q - 1) := by
    have hsplit : q * q = q * (q - 1) + q := by
      calc
        q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = q * (q - 1) + q := by ring
    omega
  rw [hcoef] at hparam
  by_contra hμ
  have hμpos : 1 ≤ μ := Nat.one_le_iff_ne_zero.mpr hμ
  have hright : q * (q - 1) ≤ q * (q - 1) * μ := by
    have := Nat.mul_le_mul_left (q * (q - 1)) hμpos
    simpa [Nat.mul_assoc] using this
  rw [← hparam] at hright
  have hstrict : (q - 1) * (q - 2) < q * (q - 1) := by
    calc
      (q - 1) * (q - 2) < (q - 1) * q :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      _ = q * (q - 1) := Nat.mul_comm _ _
  exact (not_lt_of_ge hright) (lt_of_le_of_lt hleft hstrict)

theorem squareOrder_degree_pred_srg_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {q ℓ μ : ℕ} (hq : 2 ≤ q)
    (hSRG : D.IsSRGWith (q * q) (q - 1) ℓ μ) :
    ¬ D.Connected := by
  have hμ : μ = 0 := squareOrder_degree_pred_srg_mu_eq_zero D hq hSRG
  have htrans : ∀ {x y z : V}, D.Adj x y → D.Adj y z → x ≠ z → D.Adj x z := by
    intro x y z hxy hyz hxz
    by_contra hxzAdj
    have hcard := hSRG.of_not_adj hxz hxzAdj
    have hy : y ∈ D.commonNeighbors x z := by
      rw [SimpleGraph.mem_commonNeighbors]
      exact ⟨hxy, hyz.symm⟩
    have hpos : 0 < Fintype.card (D.commonNeighbors x z) :=
      Fintype.card_pos_iff.mpr ⟨⟨y, hy⟩⟩
    omega
  intro hconn
  have hcollapse : ∀ {x z : V}, D.Reachable x z → x = z ∨ D.Adj x z := by
    intro x z hreach
    obtain ⟨p⟩ := hreach
    induction p with
    | nil => exact Or.inl rfl
    | @cons x y z hxy p ih =>
        rcases ih with rfl | hxz
        · exact Or.inr hxy
        · by_cases h : x = z
          · exact Or.inl h
          · exact Or.inr (htrans hxy hxz h)
  have hcomplete : D = ⊤ := by
    apply top_unique
    intro x z hxz
    have hr := hcollapse (hconn x z)
    rcases hr with h | h
    · exact (hxz h).elim
    · exact h
  subst D
  let v : V := Classical.choice hconn.nonempty
  have hdegree := hSRG.regular.degree_eq v
  have hcard := hSRG.card
  change (completeGraph V).degree v = q - 1 at hdegree
  simp_rw [degree] at hdegree
  simp_rw [neighborFinset_eq_filter] at hdegree
  simp_rw [top_adj] at hdegree
  have hfilter : ({x | v ≠ x} : Finset V) = Finset.univ.erase v := by
    ext x
    simp [ne_comm]
  rw [hfilter] at hdegree
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at hdegree
  rw [hcard] at hdegree
  have hqpos : 1 ≤ q := by omega
  have hqqpos : 1 ≤ q * q := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  have hpred := Nat.sub_add_cancel hqpos
  have hsqpred := Nat.sub_add_cancel hqqpos
  nlinarith

#print axioms squareOrder_degree_pred_srg_not_connected

#print axioms squareOrder_degree_pred_srg_mu_eq_zero

end Erdos85
