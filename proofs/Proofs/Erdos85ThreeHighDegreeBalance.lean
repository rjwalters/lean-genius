import Proofs.Erdos85ThreeHighCrossMargins

namespace Erdos85

/-- Count a rectangular Boolean matrix by rows or by columns. -/
theorem encodedRowDegree_sum_transpose {m n : Nat} (B : Fin m → Fin n → Bool) :
    (∑ i, encodedRowDegree (B i)) = ∑ j, encodedRowDegree (fun i => B i j) := by
  simp only [encodedRowDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossDomain_degree_balance
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R) :
    (∑ i, encodedRowDegree (U i)) = (∑ j, encodedRowDegree (R j)) + 34 := by
  have hm := threeHighCrossDomain_margins U R cross hc
  have hu : (∑ i, (encodedRowDegree (U i) + encodedRowDegree (cross i))) = 60 := by
    calc
      _ = ∑ _i : Fin 15, 4 := Finset.sum_congr rfl (fun i _ => hm.1 i)
      _ = 60 := by decide
  have hr : (∑ j : Fin 8, (encodedRowDegree (fun i => cross i j) +
      encodedRowDegree (R j) + (if j.val < 6 then 1 else 0))) = 32 := by
    calc
      _ = ∑ _j : Fin 8, 4 := Finset.sum_congr rfl (fun j _ => hm.2 j)
      _ = 32 := by decide
  have hb : (∑ j : Fin 8, (if j.val < 6 then 1 else 0 : Nat)) = 6 := by decide
  have he := encodedRowDegree_sum_transpose cross
  simp only [Finset.sum_add_distrib] at hu hr
  omega

end Erdos85
#print axioms Erdos85.encodedRowDegree_sum_transpose
#print axioms Erdos85.threeHighCrossDomain_degree_balance
