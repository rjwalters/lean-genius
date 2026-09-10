import Proofs.Erdos85ThreeHighRSwapColumnDFS

namespace Erdos85

inductive ThreeHighColumnCut where
  | row (i : Fin 15)
  | rectangle (x y a b : Fin 24)
  | order (a b : Fin 8)

def threeHighColumnCutCheck (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (k : Nat) (cross : ThreeHighCross) : ThreeHighColumnCut → Bool
  | .row i => decide (4 < encodedRowDegree (U i) + encodedRowDegree (cross i) ∨
      encodedRowDegree (U i) + encodedRowDegree (cross i) + (8-k) < 4)
  | .rectangle x y a b =>
      let B := threeHighEmptyAdj U R cross
      decide (x ≠ y ∧ a ≠ b) && B x a && B y a && B x b && B y b
  | .order a b => decide ((a,b) ∈ pairs ∧ a.val < k ∧ b.val < k) &&
      decide (score (fun i => cross i b) < score (fun i => cross i a))

theorem threeHighColumnCutCheck_false_of_valid
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (k : Nat) (cross : ThreeHighCross)
    (hr : threeHighColumnRowCapacity U cross k = true)
    (hf : encodedC4Free (threeHighEmptyAdj U R cross) = true)
    (ho : threeHighRSwapPrefixOrdered pairs score cross k = true)
    (reason : ThreeHighColumnCut) : threeHighColumnCutCheck U R pairs score k cross reason = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  cases reason with
  | row i =>
    simp only [threeHighColumnCutCheck,decide_eq_true_eq] at h
    simp only [threeHighColumnRowCapacity,threeHighColumnRowCapacityFor,decide_eq_true_eq] at hr
    have hi := hr i
    omega
  | rectangle x y a b =>
    simp only [threeHighColumnCutCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    unfold encodedC4Free at hf
    simp only [decide_eq_true_eq] at hf
    have mem (z : Fin 24) (hx : threeHighEmptyAdj U R cross x z = true)
        (hy : threeHighEmptyAdj U R cross y z = true) :
        z ∈ Finset.univ.filter (fun w => threeHighEmptyAdj U R cross x w && threeHighEmptyAdj U R cross y w) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simp only [Bool.and_eq_true]; exact ⟨hx,hy⟩⟩
    exact h.1.1.1.1.2 (Finset.card_le_one.mp (hf x y h.1.1.1.1.1)
      a (mem a h.1.1.1.2 h.1.1.2) b (mem b h.1.2 h.2))
  | order a b =>
    simp only [threeHighColumnCutCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    have hh := List.all_eq_true.mp ho (a,b) h.1.1
    simp only [h.1.2.1,h.1.2.2,and_self,if_true,decide_eq_true_eq] at hh
    omega

attribute [local irreducible] threeHighCrossDomain

theorem threeHighColumnCutCheck_prefix_false
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (ho : threeHighRSwapOrdered pairs score cross = true) (k : Nat) (reason : ThreeHighColumnCut) :
    threeHighColumnCutCheck U R pairs score k (threeHighCrossColumnPrefix cross k) reason = false := by
  apply threeHighColumnCutCheck_false_of_valid
  · exact threeHighCrossDomain_column_prefix_capacity U R cross hc k
  · exact encodedC4Free_of_subgraph _ _ (threeHighCrossColumnPrefix_subgraph U R cross k)
      ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  · exact threeHighRSwapPrefixOrdered_of_ordered pairs score cross ho k

end Erdos85
#print axioms Erdos85.threeHighColumnCutCheck_false_of_valid
#print axioms Erdos85.threeHighColumnCutCheck_prefix_false
