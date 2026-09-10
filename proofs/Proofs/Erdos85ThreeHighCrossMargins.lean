import Proofs.Erdos85ThreeHighCrossDomain

namespace Erdos85

def encodedRowDegree {W : Type*} [Fintype W] (B : W → Bool) : ℕ :=
  (Finset.univ.filter fun q => B q).card

private theorem encodedRowDegree_sum {W : Type*} [Fintype W] (B : W → Bool) :
    encodedRowDegree B = ∑ q, if B q then 1 else 0 := by
  simp only [encodedRowDegree, Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem sum_empty_coordinates (f : Fin 24 → ℕ) :
    (∑ p, f p) = (∑ i, f (threeHighEmptyUIndex i)) +
      (∑ j, f (threeHighEmptyRIndex j)) + f 23 := by
  rw [Fin.sum_univ_add (a := 23) (b := 1), Fin.sum_univ_add (a := 15) (b := 8),
    Fin.sum_univ_one]
  rfl

theorem threeHighEmptyAdj_u_degree
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (i : Fin 15) :
    encodedRowDegree (threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyUIndex i)) =
      encodedRowDegree (UAdj i) + encodedRowDegree (cross i) := by
  simp only [encodedRowDegree_sum]
  rw [sum_empty_coordinates]
  simp only [threeHighEmptyAdj, threeHighEmptySplit_u, threeHighEmptySplit_r,
    threeHighEmptySplit_root, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem threeHighEmptyAdj_r_degree
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (j : Fin 8) :
    encodedRowDegree (threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyRIndex j)) =
      encodedRowDegree (fun i => cross i j) + encodedRowDegree (RAdj j) +
        (if j.val < 6 then 1 else 0) := by
  simp only [encodedRowDegree_sum]
  rw [sum_empty_coordinates]
  simp only [threeHighEmptyAdj, threeHighEmptySplit_u, threeHighEmptySplit_r,
    threeHighEmptySplit_root, decide_eq_true_eq]

attribute [local irreducible] threeHighCrossDomain encodedC4Free

theorem threeHighCrossDomain_margins
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj) :
    (∀ i, encodedRowDegree (UAdj i) + encodedRowDegree (cross i) = 4) ∧
    (∀ j, encodedRowDegree (fun i => cross i j) + encodedRowDegree (RAdj j) +
      (if j.val < 6 then 1 else 0) = 4) := by
  have hd := (mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc |>.2
  simp only [encodedDegreeProfile, decide_eq_true_eq] at hd
  have hp : ∀ p, encodedRowDegree (threeHighEmptyAdj UAdj RAdj cross p) =
      if p = 23 then 6 else 4 := hd
  constructor
  · intro i
    have hi : threeHighEmptyUIndex i ≠ 23 := by
      intro h
      have hv := congrArg (fun p : Fin 24 => p.val) h
      change i.val = 23 at hv
      omega
    simpa only [threeHighEmptyAdj_u_degree, if_neg hi] using hp (threeHighEmptyUIndex i)
  · intro j
    have hj : threeHighEmptyRIndex j ≠ 23 := by
      intro h
      have hv := congrArg (fun p : Fin 24 => p.val) h
      change 15 + j.val = 23 at hv
      omega
    simpa only [threeHighEmptyAdj_r_degree, if_neg hj] using hp (threeHighEmptyRIndex j)

end Erdos85
#print axioms Erdos85.threeHighEmptyAdj_u_degree
#print axioms Erdos85.threeHighEmptyAdj_r_degree
#print axioms Erdos85.threeHighCrossDomain_margins
