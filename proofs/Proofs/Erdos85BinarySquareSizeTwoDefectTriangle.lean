import Mathlib

/-! # A triangle in a nonbipartite size-two defect component

The triangle-free case of the Andrasfai--Erdos--Sos minimum-degree theorem
turns the normalized size-two component arithmetic into an actual triangle.
This is the q-generic graph-theoretic input used by the `[q-2,2]` exterior
carrier argument.
-/

open SimpleGraph

namespace Erdos85

/-- A nonbipartite `(q-1)`-regular graph on `2q` vertices contains a triangle
as soon as `q >= 6`.  In the binary-square application `q=2^k`, `k>=3`, so
the strict Andrasfai--Erdos--Sos threshold is automatic. -/
theorem not_cliqueFree_three_of_card_two_mul_regular_not_bipartite
    {V : Type*} [Fintype V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (q : ℕ) (hq : 6 ≤ q)
    (hcard : Fintype.card V = 2 * q)
    (hreg : D.IsRegularOfDegree (q - 1))
    (hnb : ¬ D.IsBipartite) :
    ¬ D.CliqueFree 3 := by
  have hcardpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hcardpos
  intro htri
  apply hnb
  refine colorable_of_cliqueFree_lt_minDegree (r := 2)
    (show D.CliqueFree (2 + 1) from htri) ?_
  rw [hreg.minDegree_eq, hcard]
  omega

end Erdos85

#print axioms Erdos85.not_cliqueFree_three_of_card_two_mul_regular_not_bipartite
