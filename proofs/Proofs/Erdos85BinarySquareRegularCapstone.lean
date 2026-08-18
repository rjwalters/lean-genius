import Proofs.Erdos85BinarySquareOrderReduction
import Proofs.Erdos85SquareOrderHighNeighborParity

/-! # Binary square-order capstone: A-REG alone suffices

The uniform parity theorem `squareOrder_regular_of_even` shows that for even
`d` every tight-edge-cover C4-free core on `d²` vertices with minimum degree
`d` is `d`-regular.  Hence the only remaining hypothesis of the binary branch
is the regular exclusion `AXIOM A-REG`; the former `AXIOM A-CAPSTONE` (node 21
of `FINAL_PROOF_OUTLINE.md`) is a theorem. -/

open SimpleGraph

namespace Erdos85

/-- **AXIOM A-REG** as a proposition: for every `k ≥ 3` there is no
`2^k`-regular C4-free graph on `4^k` vertices. -/
def BinarySquareRegularExclusion : Prop :=
  ∀ k : Nat, 3 ≤ k →
    ¬ ∃ (G : SimpleGraph (Fin (2 ^ k * 2 ^ k))) (_ : DecidableRel G.Adj),
      ¬ containsC4 (Fin (2 ^ k * 2 ^ k)) G ∧ ∀ x, G.degree x = 2 ^ k

/-- Every normalized binary tight core is regular (uniform parity theorem). -/
theorem squareOrderTightCore_regular_of_two_pow
    {k : Nat} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin (2 ^ k * 2 ^ k))) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin (2 ^ k * 2 ^ k)) G)
    (hmin : 2 ^ k ≤ G.minDegree)
    (hcover : ∀ ⦃u v⦄, G.Adj u v → G.degree u = 2 ^ k ∨ G.degree v = 2 ^ k) :
    ∀ x, G.degree x = 2 ^ k := by
  classical
  have hd : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have heven : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  exact squareOrder_regular_of_even G hfree hd heven
    (fun x => le_trans hmin (G.minDegree_le_degree x))
    (fun {u v} h => hcover h) (by simp)

/-- **A-CAPSTONE is a theorem**: the regular exclusion implies the normalized
tight-core exclusion, i.e. A-REG is the sole remaining hypothesis of Branch A. -/
theorem binarySquareOrderTightCoreExclusion_of_regularExclusion
    (h : BinarySquareRegularExclusion) : BinarySquareOrderTightCoreExclusion := by
  intro k hk hcore
  rcases hcore with ⟨G, hdec, hfree, hmin, _hminimal, hcover, _hslide⟩
  letI := hdec
  exact h k hk ⟨G, hdec, hfree,
    squareOrderTightCore_regular_of_two_pow hk G hfree hmin hcover⟩

/-- Erdős 85 is false assuming only A-REG. -/
theorem not_erdos85Question_of_binarySquareRegularExclusion
    (h : BinarySquareRegularExclusion) : ¬ Erdos85Question :=
  not_erdos85Question_of_binarySquareOrderTightCoreExclusion
    (binarySquareOrderTightCoreExclusion_of_regularExclusion h)

end Erdos85
