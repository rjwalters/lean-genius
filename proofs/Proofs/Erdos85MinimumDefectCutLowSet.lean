import Proofs.Erdos85TwoSeparatorCutRigidity

/-!
# The low set of a minimum defect cut

Equality in the regular-square cut variance bound makes every adjacency
occupancy take one of two consecutive values.  For a shore of residue
`q-1`, exactly `q` vertices take the lower value.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A `q-1` defect cut whose shore has residue `q-1` produces a `q`-vertex
low set. On it the adjacency occupancy is `S.card / q`; off it the occupancy
is one larger. -/
theorem binarySquare_predCut_exists_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G) S = q - 1)
    (hmod : S.card % q = q - 1) :
    ∃ Z : Finset V, Z.card = q ∧
      ∀ x, (x ∈ Z ∧
          (G.neighborFinset x ∩ S).card = S.card / q) ∨
        (x ∉ Z ∧
          (G.neighborFinset x ∩ S).card = S.card / q + 1) := by
  let f := fun x : V => (G.neighborFinset x ∩ S).card
  have hqpos : 0 < q := by omega
  have hsum : (∑ x, f x) = q * S.card := by
    rw [sum_card_neighbor_inter_eq_sum_degree]
    calc
      (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, q := by
        apply Finset.sum_congr rfl
        intro x _
        exact hreg x
      _ = q * S.card := by simp [mul_comm]
  have hm := c4Free_regular_square_cut_neighborMoment
    G hfree hreg hcard S
  have hsq : (∑ x, f x ^ 2) +
      (∑ i : Fin 0, (0 : ℕ) * (0 - 1)) =
        S.card ^ 2 + (q - 1) := by
    simpa [f, hcut] using hm
  have hsharp : nearRegularCutLower (q * q) q S.card
      (fun _ : Fin 0 => 0) = (q - 1 : ℕ) := by
    have hr := regularSquareCutLower_eq_mod_product q S.card hqpos
    rw [hmod] at hr
    have hone : q - (q - 1) = 1 := by omega
    rw [hone, mul_one] at hr
    simpa [nearRegularCutLower, regularSquareCutLower] using hr
  have hpart := nearRegular_partition_of_cutLower_eq
    (O := V) (ι := Fin 0) (q * q) q (by positivity) hcard
    f S.card (q - 1) (fun _ => 0)
    (by simpa using hsum) hsq hsharp
  have hdiv : (∑ x, f x) / (q * q) = S.card / q := by
    rw [hsum]
    exact Nat.mul_div_mul_left S.card q hqpos
  have hrem : (∑ x, f x) % (q * q) = q * (q - 1) := by
    rw [hsum, Nat.mul_mod_mul_left, hmod]
  let U : Finset V := Finset.univ.filter fun x => f x = S.card / q + 1
  let Z : Finset V := Finset.univ \ U
  have hUcard : U.card = q * (q - 1) := by
    have hu := hpart.2
    rw [hdiv, hrem] at hu
    exact hu
  have hUsub : U ⊆ (Finset.univ : Finset V) := Finset.subset_univ U
  have hZcard : Z.card = q := by
    dsimp only [Z]
    rw [Finset.card_sdiff_of_subset hUsub, Finset.card_univ, hcard, hUcard]
    have hdecomp : q * (q - 1) + q = q * q := by
      calc
        q * (q - 1) + q = q * ((q - 1) + 1) := by ring
        _ = q * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
    omega
  refine ⟨Z, hZcard, ?_⟩
  intro x
  have hxvals := hpart.1 x
  rw [hdiv] at hxvals
  by_cases hxZ : x ∈ Z
  · have hxNotU : x ∉ U := (Finset.mem_sdiff.mp hxZ).2
    have hxLower : f x = S.card / q := by
      rcases hxvals with hx | hx
      · exact hx
      · exfalso
        exact hxNotU (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
    exact Or.inl ⟨hxZ, hxLower⟩
  · have hxU : x ∈ U := by
      by_contra hxNotU
      exact hxZ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxNotU⟩)
    have hxUpper : f x = S.card / q + 1 := (Finset.mem_filter.mp hxU).2
    exact Or.inr ⟨hxZ, hxUpper⟩

#print axioms binarySquare_predCut_exists_lowSet

end

end Erdos85
