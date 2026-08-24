import Proofs.Erdos85ThreeSeparatorEndpointParallelClass

/-!
# The exceptional-point matching

At the endpoint, every neighbor of the exceptional point `c` has exactly
two neighbors in `K`.  One is `c`; choosing the other gives a map into
`K \ {c}`.  C4-freeness makes this map injective.  This is the matching
core of (B17).
-/

open Finset SimpleGraph

namespace Erdos85

/-- B17 matching interface: the neighbors of `c` embed in `K \ {c}` through
length-two paths starting at `c`. -/
theorem exists_exceptionalPoint_otherKNeighbor_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (c : V) (K : Finset V)
    (hcK : c ∈ K)
    (htwo : ∀ y ∈ A.neighborFinset c,
      (A.neighborFinset y ∩ K).card = 2) :
    ∃ φ : {y // y ∈ A.neighborFinset c} ↪ V,
      ∀ y, φ y ∈ K \ {c} ∧ A.Adj y.1 (φ y) := by
  have hother (y : {y // y ∈ A.neighborFinset c}) :
      ∃ z ∈ A.neighborFinset y.1 ∩ K, z ≠ c := by
    let S := A.neighborFinset y.1 ∩ K
    have hcS : c ∈ S := by
      refine Finset.mem_inter.mpr ⟨?_, hcK⟩
      exact (A.mem_neighborFinset y.1 c).mpr
        ((A.mem_neighborFinset c y.1).mp y.2).symm
    have hcard : S.card = 2 := htwo y.1 y.2
    obtain ⟨z, hzS, hzc⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) c
    exact ⟨z, hzS, hzc⟩
  let φ : {y // y ∈ A.neighborFinset c} → V := fun y =>
    Classical.choose (hother y)
  have hφmem (y : {y // y ∈ A.neighborFinset c}) :
      φ y ∈ A.neighborFinset y.1 ∩ K :=
    Classical.choose_spec (hother y) |>.1
  have hφne (y : {y // y ∈ A.neighborFinset c}) : φ y ≠ c :=
    Classical.choose_spec (hother y) |>.2
  have hφinj : Function.Injective φ := by
    intro y₁ y₂ heq
    apply Subtype.ext
    have hcy₁ : A.Adj c y₁.1 := (A.mem_neighborFinset c y₁.1).mp y₁.2
    have hcy₂ : A.Adj c y₂.1 := (A.mem_neighborFinset c y₂.1).mp y₂.2
    have hφy₁ : A.Adj (φ y₁) y₁.1 :=
      ((A.mem_neighborFinset y₁.1 (φ y₁)).mp
        (Finset.mem_inter.mp (hφmem y₁)).1).symm
    have hφy₂ : A.Adj (φ y₁) y₂.1 := by
      rw [heq]
      exact ((A.mem_neighborFinset y₂.1 (φ y₂)).mp
        (Finset.mem_inter.mp (hφmem y₂)).1).symm
    exact commonNeighbor_unique_of_c4Free hfree (hφne y₁).symm
      hcy₁ hφy₁ hcy₂ hφy₂
  refine ⟨⟨φ, hφinj⟩, ?_⟩
  intro y
  have hmem := Finset.mem_inter.mp (hφmem y)
  refine ⟨Finset.mem_sdiff.mpr ⟨hmem.2, ?_⟩, ?_⟩
  · simpa using hφne y
  · exact (A.mem_neighborFinset y.1 (φ y)).mp hmem.1

#print axioms exists_exceptionalPoint_otherKNeighbor_embedding

end Erdos85
