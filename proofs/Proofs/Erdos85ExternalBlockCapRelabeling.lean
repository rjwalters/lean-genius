import Proofs.Erdos85EncodedExternalBlockCap

namespace Erdos85

/-- Relabeling vertices and blocks preserves the external neighborhood cap. -/
theorem encodedExternalBlockCap_relabel
    {W K : Type*} [Fintype W] [DecidableEq W] [Fintype K]
    (B : W → W → Bool) (blocks : K → Finset W) (e : Equiv.Perm W) :
    encodedExternalBlockCap (fun x y => B (e.symm x) (e.symm y))
      (fun k => (blocks k).image e) = encodedExternalBlockCap B blocks := by
  unfold encodedExternalBlockCap
  apply Bool.decide_congr
  have hc (x : W) (k : K) :
      (((blocks k).image e).filter (fun y => B (e.symm x) (e.symm y))).card =
        ((blocks k).filter (fun y => B (e.symm x) y)).card := by
    have he : ((blocks k).image e).filter (fun y => B (e.symm x) (e.symm y)) =
        ((blocks k).filter (fun y => B (e.symm x) y)).image e := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨z,hz,rfl⟩,hB⟩
        exact ⟨z,⟨hz,by simpa using hB⟩,rfl⟩
      · rintro ⟨z,⟨hz,hB⟩,rfl⟩
        exact ⟨⟨z,hz,rfl⟩,by simpa using hB⟩
    rw [he,Finset.card_image_of_injective _ e.injective]
  simp only [hc]
  constructor
  · intro h x k
    simpa using h (e x) k
  · intro h x k
    exact h (e.symm x) k

/-- A bijection of block labels leaves the universal cap unchanged. -/
theorem encodedExternalBlockCap_reindex
    {W K : Type*} [Fintype W] [DecidableEq W] [Fintype K]
    (B : W → W → Bool) (blocks : K → Finset W) (σ : Equiv.Perm K) :
    encodedExternalBlockCap B (fun k => blocks (σ k)) = encodedExternalBlockCap B blocks := by
  unfold encodedExternalBlockCap
  apply Bool.decide_congr
  constructor
  · intro h x k
    simpa using h x (σ.symm k)
  · intro h x k
    exact h x (σ k)

end Erdos85
#print axioms Erdos85.encodedExternalBlockCap_relabel
#print axioms Erdos85.encodedExternalBlockCap_reindex
