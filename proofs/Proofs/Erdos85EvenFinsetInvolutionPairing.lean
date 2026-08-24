import Proofs.Erdos85WitnessPairingRelayGraph

/-!
# Fixed-point-free pairing of an even finite fiber

The Baer relay construction needs to pair every even eligible witness fiber.
This file packages the elementary existence statement in the precise form
consumed by `witnessPairingRelayGraph`: the pairing is a total function, but
closure, involutivity, and absence of fixed points are asserted only on the
chosen fiber.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every even finite set admits a fixed-point-free involution on that set,
extended by the identity away from it. -/
theorem exists_mate_of_even_finset
    {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V)
    (heven : Even s.card) :
    ∃ mate : V → V,
      (∀ v, v ∈ s → mate v ∈ s) ∧
      (∀ v, v ∈ s → mate (mate v) = v) ∧
      (∀ v, v ∈ s → mate v ≠ v) ∧
      (∀ v, v ∉ s → mate v = v) := by
  let G : SimpleGraph V := ⊤
  have hclique : G.IsClique (s : Set V) := by
    intro v hv w hw hvw
    simpa [G] using hvw
  have hfinite : (s : Set V).Finite := s.finite_toSet
  have hsetEven : Even (s : Set V).ncard := by
    simpa using heven
  obtain ⟨M, hverts, hmatching⟩ :=
    (hclique.even_iff_exists_isMatching hfinite).mp hsetEven
  have hmatched : ∀ v, v ∈ s → ∃! w, M.Adj v w := by
    intro v hv
    apply hmatching
    rw [hverts]
    exact hv
  let partner : ∀ v : V, v ∈ s → V := fun v hv =>
    Classical.choose (hmatched v hv)
  let mate : V → V := fun v => if hv : v ∈ s then partner v hv else v
  refine ⟨mate, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hadj : M.Adj v (partner v hv) :=
      (Classical.choose_spec (hmatched v hv)).1
    have hmem : partner v hv ∈ M.verts := M.edge_vert hadj.symm
    rw [hverts] at hmem
    simpa [mate, hv] using hmem
  · intro v hv
    have hadj : M.Adj v (partner v hv) :=
      (Classical.choose_spec (hmatched v hv)).1
    have hpartnerMem : partner v hv ∈ s := by
      have : partner v hv ∈ M.verts := M.edge_vert hadj.symm
      rwa [hverts] at this
    have hbackAdj : M.Adj (partner v hv) v := hadj.symm
    have hback : partner (partner v hv) hpartnerMem = v :=
      ((Classical.choose_spec (hmatched (partner v hv) hpartnerMem)).2 v hbackAdj).symm
    simpa [mate, hv, hpartnerMem] using hback
  · intro v hv hfix
    have hadj : M.Adj v (partner v hv) :=
      (Classical.choose_spec (hmatched v hv)).1
    exact hadj.ne (by simpa [mate, hv] using hfix.symm)
  · intro v hv
    simp [mate, hv]

/-- Fiberwise form: if every eligible witness fiber has even cardinality,
there is one admissible local mate function for every witness simultaneously. -/
theorem exists_witnessMate_of_even_fibers
    {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (eligible : W → V → Prop) [DecidableRel eligible]
    (heven : ∀ w,
      Even ((Finset.univ.filter fun v => eligible w v).card)) :
    ∃ mate : W → V → V,
      (∀ w v, eligible w v → eligible w (mate w v)) ∧
      (∀ w v, eligible w v → mate w (mate w v) = v) ∧
      (∀ w v, eligible w v → mate w v ≠ v) ∧
      (∀ w v, ¬ eligible w v → mate w v = v) := by
  have hexists : ∀ w, ∃ mate : V → V,
      (∀ v, eligible w v → eligible w (mate v)) ∧
      (∀ v, eligible w v → mate (mate v) = v) ∧
      (∀ v, eligible w v → mate v ≠ v) ∧
      (∀ v, ¬ eligible w v → mate v = v) := by
    intro w
    obtain ⟨mate, hclosed, hinvol, hfixed, houtside⟩ :=
      exists_mate_of_even_finset
        (Finset.univ.filter fun v => eligible w v) (heven w)
    refine ⟨mate, ?_, ?_, ?_, ?_⟩
    · intro v hv
      exact (Finset.mem_filter.mp
        (hclosed v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩))).2
    · intro v hv
      exact hinvol v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)
    · intro v hv
      exact hfixed v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)
    · intro v hv
      apply houtside v
      simp [hv]
  choose mate hclosed hinvol hfixed houtside using hexists
  exact ⟨mate, hclosed, hinvol, hfixed, houtside⟩

end

end Erdos85

#print axioms Erdos85.exists_mate_of_even_finset
#print axioms Erdos85.exists_witnessMate_of_even_fibers
