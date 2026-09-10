import Proofs.Erdos85IndependentTriangleCover
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A triangle cover with at most two covered vertices per triangle yields a matching. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extract disjoint two-cliques from a triangle cover. The extracted edges
are a matching supported on S, and their number measures the saving over
covering every vertex separately. -/
theorem triangle_cover_extract_disjoint_pairs
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (K : Finset (Finset V))
    (hK : K ⊆ G.cliqueFinset 3)
    (hcover : ∀ v ∈ S, ∃ t ∈ K, v ∈ t)
    (hcap : ∀ t ∈ K, (S ∩ t).card ≤ 2) :
    ∃ P : Finset (Finset V),
      (∀ e ∈ P, G.IsNClique 2 e ∧ e ⊆ S) ∧
      (∀ e ∈ P, ∀ d ∈ P, e ≠ d → Disjoint e d) ∧
      S.card ≤ K.card + P.card := by
  classical
  let f : V → Finset V := fun v =>
    if hv : v ∈ S then Classical.choose (hcover v hv) else ∅
  have hf : ∀ v ∈ S, f v ∈ K ∧ v ∈ f v := by
    intro v hv
    simp only [f, dif_pos hv]
    exact Classical.choose_spec (hcover v hv)
  let fiber := fun t => S.filter (fun v => f v = t)
  have hsub : ∀ t, fiber t ⊆ S ∩ t := by
    intro t v hv
    have hvS := (Finset.mem_filter.mp hv).1
    have heq := (Finset.mem_filter.mp hv).2
    exact Finset.mem_inter.mpr ⟨hvS, heq ▸ (hf v hvS).2⟩
  have hsmall : ∀ t ∈ K, (fiber t).card ≤ 2 := by
    intro t ht
    exact (Finset.card_le_card (hsub t)).trans (hcap t ht)
  let R := K.filter (fun t => (fiber t).card = 2)
  let P := R.image fiber
  have hfiberDisjoint : ∀ t u, t ≠ u → Disjoint (fiber t) (fiber u) := by
    intro t u hne
    apply Finset.disjoint_left.mpr
    intro v hvt hvu
    exact hne ((Finset.mem_filter.mp hvt).2.symm.trans (Finset.mem_filter.mp hvu).2)
  have hinj : Set.InjOn fiber ↑R := by
    intro t ht u hu heq
    by_contra hne
    have hdis := hfiberDisjoint t u hne
    rw [heq] at hdis
    have hempty : fiber u = ∅ := (Finset.disjoint_self_iff_empty _).mp hdis
    have htwo := (Finset.mem_filter.mp hu).2
    rw [hempty] at htwo
    simp at htwo
  have hPcard : P.card = R.card := Finset.card_image_of_injOn hinj
  refine ⟨P, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    have htK := (Finset.mem_filter.mp ht).1
    have htwo := (Finset.mem_filter.mp ht).2
    have hclique := (G.mem_cliqueFinset_iff.mp (hK htK)).isClique
    refine ⟨⟨?_, htwo⟩, ?_⟩
    · intro u hu v hv hne
      exact hclique (Finset.mem_inter.mp (hsub t hu)).2
        (Finset.mem_inter.mp (hsub t hv)).2 hne
    · intro v hv
      exact (Finset.mem_inter.mp (hsub t hv)).1
  · intro e he d hd hne
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
    exact hfiberDisjoint t u (fun h => hne (congrArg fiber h))
  · have hcount : S.card = ∑ t ∈ K, (fiber t).card :=
      Finset.card_eq_sum_card_fiberwise (fun v hv => (hf v hv).1)
    have hbound : ∀ t ∈ K, (fiber t).card ≤
        1 + (if (fiber t).card = 2 then 1 else 0) := by
      intro t ht
      have := hsmall t ht
      split_ifs <;> omega
    calc
      S.card = ∑ t ∈ K, (fiber t).card := hcount
      _ ≤ ∑ t ∈ K, (1 + if (fiber t).card = 2 then 1 else 0) :=
        Finset.sum_le_sum hbound
      _ = K.card + R.card := by
        have hR : (∑ t ∈ K, if (fiber t).card = 2 then 1 else 0) = R.card := by
          rw [← Finset.sum_filter]
          simp [R]
        rw [Finset.sum_add_distrib, hR]
        simp
      _ = K.card + P.card := by rw [hPcard]

/-- Any upper bound on the size of disjoint edge families in S gives the
matching-based triangle-cover inequality. -/
theorem triangle_cover_bound_of_disjoint_pair_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (K : Finset (Finset V)) (ν : ℕ)
    (hK : K ⊆ G.cliqueFinset 3)
    (hcover : ∀ v ∈ S, ∃ t ∈ K, v ∈ t)
    (hcap : ∀ t ∈ K, (S ∩ t).card ≤ 2)
    (hmatching : ∀ P : Finset (Finset V),
      (∀ e ∈ P, G.IsNClique 2 e ∧ e ⊆ S) →
      (∀ e ∈ P, ∀ d ∈ P, e ≠ d → Disjoint e d) → P.card ≤ ν) :
    S.card ≤ K.card + ν := by
  obtain ⟨P, hP, hdis, hcount⟩ := triangle_cover_extract_disjoint_pairs G S K hK hcover hcap
  exact hcount.trans (Nat.add_le_add_left (hmatching P hP hdis) _)
end Erdos85
#print axioms Erdos85.triangle_cover_extract_disjoint_pairs
#print axioms Erdos85.triangle_cover_bound_of_disjoint_pair_bound
