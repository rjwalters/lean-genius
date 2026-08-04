import Proofs.Erdos85GadgetExtension
import Proofs.Erdos85IntersectingPairs

/-!
# A five-selector packing obstruction

The order-32 polarity witness deletes four absolute points and attaches five
new vertices.  For larger fields, any sufficiently large safe selector is
forced into the surviving neighbourhood of one deleted absolute point.  The
lemma below isolates the final finite packing obstruction: five such large
star selectors cannot be assigned to only four centres while meeting pairwise
in at most one point.
-/

namespace Erdos85

/-- A rank-two intersecting multifamily with at least four indexed members is
a star, provided repeated two-element labels can only come from the same
index.  Singleton labels force the star directly; otherwise this is
`pair_intersecting_star_or_card_le_three` transported along the label map. -/
theorem intersecting_rank_two_multifamily_star_of_four
    {X C : Type*} [DecidableEq X] [Fintype C] [DecidableEq C]
    (S : Finset X) (label : X → Finset C)
    (hfour : 4 ≤ S.card)
    (hnonempty : ∀ x ∈ S, (label x).Nonempty)
    (hcard : ∀ x ∈ S, (label x).card ≤ 2)
    (hinter : ∀ x ∈ S, ∀ y ∈ S, ¬ Disjoint (label x) (label y))
    (hinj_two : ∀ x ∈ S, ∀ y ∈ S,
      (label x).card = 2 → label x = label y → x = y) :
    ∃ c : C, ∀ x ∈ S, c ∈ label x := by
  classical
  by_cases hone : ∃ x ∈ S, (label x).card = 1
  · obtain ⟨x, hx, hcardx⟩ := hone
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcardx
    refine ⟨c, ?_⟩
    intro y hy
    have hxy := hinter x hx y hy
    rw [Finset.not_disjoint_iff] at hxy
    obtain ⟨z, hzx, hzy⟩ := hxy
    rw [hc] at hzx
    simp only [Finset.mem_singleton] at hzx
    subst z
    exact hzy
  · push Not at hone
    have htwo : ∀ x ∈ S, (label x).card = 2 := by
      intro x hx
      have hp := Finset.card_pos.mpr (hnonempty x hx)
      have hl := hcard x hx
      have hn := hone x hx
      omega
    let emb : {x // x ∈ S} ↪ Finset C :=
      ⟨fun x => label x.1, fun x y h => by
        apply Subtype.ext
        exact hinj_two x.1 x.2 y.1 y.2 (htwo x.1 x.2) h⟩
    let A : Finset (Finset C) := Finset.univ.map emb
    have hAcard : A.card = S.card := by
      simp [A, Fintype.card_coe]
    have hAsized : (A : Set (Finset C)).Sized 2 := by
      intro T hT
      rw [Finset.mem_coe, Finset.mem_map] at hT
      obtain ⟨x, hx, rfl⟩ := hT
      exact htwo x.1 x.2
    have hAint : (A : Set (Finset C)).Intersecting := by
      intro T hT U hU hdisj
      rw [Finset.mem_coe, Finset.mem_map] at hT hU
      obtain ⟨x, hx, rfl⟩ := hT
      obtain ⟨y, hy, rfl⟩ := hU
      exact hinter x.1 x.2 y.1 y.2 hdisj
    rcases pair_intersecting_star_or_card_le_three A hAint hAsized with hstar | hsmall
    · obtain ⟨c, hc⟩ := hstar
      refine ⟨c, ?_⟩
      intro x hx
      let xs : {x // x ∈ S} := ⟨x, hx⟩
      apply hc (label x)
      exact Finset.mem_map.mpr ⟨xs, Finset.mem_univ _, rfl⟩
    · rw [hAcard] at hsmall
      omega

/-- Five subsets of size at least `q-2`, each lying in a `q`-element fibre
over one of at most four centres, cannot have pairwise intersections of size
at most one once `q ≥ 7`. -/
theorem five_large_star_selectors_impossible
    {X C : Type*} [DecidableEq X] [Fintype C]
    (q : ℕ) (hq : 7 ≤ q)
    (S : Fin 5 → Finset X) (center : Fin 5 → C)
    (fiber : C → Finset X)
    (hcenters : Fintype.card C ≤ 4)
    (hlarge : ∀ i, q - 2 ≤ (S i).card)
    (hsub : ∀ i, S i ⊆ fiber (center i))
    (hfiber : ∀ c, (fiber c).card ≤ q)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    False := by
  have hninj : ¬ Function.Injective center := by
    intro hinj
    have hcard := Fintype.card_le_of_injective center hinj
    have hfin : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
    rw [hfin] at hcard
    omega
  rw [Function.not_injective_iff] at hninj
  obtain ⟨i, j, hc, hij⟩ := hninj
  have hunion : S i ∪ S j ⊆ fiber (center i) := by
    apply Finset.union_subset
    · exact hsub i
    · rw [hc]
      exact hsub j
  have hucard : (S i ∪ S j).card ≤ q :=
    (Finset.card_le_card hunion).trans (hfiber (center i))
  have hcards := Finset.card_union_add_card_inter (S i) (S j)
  have hicard := hinter i j hij
  have hi := hlarge i
  have hj := hlarge j
  omega

end Erdos85
