import Proofs.Erdos85GadgetExtension

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
