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

open SimpleGraph

/-- A rank-two intersecting multifamily with at least four indexed members is
a star, provided repeated two-element labels can only come from the same
index.  Singleton labels force the star directly; otherwise this is
`pair_intersecting_star_or_card_le_three` transported along the label map. -/
theorem intersecting_rank_two_multifamily_star_of_four
    {X C : Type*} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
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

/-- Combined rank-two form.  If every one of five large selectors has an
intersecting rank-two label family, repeated two-labels identify the same
point, each centre fibre has at most `q` points, and distinct selectors meet
in at most one point, then `q ≥ 7` is impossible. -/
theorem five_large_rank_two_selectors_impossible
    {X C : Type*} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (q : ℕ) (hq : 7 ≤ q)
    (S : Fin 5 → Finset X) (label : X → Finset C)
    (hcenters : Fintype.card C ≤ 4)
    (hlarge : ∀ i, q - 2 ≤ (S i).card)
    (hnonempty : ∀ i x, x ∈ S i → (label x).Nonempty)
    (hcard : ∀ i x, x ∈ S i → (label x).card ≤ 2)
    (hlabel_inter : ∀ i x, x ∈ S i → ∀ y, y ∈ S i →
      ¬ Disjoint (label x) (label y))
    (hinj_two : ∀ i x, x ∈ S i → ∀ y, y ∈ S i →
      (label x).card = 2 → label x = label y → x = y)
    (hfiber : ∀ c, (Finset.univ.filter fun x => c ∈ label x).card ≤ q)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    False := by
  classical
  have hfour : ∀ i, 4 ≤ (S i).card := by
    intro i
    have hi := hlarge i
    omega
  choose center hcenter using fun i =>
    intersecting_rank_two_multifamily_star_of_four
      (S i) label (hfour i)
      (hnonempty i) (hcard i) (hlabel_inter i) (hinj_two i)
  apply five_large_star_selectors_impossible
    q hq S center (fun c => Finset.univ.filter fun x => c ∈ label x)
    hcenters hlarge
  · intro i x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcenter i x hx
  · exact hfiber
  · exact hinter

/-- Gadget-facing form: a compatible five-cycle attachment whose new
vertices all reach degree `q ≥ 7` is impossible whenever the old selector
labels satisfy the rank-two four-centre hypotheses. -/
theorem fiveCycleAttachment_impossible_of_rank_two_labels
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : 7 ≤ q)
    (A : Fin 5 → Finset V) (label : V → Finset C)
    (hcompat : GadgetAttachmentCompatible G (cycleGraph 5) A)
    (hnewDegree : ∀ w : Fin 5,
      q ≤ (attachGadget G (cycleGraph 5) A).degree (.inr w))
    (hcenters : Fintype.card C ≤ 4)
    (hnonempty : ∀ i x, x ∈ A i → (label x).Nonempty)
    (hcard : ∀ i x, x ∈ A i → (label x).card ≤ 2)
    (hlabel_inter : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      ¬ Disjoint (label x) (label y))
    (hinj_two : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      (label x).card = 2 → label x = label y → x = y)
    (hfiber : ∀ c, (Finset.univ.filter fun x => c ∈ label x).card ≤ q) :
    False := by
  have hlarge : ∀ i, q - 2 ≤ (A i).card := by
    intro i
    have hi := hnewDegree i
    rw [attachGadget_degree_new, cycleGraph_degree_three_le] at hi
    omega
  exact five_large_rank_two_selectors_impossible
    q hq A label hcenters hlarge hnonempty hcard hlabel_inter hinj_two
    hfiber (fun i j hij =>
      hcompat.card_selector_inter_le_one G (cycleGraph 5) A hij)

/-- General pigeonhole form of the selector obstruction.  More large
rank-two selectors than available centres are impossible once `q ≥ 6`. -/
theorem too_many_large_rank_two_selectors_impossible
    {I X C : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (q : ℕ) (hq : 6 ≤ q)
    (S : I → Finset X) (label : X → Finset C)
    (hcenters : Fintype.card C < Fintype.card I)
    (hlarge : ∀ i, q - 2 ≤ (S i).card)
    (hnonempty : ∀ i x, x ∈ S i → (label x).Nonempty)
    (hcard : ∀ i x, x ∈ S i → (label x).card ≤ 2)
    (hlabel_inter : ∀ i x, x ∈ S i → ∀ y, y ∈ S i →
      ¬ Disjoint (label x) (label y))
    (hinj_two : ∀ i x, x ∈ S i → ∀ y, y ∈ S i →
      (label x).card = 2 → label x = label y → x = y)
    (hfiber : ∀ c, (Finset.univ.filter fun x => c ∈ label x).card ≤ q)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    False := by
  classical
  have hfour : ∀ i, 4 ≤ (S i).card := by
    intro i
    have hi := hlarge i
    omega
  choose center hcenter using fun i =>
    intersecting_rank_two_multifamily_star_of_four
      (S i) label (hfour i)
      (hnonempty i) (hcard i) (hlabel_inter i) (hinj_two i)
  have hninj : ¬ Function.Injective center := by
    intro hinj
    exact (not_le_of_gt hcenters) (Fintype.card_le_of_injective center hinj)
  rw [Function.not_injective_iff] at hninj
  obtain ⟨i, j, hc, hij⟩ := hninj
  have hsubi : S i ⊆ Finset.univ.filter fun x => center i ∈ label x := by
    intro x hx
    simp [hcenter i x hx]
  have hsubj : S j ⊆ Finset.univ.filter fun x => center i ∈ label x := by
    intro x hx
    simp [hc, hcenter j x hx]
  have hunion : S i ∪ S j ⊆
      Finset.univ.filter fun x => center i ∈ label x :=
    Finset.union_subset hsubi hsubj
  have hucard : (S i ∪ S j).card ≤ q :=
    (Finset.card_le_card hunion).trans (hfiber (center i))
  have hcards := Finset.card_union_add_card_inter (S i) (S j)
  have hicard := hinter i j hij
  have hi := hlarge i
  have hj := hlarge j
  omega

/-- Gadget-facing general form for a two-regular new gadget: if there are
more new vertices than rank-two label centres, degree `q ≥ 6` is impossible. -/
theorem degreeTwoGadgetAttachment_impossible_of_rank_two_labels
    {V W C : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (q : ℕ) (hq : 6 ≤ q)
    (A : W → Finset V) (label : V → Finset C)
    (hcompat : GadgetAttachmentCompatible G F A)
    (hFdegree : ∀ w, F.degree w = 2)
    (hnewDegree : ∀ w, q ≤ (attachGadget G F A).degree (.inr w))
    (hcenters : Fintype.card C < Fintype.card W)
    (hnonempty : ∀ i x, x ∈ A i → (label x).Nonempty)
    (hcard : ∀ i x, x ∈ A i → (label x).card ≤ 2)
    (hlabel_inter : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      ¬ Disjoint (label x) (label y))
    (hinj_two : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      (label x).card = 2 → label x = label y → x = y)
    (hfiber : ∀ c, (Finset.univ.filter fun x => c ∈ label x).card ≤ q) :
    False := by
  have hlarge : ∀ i, q - 2 ≤ (A i).card := by
    intro i
    have hi := hnewDegree i
    rw [attachGadget_degree_new, hFdegree] at hi
    omega
  exact too_many_large_rank_two_selectors_impossible
    q hq A label hcenters hlarge hnonempty hcard hlabel_inter hinj_two
    hfiber (fun i j hij => hcompat.card_selector_inter_le_one G F A hij)

/-- Parameterized packing obstruction.  If there are more selectors than
centres, every selector has size at least `q-r`, and `q ≥ 2r+2`, then two
selectors routed to the same `q`-point centre fibre must overlap in at least
two points, contradicting the compatibility budget. -/
theorem too_many_large_rank_two_selectors_impossible_of_sub_degree
    {I X C : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (q r : ℕ) (hr : 2 ≤ r) (hqr : 2 * r + 2 ≤ q)
    (S : I → Finset X) (label : X → Finset C)
    (hcenters : Fintype.card C < Fintype.card I)
    (hlarge : ∀ i, q - r ≤ (S i).card)
    (hnonempty : ∀ i x, x ∈ S i → (label x).Nonempty)
    (hcard : ∀ i x, x ∈ S i → (label x).card ≤ 2)
    (hlabel_inter : ∀ i x, x ∈ S i → ∀ y, y ∈ S i →
      ¬ Disjoint (label x) (label y))
    (hinj_two : ∀ i x, x ∈ S i → ∀ y, y ∈ S i →
      (label x).card = 2 → label x = label y → x = y)
    (hfiber : ∀ c, (Finset.univ.filter fun x => c ∈ label x).card ≤ q)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    False := by
  classical
  have hfour : ∀ i, 4 ≤ (S i).card := by
    intro i
    have hi := hlarge i
    omega
  choose center hcenter using fun i =>
    intersecting_rank_two_multifamily_star_of_four
      (S i) label (hfour i)
      (hnonempty i) (hcard i) (hlabel_inter i) (hinj_two i)
  have hninj : ¬ Function.Injective center := by
    intro hinj
    exact (not_le_of_gt hcenters) (Fintype.card_le_of_injective center hinj)
  rw [Function.not_injective_iff] at hninj
  obtain ⟨i, j, hc, hij⟩ := hninj
  have hsubi : S i ⊆ Finset.univ.filter fun x => center i ∈ label x := by
    intro x hx
    simp [hcenter i x hx]
  have hsubj : S j ⊆ Finset.univ.filter fun x => center i ∈ label x := by
    intro x hx
    simp [hc, hcenter j x hx]
  have hunion : S i ∪ S j ⊆
      Finset.univ.filter fun x => center i ∈ label x :=
    Finset.union_subset hsubi hsubj
  have hucard : (S i ∪ S j).card ≤ q :=
    (Finset.card_le_card hunion).trans (hfiber (center i))
  have hcards := Finset.card_union_add_card_inter (S i) (S j)
  have hicard := hinter i j hij
  have hi := hlarge i
  have hj := hlarge j
  omega

/-- Gadget-facing bounded-degree form.  A net-positive gadget whose new
vertices have old-gadget degree at most `r` cannot reach degree `q` when
`q ≥ 2r+2`, under the rank-two label hypotheses. -/
theorem boundedDegreeGadgetAttachment_impossible_of_rank_two_labels
    {V W C : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (q r : ℕ) (hr : 2 ≤ r) (hqr : 2 * r + 2 ≤ q)
    (A : W → Finset V) (label : V → Finset C)
    (hcompat : GadgetAttachmentCompatible G F A)
    (hFdegree : ∀ w, F.degree w ≤ r)
    (hnewDegree : ∀ w, q ≤ (attachGadget G F A).degree (.inr w))
    (hcenters : Fintype.card C < Fintype.card W)
    (hnonempty : ∀ i x, x ∈ A i → (label x).Nonempty)
    (hcard : ∀ i x, x ∈ A i → (label x).card ≤ 2)
    (hlabel_inter : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      ¬ Disjoint (label x) (label y))
    (hinj_two : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      (label x).card = 2 → label x = label y → x = y)
    (hfiber : ∀ c, (Finset.univ.filter fun x => c ∈ label x).card ≤ q) :
    False := by
  have hlarge : ∀ i, q - r ≤ (A i).card := by
    intro i
    have hi := hnewDegree i
    rw [attachGadget_degree_new] at hi
    have hir := hFdegree i
    omega
  exact too_many_large_rank_two_selectors_impossible_of_sub_degree
    q r hr hqr A label hcenters hlarge hnonempty hcard hlabel_inter
    hinj_two hfiber
    (fun i j hij => hcompat.card_selector_inter_le_one G F A hij)

/-- Abstract pair-pole omission count.  If every unordered pair of selector
centres can be injected into a point omitted by one of its endpoint
selectors, then the number of centre pairs is at most the total selector
deficit.  The geometric work in applications is exactly the construction of
`route`. -/
theorem choose_two_le_sum_deficit_of_injective_omission_route
    {I X C : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (q : ℕ) (S : I → Finset X) (center : I → C)
    (fiber : C → Finset X) (deficit : I → ℕ)
    (hsub : ∀ i, S i ⊆ fiber (center i))
    (hfiber : ∀ c, (fiber c).card ≤ q)
    (hlarge : ∀ i, q - deficit i ≤ (S i).card)
    (route :
      {T : Finset I // T ∈ (Finset.univ : Finset I).powersetCard 2} →
        Σ i : I, {x : X // x ∈ fiber (center i) \ S i})
    (hroute : Function.Injective route) :
    (Fintype.card I).choose 2 ≤ ∑ i : I, deficit i := by
  classical
  have hcard_route := Fintype.card_le_of_injective route hroute
  have hpairs : Fintype.card
      {T : Finset I // T ∈ (Finset.univ : Finset I).powersetCard 2} =
      (Fintype.card I).choose 2 := by
    rw [Fintype.card_coe]
    simp
  have htarget : Fintype.card
      (Σ i : I, {x : X // x ∈ fiber (center i) \ S i}) =
      ∑ i : I, (fiber (center i) \ S i).card := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.card_coe _
  rw [hpairs, htarget] at hcard_route
  apply hcard_route.trans
  apply Finset.sum_le_sum
  intro i _
  have hdiff : (fiber (center i) \ S i).card + (S i).card =
      (fiber (center i)).card := by
    have hpart := Finset.card_sdiff_add_card_inter
      (fiber (center i)) (S i)
    rw [Finset.inter_eq_right.mpr (hsub i)] at hpart
    exact hpart
  have hf := hfiber (center i)
  have hl := hlarge i
  omega

end Erdos85
