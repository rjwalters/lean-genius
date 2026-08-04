import Proofs.Erdos85CompensatedGadget

/-!
# Selector multiplicity and compensation concentration

Compatibility allows two distinct gadget selectors to share at most one old
vertex.  Double-counting pairs of selectors through each old vertex therefore
bounds how concentrated attachment compensation can be.
-/

open SimpleGraph

namespace Erdos85

/-- Gadget vertices whose selectors contain a given old vertex. -/
def attachmentIndices
    {V W : Type*} [Fintype W] [DecidableEq W]
    (A : W → Finset V) [DecidableEq V] (x : V) : Finset W :=
  Finset.univ.filter fun w => x ∈ A w

/-- Number of gadget attachment edges received by an old vertex. -/
def attachmentMultiplicity
    {V W : Type*} [Fintype W] [DecidableEq W]
    (A : W → Finset V) [DecidableEq V] (x : V) : ℕ :=
  (attachmentIndices A x).card

@[simp] theorem mem_attachmentIndices
    {V W : Type*} [Fintype W] [DecidableEq W]
    (A : W → Finset V) [DecidableEq V] (x : V) (w : W) :
    w ∈ attachmentIndices A x ↔ x ∈ A w := by
  simp [attachmentIndices]

/-- Incidences `(x,P)` where the old vertex `x` belongs to both selectors in
the two-element gadget-vertex set `P`. -/
def attachmentPairIncidences
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (A : W → Finset V) : Finset (Σ _x : V, Finset W) :=
  Finset.univ.sigma fun x => (attachmentIndices A x).powersetCard 2

/-- The incidence count is the sum of `choose(t_x,2)`. -/
theorem card_attachmentPairIncidences
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (A : W → Finset V) :
    (attachmentPairIncidences A).card =
      ∑ x : V, (attachmentMultiplicity A x).choose 2 := by
  rw [attachmentPairIncidences, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro x _
  simp [attachmentMultiplicity]

/-- **Selector-pair multiplicity bound.**  In a compatible gadget attachment,
`Σ_x choose(t_x,2) ≤ choose(|W|,2)`.  Thus repeated use of old vertices
cannot be concentrated arbitrarily. -/
theorem GadgetAttachmentCompatible.sum_choose_two_attachmentMultiplicity_le
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A) :
    (∑ x : V, (attachmentMultiplicity A x).choose 2) ≤
      (Fintype.card W).choose 2 := by
  classical
  let P := attachmentPairIncidences A
  let Q := (Finset.univ : Finset W).powersetCard 2
  have hPQ : P.card ≤ Q.card := by
    apply Finset.card_le_card_of_injOn (fun p : (Σ _x : V, Finset W) => p.2)
    · intro p hp
      change p ∈ P at hp
      change p.2 ∈ Q
      dsimp [P, Q] at hp ⊢
      rw [attachmentPairIncidences, Finset.mem_sigma] at hp
      rw [Finset.mem_powersetCard] at hp ⊢
      exact ⟨hp.2.1.trans (by simp), hp.2.2⟩
    · intro p hp q hq hpq
      rcases p with ⟨x, S⟩
      rcases q with ⟨y, T⟩
      change S = T at hpq
      subst T
      change (⟨x, S⟩ : Σ _x : V, Finset W) ∈ P at hp
      change (⟨y, S⟩ : Σ _x : V, Finset W) ∈ P at hq
      dsimp [P] at hp hq
      rw [attachmentPairIncidences, Finset.mem_sigma] at hp hq
      have hScard : S.card = 2 := (Finset.mem_powersetCard.mp hp.2).2
      have hSlarge : 1 < S.card := by omega
      obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hSlarge
      have hSx := (Finset.mem_powersetCard.mp hp.2).1
      have hSy := (Finset.mem_powersetCard.mp hq.2).1
      have hxu : x ∈ A u := (mem_attachmentIndices A x u).mp (hSx hu)
      have hxw : x ∈ A w := (mem_attachmentIndices A x w).mp (hSx hw)
      have hyu : y ∈ A u := (mem_attachmentIndices A y u).mp (hSy hu)
      have hyw : y ∈ A w := (mem_attachmentIndices A y w).mp (hSy hw)
      have hxy : x = y := by
        by_contra hne
        have hinter : 1 < (A u ∩ A w).card := by
          apply Finset.one_lt_card.mpr
          exact ⟨x, Finset.mem_inter.mpr ⟨hxu, hxw⟩,
            y, Finset.mem_inter.mpr ⟨hyu, hyw⟩, hne⟩
        have hle := hcompat.card_selector_inter_le_one G F A huw
        omega
      subst y
      rfl
  rw [card_attachmentPairIncidences] at hPQ
  simpa [Q] using hPQ

/-- Exact attachment multiplicity is the degree credit appearing in the
gadget surgery. -/
theorem card_filter_attachment_eq_attachmentMultiplicity
    {V W : Type*} [Fintype W] [DecidableEq W]
    (A : W → Finset V) [DecidableEq V] (x : V) :
    (Finset.univ.filter fun w => x ∈ A w).card =
      attachmentMultiplicity A x := rfl

/-- At a baseline-tight old vertex, every deleted incident edge must be
repaid by a distinct gadget attachment. -/
theorem subgraphDegreeLoss_le_attachmentMultiplicity_of_tight
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H) (A : W → Finset V) {d : ℕ} (x : V)
    (htight : H.degree x = d)
    (hfinal : d ≤ K.degree x + attachmentMultiplicity A x) :
    subgraphDegreeLoss H K x ≤ attachmentMultiplicity A x := by
  have hsplit := degree_add_subgraphDegreeLoss H K hKH x
  omega

/-- More generally, only degree loss beyond the old surplus above `d` must
be repaid by gadget attachments. -/
theorem subgraphDegreeLoss_sub_surplus_le_attachmentMultiplicity
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H) (A : W → Finset V) {d : ℕ} (x : V)
    (hfinal : d ≤ K.degree x + attachmentMultiplicity A x) :
    subgraphDegreeLoss H K x - (H.degree x - d) ≤
      attachmentMultiplicity A x := by
  have hsplit := degree_add_subgraphDegreeLoss H K hKH x
  omega

/-- Quantitative cascade bound.  If a baseline-tight vertex loses at least
`q` incident old edges, it must lie in at least `q` selectors.  Pairwise
selector intersection then permits at most `choose(m,2)/choose(q,2)` such
vertices (stated without division). -/
theorem card_tight_loss_ge_mul_choose_le_choose_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d q : ℕ}
    (hfinal : ∀ x : V, d ≤ K.degree x + attachmentMultiplicity A x)
    (hcompat : GadgetAttachmentCompatible K F A) :
    ((Finset.univ.filter fun x : V =>
        H.degree x = d ∧ q ≤ subgraphDegreeLoss H K x).card) *
        q.choose 2 ≤ (Fintype.card W).choose 2 := by
  classical
  let S := Finset.univ.filter fun x : V =>
    H.degree x = d ∧ q ≤ subgraphDegreeLoss H K x
  have hpair := hcompat.sum_choose_two_attachmentMultiplicity_le K F A
  calc
    S.card * q.choose 2 = ∑ _x ∈ S, q.choose 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, (attachmentMultiplicity A x).choose 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hxdata : H.degree x = d ∧
          q ≤ subgraphDegreeLoss H K x := by
        simpa [S] using hx
      have hloss := subgraphDegreeLoss_le_attachmentMultiplicity_of_tight
        H K hKH A x hxdata.1 (hfinal x)
      exact Nat.choose_le_choose 2 (hxdata.2.trans hloss)
    _ ≤ ∑ x : V, (attachmentMultiplicity A x).choose 2 := by
      exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ ≤ (Fintype.card W).choose 2 := hpair

/-- In particular, at most `choose(m,2)` tight vertices can each lose two or
more incident old edges in a compatible compensated gadget repair. -/
theorem card_tight_loss_ge_two_le_choose_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hfinal : ∀ x : V, d ≤ K.degree x + attachmentMultiplicity A x)
    (hcompat : GadgetAttachmentCompatible K F A) :
    (Finset.univ.filter fun x : V =>
        H.degree x = d ∧ 2 ≤ subgraphDegreeLoss H K x).card ≤
      (Fintype.card W).choose 2 := by
  have h := card_tight_loss_ge_mul_choose_le_choose_card
    H K hKH F A (q := 2) hfinal hcompat
  simpa using h

end Erdos85
