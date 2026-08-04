import Proofs.Erdos85DeleteOnePairObstruction
import Proofs.Erdos85DistanceLayers

/-!
# Bounded delete-set/replacement-gadget obstruction

With no additional survivor-edge deletion, a fixed-size delete-`k`/add-`k+1`
repair cannot work at Moore-layer order once the target degree is large and
the deleted vertices are tight.  Global regularity is unnecessary.
-/

open SimpleGraph

namespace Erdos85

/-- Cut-incidence counting: total neighbors lost by survivors is at most the
sum of degrees in the deleted set. -/
theorem sum_card_neighbor_inter_deleted_le_sum_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    (∑ v : {v : V // v ∉ D}, (G.neighborFinset v.1 ∩ D).card) ≤
      ∑ x ∈ D, G.degree x := by
  classical
  let L : Finset (Σ _v : {v : V // v ∉ D}, V) :=
    Finset.univ.sigma fun v => G.neighborFinset v.1 ∩ D
  let R : Finset (Σ _x : V, V) :=
    D.sigma fun x => G.neighborFinset x
  have hLR : L.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn
      (fun p : (Σ _v : {v : V // v ∉ D}, V) =>
        (⟨p.2, p.1.1⟩ : Σ _x : V, V))
    · intro p hp
      change p ∈ L at hp
      change (⟨p.2, p.1.1⟩ : Σ _x : V, V) ∈ R
      dsimp [L, R] at hp ⊢
      rw [Finset.mem_sigma] at hp ⊢
      have hp2 := Finset.mem_inter.mp hp.2
      exact ⟨hp2.2, (G.mem_neighborFinset p.2 p.1.1).mpr
        ((G.mem_neighborFinset p.1.1 p.2).mp hp2.1).symm⟩
    · intro p hp q hq hpq
      rcases p with ⟨v, x⟩
      rcases q with ⟨w, y⟩
      have hxy : x = y := congrArg Sigma.fst hpq
      subst y
      have hvw : v.1 = w.1 := congrArg Sigma.snd hpq
      have hvw' : v = w := Subtype.ext hvw
      subst w
      rfl
  have hLcard : L.card =
      ∑ v : {v : V // v ∉ D}, (G.neighborFinset v.1 ∩ D).card := by
    simp [L, Finset.card_sigma]
  have hRcard : R.card = ∑ x ∈ D, G.degree x := by
    dsimp [R]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro x _
    exact G.card_neighborFinset_eq_degree x
  rwa [hLcard, hRcard] at hLR

/-- In a `d`-regular graph, total survivor loss from deleting `k` vertices is
at most `kd`. -/
theorem sum_deletedNeighborLoss_le_card_mul_degree_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) {d k : ℕ}
    (hDcard : D.card = k) (hreg : ∀ x : V, G.degree x = d) :
    (∑ v : {v : V // v ∉ D}, (G.neighborFinset v.1 ∩ D).card) ≤
      k * d := by
  have hcut := sum_card_neighbor_inter_deleted_le_sum_degrees G D
  simpa [hDcard, hreg] using hcut

/-- Global regularity is unnecessary for the cut bound: it is enough that
every vertex actually placed in the deleted set has degree `d`. -/
theorem sum_deletedNeighborLoss_le_card_mul_degree_of_tight_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) {d k : ℕ}
    (hDcard : D.card = k) (hDtight : ∀ x ∈ D, G.degree x = d) :
    (∑ v : {v : V // v ∉ D}, (G.neighborFinset v.1 ∩ D).card) ≤
      k * d := by
  have hcut := sum_card_neighbor_inter_deleted_le_sum_degrees G D
  calc
    _ ≤ ∑ x ∈ D, G.degree x := hcut
    _ = ∑ _x ∈ D, d := Finset.sum_congr rfl fun x hx => hDtight x hx
    _ = k * d := by simp [hDcard]

/-- Weighted deleted-neighbor loss obeys the same `kd + k*choose(m,2)` bound
for selectors compatible with any survivor subgraph `K`. -/
theorem sum_weighted_deletedNeighborLoss_le_card_mul_degree_add_card_mul_choose
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hDcard : D.card = k) (hreg : ∀ x : V, G.degree x = d)
    (hcompat : GadgetAttachmentCompatible K F A) :
    (∑ w : W, ∑ a ∈ A w, (G.neighborFinset a.1 ∩ D).card) ≤
      k * d + k * (Fintype.card W).choose 2 := by
  let loss : {v : V // v ∉ D} → ℕ := fun v =>
    (G.neighborFinset v.1 ∩ D).card
  rw [sum_sum_weight_eq_sum_weight_mul_attachmentMultiplicity]
  have hlossle : ∀ v, loss v ≤ k := by
    intro v
    rw [← hDcard]
    exact Finset.card_le_card Finset.inter_subset_right
  have hpoint : ∀ v, loss v * attachmentMultiplicity A v ≤
      loss v + k * (attachmentMultiplicity A v).choose 2 := by
    intro v
    have ht := le_one_add_choose_two (attachmentMultiplicity A v)
    have hmul := Nat.mul_le_mul_left (loss v) ht
    have hchoose := Nat.mul_le_mul_right
      ((attachmentMultiplicity A v).choose 2) (hlossle v)
    nlinarith
  change (∑ v, loss v * attachmentMultiplicity A v) ≤ _
  calc
    (∑ v, loss v * attachmentMultiplicity A v) ≤
        ∑ v, (loss v + k * (attachmentMultiplicity A v).choose 2) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v, loss v) +
        k * ∑ v, (attachmentMultiplicity A v).choose 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ k * d + k * (Fintype.card W).choose 2 := by
      apply Nat.add_le_add
      · exact sum_deletedNeighborLoss_le_card_mul_degree_of_regular
          G D hDcard hreg
      · exact Nat.mul_le_mul_left k
          (hcompat.sum_choose_two_attachmentMultiplicity_le K F A)

/-- Weighted loss amplification is controlled by selector-pair multiplicity.
For deletion-only replacement it is at most `kd + k*choose(m,2)`. -/
theorem sum_replacementLoss_le_card_mul_degree_add_card_mul_choose_of_regular
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hDcard : D.card = k) (hreg : ∀ x : V, G.degree x = d)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    (∑ w : W, ∑ a ∈ A w,
      replacementDegreeLoss G D (deleteVertexSetGraph G D) a) ≤
      k * d + k * (Fintype.card W).choose 2 := by
  let loss : {v : V // v ∉ D} → ℕ := fun v =>
    (G.neighborFinset v.1 ∩ D).card
  have hloss : ∀ v : {v : V // v ∉ D},
      replacementDegreeLoss G D (deleteVertexSetGraph G D) v = loss v := by
    intro v
    simp [replacementDegreeLoss, subgraphDegreeLoss, loss]
  rw [sum_sum_weight_eq_sum_weight_mul_attachmentMultiplicity]
  simp_rw [hloss]
  have hlossle : ∀ v, loss v ≤ k := by
    intro v
    rw [← hDcard]
    exact Finset.card_le_card Finset.inter_subset_right
  have hpoint : ∀ v, loss v * attachmentMultiplicity A v ≤
      loss v + k * (attachmentMultiplicity A v).choose 2 := by
    intro v
    have ht := le_one_add_choose_two (attachmentMultiplicity A v)
    have hmul := Nat.mul_le_mul_left (loss v) ht
    have hchoose := Nat.mul_le_mul_right
      ((attachmentMultiplicity A v).choose 2) (hlossle v)
    nlinarith
  calc
    (∑ v, loss v * attachmentMultiplicity A v) ≤
        ∑ v, (loss v + k * (attachmentMultiplicity A v).choose 2) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v, loss v) +
        k * ∑ v, (attachmentMultiplicity A v).choose 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ k * d + k * (Fintype.card W).choose 2 := by
      apply Nat.add_le_add
      · exact sum_deletedNeighborLoss_le_card_mul_degree_of_regular
          G D hDcard hreg
      · exact Nat.mul_le_mul_left k
          (hcompat.sum_choose_two_attachmentMultiplicity_le
            (deleteVertexSetGraph G D) F A)

/-- The deletion-only weighted-loss bound only requires the deleted set,
rather than the whole graph, to consist of degree-`d` vertices. -/
theorem sum_replacementLoss_le_card_mul_degree_add_card_mul_choose_of_tight_set
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hDcard : D.card = k) (hDtight : ∀ x ∈ D, G.degree x = d)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    (∑ w : W, ∑ a ∈ A w,
      replacementDegreeLoss G D (deleteVertexSetGraph G D) a) ≤
      k * d + k * (Fintype.card W).choose 2 := by
  let loss : {v : V // v ∉ D} → ℕ := fun v =>
    (G.neighborFinset v.1 ∩ D).card
  have hloss : ∀ v : {v : V // v ∉ D},
      replacementDegreeLoss G D (deleteVertexSetGraph G D) v = loss v := by
    intro v
    simp [replacementDegreeLoss, subgraphDegreeLoss, loss]
  rw [sum_sum_weight_eq_sum_weight_mul_attachmentMultiplicity]
  simp_rw [hloss]
  have hlossle : ∀ v, loss v ≤ k := by
    intro v
    rw [← hDcard]
    exact Finset.card_le_card Finset.inter_subset_right
  have hpoint : ∀ v, loss v * attachmentMultiplicity A v ≤
      loss v + k * (attachmentMultiplicity A v).choose 2 := by
    intro v
    have ht := le_one_add_choose_two (attachmentMultiplicity A v)
    have hmul := Nat.mul_le_mul_left (loss v) ht
    have hchoose := Nat.mul_le_mul_right
      ((attachmentMultiplicity A v).choose 2) (hlossle v)
    nlinarith
  calc
    (∑ v, loss v * attachmentMultiplicity A v) ≤
        ∑ v, (loss v + k * (attachmentMultiplicity A v).choose 2) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v, loss v) +
        k * ∑ v, (attachmentMultiplicity A v).choose 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ k * d + k * (Fintype.card W).choose 2 := by
      apply Nat.add_le_add
      · exact sum_deletedNeighborLoss_le_card_mul_degree_of_tight_set
          G D hDcard hDtight
      · exact Nat.mul_le_mul_left k
          (hcompat.sum_choose_two_attachmentMultiplicity_le
            (deleteVertexSetGraph G D) F A)

/-- Without any regularity or tightness assumption, the natural upper bound
is the sum of the degrees of the deleted vertices plus the selector-pair
amplification budget. -/
theorem sum_replacementLoss_le_sum_deletedDegrees_add_card_mul_choose
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {k : ℕ}
    (hDcard : D.card = k)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    (∑ w : W, ∑ a ∈ A w,
      replacementDegreeLoss G D (deleteVertexSetGraph G D) a) ≤
      (∑ x ∈ D, G.degree x) + k * (Fintype.card W).choose 2 := by
  let loss : {v : V // v ∉ D} → ℕ := fun v =>
    (G.neighborFinset v.1 ∩ D).card
  have hloss : ∀ v : {v : V // v ∉ D},
      replacementDegreeLoss G D (deleteVertexSetGraph G D) v = loss v := by
    intro v
    simp [replacementDegreeLoss, subgraphDegreeLoss, loss]
  rw [sum_sum_weight_eq_sum_weight_mul_attachmentMultiplicity]
  simp_rw [hloss]
  have hlossle : ∀ v, loss v ≤ k := by
    intro v
    rw [← hDcard]
    exact Finset.card_le_card Finset.inter_subset_right
  have hpoint : ∀ v, loss v * attachmentMultiplicity A v ≤
      loss v + k * (attachmentMultiplicity A v).choose 2 := by
    intro v
    have ht := le_one_add_choose_two (attachmentMultiplicity A v)
    have hmul := Nat.mul_le_mul_left (loss v) ht
    have hchoose := Nat.mul_le_mul_right
      ((attachmentMultiplicity A v).choose 2) (hlossle v)
    nlinarith
  calc
    (∑ v, loss v * attachmentMultiplicity A v) ≤
        ∑ v, (loss v + k * (attachmentMultiplicity A v).choose 2) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v, loss v) +
        k * ∑ v, (attachmentMultiplicity A v).choose 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ x ∈ D, G.degree x) +
        k * (Fintype.card W).choose 2 := by
      apply Nat.add_le_add
      · exact sum_card_neighbor_inter_deleted_le_sum_degrees G D
      · exact Nat.mul_le_mul_left k
          (hcompat.sum_choose_two_attachmentMultiplicity_le
            (deleteVertexSetGraph G D) F A)

/-- **Deleted-degree-surplus obstruction.**  In an arbitrary Moore-layer
minimum-degree-`d` graph, successful deletion-only delete-`k`/add-`k+1`
replacement forces the deleted vertices collectively to have large degree
surplus above `d`. -/
theorem degree_sub_replacementPolynomial_le_deletedDegreeSurplus_of_moore
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    d - ((k + 1) * (k + 1) + k * (k + 1).choose 2) ≤
      ∑ x ∈ D, (G.degree x - d) := by
  let P := (k + 1) * (k + 1) + k * (k + 1).choose 2
  let E := ∑ x ∈ D, (G.degree x - d)
  have hlower :=
    card_succ_mul_degree_pred_sub_card_le_replacementLoss_of_mooreOrder
      G D (deleteVertexSetGraph G D) (le_refl _) F A hd hk hcard
        hDcard hWcard hmin hnew hcompat
  have hupper :=
    sum_replacementLoss_le_sum_deletedDegrees_add_card_mul_choose
      G D F A hDcard hcompat
  have hdegrees : ∀ x : V, d ≤ G.degree x := by
    intro x
    exact hmin.trans (G.minDegree_le_degree x)
  have hsum : (∑ x ∈ D, G.degree x) = k * d + E := by
    calc
      (∑ x ∈ D, G.degree x) = ∑ x ∈ D, (d + (G.degree x - d)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (Nat.add_sub_of_le (hdegrees x)).symm
      _ = k * d + E := by simp [E, hDcard, Finset.sum_add_distrib]
  rw [hsum, hWcard] at hupper
  change d - P ≤ E
  by_cases hPd : P ≤ d
  · have hPsub : d - P + P = d := Nat.sub_add_cancel hPd
    have hksub : d - 1 - k + (k + 1) = d := by omega
    have heq : (k + 1) * (d - 1 - k) =
        k * d + k * (k + 1).choose 2 + (d - P) := by
      dsimp [P] at hPsub ⊢
      nlinarith
    have htotal : (k + 1) * (d - 1 - k) ≤
        k * d + E + k * (k + 1).choose 2 := hlower.trans hupper
    rw [heq] at htotal
    omega
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hPd)]

/-- Above the fixed-`k` polynomial threshold, every successful deletion-only
replacement must delete at least one vertex whose degree is strictly above
the target. -/
theorem exists_above_target_in_deleted_set_of_moore_replacement
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hlarge : (k + 1) * (k + 1) + k * (k + 1).choose 2 < d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    ∃ x ∈ D, d < G.degree x := by
  have hsurplus :=
    degree_sub_replacementPolynomial_le_deletedDegreeSurplus_of_moore
      G D F A hd hk hcard hDcard hWcard hmin hnew hcompat
  by_contra hnone
  have hle : ∀ x ∈ D, G.degree x ≤ d := by
    intro x hx
    by_contra hnot
    apply hnone
    exact ⟨x, hx, by omega⟩
  have hzero : (∑ x ∈ D, (G.degree x - d)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact Nat.sub_eq_zero_of_le (hle x hx)
  rw [hzero] at hsurplus
  omega

/-- **Fixed-size replacement no-go for a tight deleted set.**  Global
regularity can be weakened to minimum degree at least `d` together with
degree exactly `d` on the vertices selected for deletion. -/
theorem not_gadgetCompatible_bounded_replacement_of_moore_tight_set
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hlarge : (k + 1) * (k + 1) + k * (k + 1).choose 2 < d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree) (hDtight : ∀ x ∈ D, G.degree x = d)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    ¬ GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A := by
  intro hcompat
  have hlower :=
    card_succ_mul_degree_pred_sub_card_le_replacementLoss_of_mooreOrder
      G D (deleteVertexSetGraph G D) (le_refl _) F A hd hk hcard
        hDcard hWcard hmin hnew hcompat
  have hupper :=
    sum_replacementLoss_le_card_mul_degree_add_card_mul_choose_of_tight_set
      G D F A hDcard hDtight hcompat
  rw [hWcard] at hupper
  have hksub : d - 1 - k + (k + 1) = d := by omega
  nlinarith

/-- **Fixed-size replacement no-go.**  In a `d`-regular Moore-layer graph,
delete-`k`/add-`k+1` repair without additional survivor-edge deletion is
impossible once `d > (k+1)² + k*choose(k+1,2)`. -/
theorem not_gadgetCompatible_bounded_replacement_of_moore_regular
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hlarge : (k + 1) * (k + 1) + k * (k + 1).choose 2 < d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hreg : ∀ x : V, G.degree x = d)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    ¬ GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A := by
  intro hcompat
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  have hmin : d ≤ G.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [hreg v]
  have hlower :=
    card_succ_mul_degree_pred_sub_card_le_replacementLoss_of_mooreOrder
      G D (deleteVertexSetGraph G D) (le_refl _) F A hd hk hcard
        hDcard hWcard hmin hnew hcompat
  have hupper :=
    sum_replacementLoss_le_card_mul_degree_add_card_mul_choose_of_regular
      G D F A hDcard hreg hcompat
  rw [hWcard] at hupper
  have hksub : d - 1 - k + (k + 1) = d := by omega
  nlinarith

/-- **Intrinsic fixed-size replacement no-go.**  Regularity need not be
assumed: C4-freeness, minimum degree `d`, and exact Moore-layer order force it.
Thus every deletion-only delete-`k`/add-`k+1` replacement fails above the same
polynomial threshold for every witness at this order. -/
theorem not_gadgetCompatible_bounded_replacement_of_c4Free_moore
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 2 ≤ d) (hk : k ≤ d - 1)
    (hlarge : (k + 1) * (k + 1) + k * (k + 1).choose 2 < d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    ¬ GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A := by
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_mooreOrder G hfree hd hmin hcard
  exact not_gadgetCompatible_bounded_replacement_of_moore_regular
    G D F A (by omega) hk hlarge hcard hDcard hWcard hreg hnew

/-- The arbitrary delete-one/add-two obstruction in natural witness form:
for `d≥6`, it applies to every C4-free minimum-degree-`d` graph at Moore-layer
order and every choice of the deleted vertex. -/
theorem not_gadgetCompatible_delete_one_add_pair_of_c4Free_moore
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ ({x} : Finset V)})
    {d : ℕ} (hd : 6 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hWcard : Fintype.card W = 2)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    ¬ GadgetAttachmentCompatible (deleteVertexSetGraph G {x}) F A := by
  have hreg : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_mooreOrder G hfree (by omega) hmin hcard
  exact not_gadgetCompatible_delete_one_add_pair_of_moore_regular
    G x F A hd hcard hreg hWcard hnew

/-- Existence form of the fixed-size obstruction: every compatible
deletion-only replacement forces the explicit cubic-scale inequality on `d`. -/
theorem degree_le_replacementPolynomial_of_moore_regular
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hreg : ∀ x : V, G.degree x = d)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    d ≤ (k + 1) * (k + 1) + k * (k + 1).choose 2 := by
  by_contra hnot
  exact (not_gadgetCompatible_bounded_replacement_of_moore_regular
    G D F A hd hk (Nat.lt_of_not_ge hnot) hcard hDcard hWcard hreg hnew) hcompat

/-- A simpler cubic consequence: compatible deletion-only replacement forces
`d ≤ (k+1)³`. -/
theorem degree_le_card_succ_cubed_of_moore_regular_replacement
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hreg : ∀ x : V, G.degree x = d)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A) :
    d ≤ (k + 1) * (k + 1) * (k + 1) := by
  have hpoly := degree_le_replacementPolynomial_of_moore_regular
    G D F A hd hk hcard hDcard hWcard hreg hnew hcompat
  have hchoose : (k + 1).choose 2 ≤ (k + 1) * (k + 1) := by
    have h := two_mul_choose_two_add_self (k + 1)
    nlinarith
  have hmul := Nat.mul_le_mul_left k hchoose
  nlinarith

/-- **Mandatory survivor-edge surgery.**  For a fully compensated
delete-`k`/add-`k+1` repair, any excess of `d` above the deletion-only
polynomial must be paid by attachment-weighted additional survivor-edge
loss. -/
theorem degree_sub_replacementPolynomial_le_weightedSubgraphLoss_of_moore_regular
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hreg : ∀ x : V, G.degree x = d)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    d - ((k + 1) * (k + 1) + k * (k + 1).choose 2) ≤
      ∑ w : W, ∑ a ∈ A w,
        subgraphDegreeLoss (deleteVertexSetGraph G D) K a := by
  let P := (k + 1) * (k + 1) + k * (k + 1).choose 2
  let E := ∑ w : W, ∑ a ∈ A w,
    subgraphDegreeLoss (deleteVertexSetGraph G D) K a
  have hmin : d ≤ G.minDegree := by
    letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [hreg v]
  have hlower :=
    card_succ_mul_degree_pred_sub_card_le_replacementLoss_of_mooreOrder
      G D K hKle F A hd hk hcard hDcard hWcard hmin hnew hcompat
  have hdelete :=
    sum_weighted_deletedNeighborLoss_le_card_mul_degree_add_card_mul_choose
      G D K F A hDcard hreg hcompat
  rw [hWcard] at hdelete
  have hdecomp :
      (∑ w : W, ∑ a ∈ A w, replacementDegreeLoss G D K a) =
        (∑ w : W, ∑ a ∈ A w, (G.neighborFinset a.1 ∩ D).card) + E := by
    simp only [replacementDegreeLoss, Finset.sum_add_distrib]
    rfl
  rw [hdecomp] at hlower
  change d - P ≤ E
  by_cases hPd : P ≤ d
  · have hPsub : d - P + P = d := Nat.sub_add_cancel hPd
    have hksub : d - 1 - k + (k + 1) = d := by omega
    have hleft : (k + 1) * (d - 1 - k) + (k + 1) * (k + 1) =
        (k + 1) * d := by
      rw [← Nat.mul_add, hksub]
    have hright : k * d + k * (k + 1).choose 2 + (d - P) +
        (k + 1) * (k + 1) = (k + 1) * d := by
      have hPsub' : d - P +
          ((k + 1) * (k + 1) + k * (k + 1).choose 2) = d := by
        simpa [P] using hPsub
      calc
        k * d + k * (k + 1).choose 2 + (d - P) +
            (k + 1) * (k + 1) = k * d + d := by omega
        _ = (k + 1) * d := by ring
    have heq : (k + 1) * (d - 1 - k) =
        k * d + k * (k + 1).choose 2 + (d - P) := by omega
    have htotal : (k + 1) * (d - 1 - k) ≤
        k * d + k * (k + 1).choose 2 + E := by omega
    rw [heq] at htotal
    omega
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hPd)]

end Erdos85
