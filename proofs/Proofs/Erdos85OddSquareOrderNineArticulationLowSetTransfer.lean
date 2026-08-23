import Proofs.Erdos85OddSquareOrderNineArticulationCapstone
import Proofs.Erdos85SecondOrderDefectSetTransfer

/-!
# Low-set transfer for the order-nine articulation equality branches

An explicit two-level partition on the 78 ordinary centers, together with
the matching upper level at all three high centers, gives a global formula
`A 1_R = (a+1) 1 - 1_Z`.  Applying the pointwise nonregular defect transfer
then gives the exact integer form of the audit's equations (20) and (23).
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The ordinary centers attaining the lower level of an explicit
order-nine incidence partition. -/
def orderNineOrdinaryLowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) (a : ℕ) : Finset V :=
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  O.filter fun x ↦ (G.neighborFinset x ∩ R).card = a

theorem orderNineOrdinaryLowSet_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) (a : ℕ) :
    orderNineOrdinaryLowSet G h₁ h₂ h₃ R a ⊆
      (Finset.univ : Finset V) \ {h₁, h₂, h₃} := by
  exact Finset.filter_subset _ _

/-- The lower level contains exactly the complement, among the 78 ordinary
centers, of the `r` upper-level centers. -/
theorem orderNineOrdinaryLowSet_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V) (a r : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r) :
    (orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card = 78 - r := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  let Z := O.filter fun x ↦ (G.neighborFinset x ∩ R).card = a
  let U := O.filter fun x ↦ (G.neighborFinset x ∩ R).card = a + 1
  change (∀ x, f x = a ∨ f x = a + 1) ∧
    (Finset.univ.filter fun x ↦ f x = a + 1).card = r at hpart
  have hHcard : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hOcard : O.card = 78 := by
    rw [show O = (Finset.univ : Finset V) \ H by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ H),
      Finset.card_univ, hcard, hHcard]
  let e : ↥(↑O : Set V) ↪ V := Function.Embedding.subtype _
  have hmap :
      (Finset.univ.filter fun x : ↥(↑O : Set V) ↦ f x = a + 1).map e = U := by
    ext x
    simp [e, U, f]
    constructor
    · rintro ⟨hxO, hx⟩
      exact ⟨hxO, hx⟩
    · rintro ⟨hxO, hx⟩
      exact ⟨hxO, hx⟩
  have hUcard : U.card = r := by
    calc
      U.card = ((Finset.univ.filter fun x : ↥(↑O : Set V) ↦
          f x = a + 1).map e).card := congrArg Finset.card hmap.symm
      _ = (Finset.univ.filter fun x : ↥(↑O : Set V) ↦
          f x = a + 1).card := Finset.card_map e
      _ = r := hpart.2
  have hcover : Z ∪ U = O := by
    ext x
    constructor
    · simp only [Finset.mem_union]
      aesop
    · intro hxO
      have hlevels := hpart.1 ⟨x, hxO⟩
      simpa [Z, U, f, hxO] using hlevels
  have hdisj : Disjoint Z U := by
    rw [Finset.disjoint_left]
    intro x hxZ hxU
    have hz := (Finset.mem_filter.mp hxZ).2
    have hu := (Finset.mem_filter.mp hxU).2
    omega
  have hcards : Z.card + U.card = O.card := by
    rw [← hcover, Finset.card_union_of_disjoint hdisj]
  change Z.card = 78 - r
  omega

theorem orderNineOrdinaryLowSet_card_eq_thirty_of_upper48
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V) (a : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a 48) :
    (orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card = 30 := by
  simpa using orderNineOrdinaryLowSet_card G hcard h₁ h₂ h₃
    h₁₂ h₁₃ h₂₃ R a 48 hpart

theorem orderNineOrdinaryLowSet_card_eq_eighteen_of_upper60
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V) (a : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a 60) :
    (orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card = 18 := by
  simpa using orderNineOrdinaryLowSet_card G hcard h₁ h₂ h₃
    h₁₂ h₁₃ h₂₃ R a 60 hpart

/-- The two ordinary levels and matching high-root values combine into the
global incidence identity `A 1_R = (a+1)1 - 1_Z`. -/
theorem orderNineOrdinaryExplicitPartition_global_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) (a r : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = a + 1)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = a + 1)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = a + 1) :
    ∀ x : V,
      ((G.neighborFinset x ∩ R).card : ℤ) =
        (a + 1 : ℕ) -
          (if x ∈ orderNineOrdinaryLowSet G h₁ h₂ h₃ R a then 1 else 0) := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  change (∀ x, f x = a ∨ f x = a + 1) ∧ _ at hpart
  intro x
  by_cases hx₁ : x = h₁
  · subst x
    simp [orderNineOrdinaryLowSet, hhigh₁]
  by_cases hx₂ : x = h₂
  · subst x
    simp [orderNineOrdinaryLowSet, hhigh₂]
  by_cases hx₃ : x = h₃
  · subst x
    simp [orderNineOrdinaryLowSet, hhigh₃]
  have hxO : x ∈ O := by simp [O, H, hx₁, hx₂, hx₃]
  have hlevels := hpart.1 ⟨x, hxO⟩
  change (G.neighborFinset x ∩ R).card = a ∨
    (G.neighborFinset x ∩ R).card = a + 1 at hlevels
  rcases hlevels with hlow | hupp
  · simp [orderNineOrdinaryLowSet, O, H, hxO, hlow]
  · simp [orderNineOrdinaryLowSet, O, H, hxO, hupp]

/-- **Order-nine low-set defect equation.**  This is the pointwise cardinal
form of

`D 1_R = diag(deg-1) 1_R + |R| 1 - (a+1) deg + A 1_Z`.

At `(a,|R|)=(5,50)` and `(3,34)` it is exactly the arithmetic content of
audit equations (20) and (23), before substituting degrees 9 and 10. -/
theorem orderNineOrdinaryExplicitPartition_defect_lowSet_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ : V) (R : Finset V) (a r : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = a + 1)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = a + 1)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = a + 1) :
    ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ R).card : ℤ) =
        ((G.degree x : ℤ) - 1) * (if x ∈ R then 1 else 0) + (R.card : ℤ) -
          (G.degree x : ℤ) * (a + 1 : ℕ) +
            ((G.neighborFinset x ∩
              orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card : ℤ) := by
  classical
  intro x
  have htransfer :=
    c4Free_secondOrderDefect_neighbor_inter_card_eq G hfree R x
  have hglobal := orderNineOrdinaryExplicitPartition_global_lowSet
    G h₁ h₂ h₃ R a r hpart hhigh₁ hhigh₂ hhigh₃
  rw [htransfer]
  have hsum :
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ R).card : ℤ)) =
      (G.degree x : ℤ) * (a + 1 : ℕ) -
        ((G.neighborFinset x ∩
          orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card : ℤ) := by
    simp_rw [hglobal]
    simp [G.card_neighborFinset_eq_degree, Finset.sum_sub_distrib, mul_comm]
  rw [hsum]
  ring

/-- In the order-nine three-high degree profile, the low-set equation takes
the uniform vector form

`D 1_R = 8 1_R + (|R|-9(a+1))1 - (a+1)1_H + A 1_Z`.

Thus `(a,|R|)=(5,50)` gives audit equation (20), while `(3,34)` gives (23). -/
theorem orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ : V) (R : Finset V) (a r : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = a + 1)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = a + 1)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = a + 1)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10) :
    ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ R).card : ℤ) =
        8 * (if x ∈ R then 1 else 0) + (R.card : ℤ) -
          9 * (a + 1 : ℕ) -
          (a + 1 : ℕ) *
            (if x ∈ ({h₁, h₂, h₃} : Finset V) then 1 else 0) +
          ((G.neighborFinset x ∩
            orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card : ℤ) := by
  classical
  intro x
  rw [orderNineOrdinaryExplicitPartition_defect_lowSet_eq G hfree
    h₁ h₂ h₃ R a r hpart hhigh₁ hhigh₂ hhigh₃ x]
  by_cases hxH : x ∈ ({h₁, h₂, h₃} : Finset V)
  · have hxR : x ∉ R := by
      intro hxR
      exact (Finset.disjoint_left.mp hRH) hxR hxH
    rw [hdegHigh x hxH]
    simp [hxH, hxR]
    ring
  · rw [hdegOrd x hxH]
    simp [hxH]

/-- The concrete low-set data at the order-34 equality branch: the low set
has 18 ordinary centers and every high root has exactly six neighbors in it. -/
theorem orderNine_order34_lowSet_card_and_high_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hRcard : R.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 4)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) :
    let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ R 3
    Z.card = 18 ∧
      (G.neighborFinset h₁ ∩ Z).card = 6 ∧
      (G.neighborFinset h₂ ∩ Z).card = 6 ∧
      (G.neighborFinset h₃ ∩ Z).card = 6 := by
  classical
  let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ R 3
  have hZcard : Z.card = 18 := by
    exact orderNineOrdinaryLowSet_card_eq_eighteen_of_upper60
      G hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R 3 hpart
  have heq := orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    G hfree h₁ h₂ h₃ R 3 60 hpart hhigh₁ hhigh₂ hhigh₃
      hRH hdegOrd hdegHigh
  have hroot (h : V) (hh : h ∈ ({h₁, h₂, h₃} : Finset V)) :
      (G.neighborFinset h ∩ Z).card = 6 := by
    have hnR : h ∉ R := by
      intro hR
      exact (Finset.disjoint_left.mp hRH) hR hh
    have hv := heq h
    rw [hdefectHighIsolated h hh] at hv
    simp [hRcard, hh, hnR] at hv
    dsimp only [Z] at hv ⊢
    omega
  exact ⟨hZcard,
    hroot h₁ (by simp), hroot h₂ (by simp), hroot h₃ (by simp)⟩

/-- Evaluating the order-34 low-set equation at the deleted ordinary owner:
two defect neighbors on the shore force exactly four original neighbors in
the 18-point low set. -/
theorem orderNine_order34_owner_lowSet_degree_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ owner : V) (R : Finset V)
    (hRcard : R.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 4)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hownerH : owner ∉ ({h₁, h₂, h₃} : Finset V))
    (hownerR : owner ∉ R)
    (hownerDefect :
      ((secondOrderDefectGraph G).neighborFinset owner ∩ R).card = 2) :
    (G.neighborFinset owner ∩
      orderNineOrdinaryLowSet G h₁ h₂ h₃ R 3).card = 4 := by
  classical
  have hv := orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    G hfree h₁ h₂ h₃ R 3 60 hpart hhigh₁ hhigh₂ hhigh₃
      hRH hdegOrd hdegHigh owner
  simp [hRcard, hownerH, hownerR, hownerDefect] at hv
  omega

/-- Abstract saturation step behind the order-34 owner argument.  An
18-point set of total incidence 18, with every nonowner incidence at most
one, consists entirely of incidence-one points if it omits the owner.  Four
owner neighbors in that set then contradict an ambient bin-one degree of
three. -/
theorem owner_mem_of_lowSet_incidence_saturation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (Z B₁ : Finset V) (k : V → ℕ)
    (hZcard : Z.card = 18)
    (hsum : (∑ z ∈ Z, k z) = 18)
    (hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1)
    (hbin₁ : ∀ z ∈ Z, k z = 1 → z ∈ B₁)
    (hownerZ : (G.neighborFinset owner ∩ Z).card = 4)
    (hownerB₁ : (G.neighborFinset owner ∩ B₁).card = 3) :
    owner ∈ Z := by
  classical
  by_contra hownerNotZ
  have hle : ∀ z ∈ Z, k z ≤ 1 := by
    intro z hz
    exact hcap z hz (fun hzo ↦ hownerNotZ (hzo ▸ hz))
  have hsumEq : (∑ z ∈ Z, k z) = ∑ _z ∈ Z, 1 := by
    simpa [hZcard] using hsum
  have hone : ∀ z ∈ Z, k z = 1 :=
    (Finset.sum_eq_sum_iff_of_le hle).mp hsumEq
  have hsub : G.neighborFinset owner ∩ Z ⊆
      G.neighborFinset owner ∩ B₁ := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
      hbin₁ z (Finset.mem_inter.mp hz).2
        (hone z (Finset.mem_inter.mp hz).2)⟩
  have hcardLe := Finset.card_le_card hsub
  rw [hownerZ, hownerB₁] at hcardLe
  omega

/-- Three named high roots with six low-set neighbors each give total
high-incidence mass 18 on the low set. -/
theorem orderNine_lowSet_highIncidence_sum_eq_eighteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (Z : Finset V)
    (hroot₁ : (G.neighborFinset h₁ ∩ Z).card = 6)
    (hroot₂ : (G.neighborFinset h₂ ∩ Z).card = 6)
    (hroot₃ : (G.neighborFinset h₃ ∩ Z).card = 6) :
    (∑ z ∈ Z, squareOrderHighIncidenceCount G 9 z) = 18 := by
  have hswap := sum_card_neighborFinset_inter_comm G Z
    (squareOrderHighVertices G 9)
  change (∑ z ∈ Z, squareOrderHighIncidenceCount G 9 z) =
    ∑ h ∈ squareOrderHighVertices G 9,
      (G.neighborFinset h ∩ Z).card at hswap
  rw [hH] at hswap
  simpa [h₁₂, h₁₃, h₂₃, hroot₁, hroot₂, hroot₃] using hswap

/-- In the second three-high profile, every ordinary vertex other than the
unique bin-three owner has at most one high neighbor. -/
theorem orderNine_secondProfile_nonowner_ordinary_highIncidence_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (owner z : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hzOrd : z ∈ (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (hzowner : z ≠ owner) :
    squareOrderHighIncidenceCount G 9 z ≤ 1 := by
  classical
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  have hkLe : k z ≤ 3 := by
    have hinter := Finset.card_le_card (Finset.inter_subset_right :
      G.neighborFinset z ∩ H ⊆ H)
    simpa [k, squareOrderHighIncidenceCount, H, hhigh] using hinter
  change k z ≤ 1
  by_contra hkNot
  have hkTwoOrThree : k z = 2 ∨ k z = 3 := by omega
  rcases hkTwoOrThree with hkTwo | hkThree
  · have hzB2 : z ∈ squareOrderNineLowIncidenceBin G 2 := by
      exact Finset.mem_filter.mpr ⟨hzOrd, hkTwo⟩
    have hB2card : (squareOrderNineLowIncidenceBin G 2).card = 0 := by
      rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
    rw [Finset.card_eq_zero.mp hB2card] at hzB2
    exact Finset.notMem_empty z hzB2
  · have hzB3 : z ∈ squareOrderNineLowIncidenceBin G 3 := by
      exact Finset.mem_filter.mpr ⟨hzOrd, hkThree⟩
    have hB3card : (squareOrderNineLowIncidenceBin G 3).card = 1 := by
      rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hB3card
    have hzEq : z = u := by simpa [hu] using hzB3
    have hownerEq : owner = u := by simpa [hu] using howner
    exact hzowner (hzEq.trans hownerEq.symm)

/-- **Order-34 owner membership.**  The 18-point, six-per-root low-set data
and the owner's four low-set neighbors force the unique bin-three owner to
belong to the low set. -/
theorem orderNine_secondProfile_owner_mem_order34_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (Z : Finset V)
    (hZsub : Z ⊆ (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (hZcard : Z.card = 18)
    (hroot₁ : (G.neighborFinset h₁ ∩ Z).card = 6)
    (hroot₂ : (G.neighborFinset h₂ ∩ Z).card = 6)
    (hroot₃ : (G.neighborFinset h₃ ∩ Z).card = 6)
    (hownerZ : (G.neighborFinset owner ∩ Z).card = 4) :
    owner ∈ Z := by
  classical
  let k := squareOrderHighIncidenceCount G 9
  let B₁ := squareOrderNineLowIncidenceBin G 1
  have hsum : (∑ z ∈ Z, k z) = 18 := by
    exact orderNine_lowSet_highIncidence_sum_eq_eighteen G
      h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH Z hroot₁ hroot₂ hroot₃
  have hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1 := by
    intro z hz hzowner
    exact orderNine_secondProfile_nonowner_ordinary_highIncidence_le_one
      G hp hhigh hc2 hc3 owner z howner (hZsub hz) hzowner
  have hbin₁ : ∀ z ∈ Z, k z = 1 → z ∈ B₁ := by
    intro z hz hk
    exact Finset.mem_filter.mpr ⟨hZsub hz, hk⟩
  have hownerB₁ : (G.neighborFinset owner ∩ B₁).card = 3 := by
    exact squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  exact owner_mem_of_lowSet_incidence_saturation G owner Z B₁ k
    hZcard hsum hcap hbin₁ hownerZ hownerB₁

end

end Erdos85

#print axioms Erdos85.orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
