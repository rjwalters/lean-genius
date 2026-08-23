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

/-- Once the incidence-three owner lies in an 18-point low set of total
incidence 18, and all other points have incidence at most one, the set
contains exactly fifteen incidence-one and two incidence-zero points. -/
theorem lowSet_incidence_one_zero_card_of_owner_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (owner : V) (Z : Finset V) (k : V → ℕ)
    (hZcard : Z.card = 18) (hsum : (∑ z ∈ Z, k z) = 18)
    (howner : owner ∈ Z) (hkowner : k owner = 3)
    (hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1) :
    (Z.filter fun z ↦ k z = 1).card = 15 ∧
      (Z.filter fun z ↦ k z = 0).card = 2 := by
  classical
  let Z₀ := Z.erase owner
  have hZ₀card : Z₀.card = 17 := by
    dsimp [Z₀]
    rw [Finset.card_erase_of_mem howner, hZcard]
  have hsplit := Finset.sum_erase_add Z k howner
  have hsumZ₀ : (∑ z ∈ Z₀, k z) = 15 := by
    dsimp [Z₀]
    omega
  have hpoint : ∀ z ∈ Z₀, k z = if k z = 1 then 1 else 0 := by
    intro z hz
    have hzParts := Finset.mem_erase.mp hz
    have hle := hcap z hzParts.2 hzParts.1
    by_cases hk : k z = 1
    · simp [hk]
    · have hkzero : k z = 0 := by omega
      simp [hkzero]
  have honeErase : (Z₀.filter fun z ↦ k z = 1).card = 15 := by
    calc
      (Z₀.filter fun z ↦ k z = 1).card =
          ∑ z ∈ Z₀, if k z = 1 then (1 : ℕ) else 0 := by
        rw [Finset.sum_boole]
        norm_num
      _ = ∑ z ∈ Z₀, k z := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (hpoint z hz).symm
      _ = 15 := hsumZ₀
  have honeFilter : Z₀.filter (fun z ↦ k z = 1) =
      Z.filter (fun z ↦ k z = 1) := by
    ext z
    constructor
    · intro hz
      have hp := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hp.1).2, hp.2⟩
    · intro hz
      have hp := Finset.mem_filter.mp hz
      have hne : z ≠ owner := by
        intro hzo
        subst z
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hp.1⟩, hp.2⟩
  have hone : (Z.filter fun z ↦ k z = 1).card = 15 := by
    rw [← honeFilter]
    exact honeErase
  let W := Z₀.filter fun z ↦ k z = 0
  let P := Z₀.filter fun z ↦ k z = 1
  have hcover : W ∪ P = Z₀ := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hzW | hzP
      · exact Finset.filter_subset _ _ hzW
      · exact Finset.filter_subset _ _ hzP
    · intro hz
      have hle := hcap z (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz).1
      have hk : k z = 0 ∨ k z = 1 := by omega
      simpa [W, P, hz] using hk
  have hdisj : Disjoint W P := by
    rw [Finset.disjoint_left]
    intro z hzW hzP
    have hzero := (Finset.mem_filter.mp hzW).2
    have hone' := (Finset.mem_filter.mp hzP).2
    omega
  have hcards : W.card + P.card = Z₀.card := by
    rw [← hcover, Finset.card_union_of_disjoint hdisj]
  have hPcard : P.card = 15 := by
    simpa [P] using honeErase
  have hWcard : W.card = 2 := by omega
  have hzeroFilter : W = Z.filter (fun z ↦ k z = 0) := by
    ext z
    constructor
    · intro hz
      have hp := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hp.1).2, hp.2⟩
    · intro hz
      have hp := Finset.mem_filter.mp hz
      have hne : z ≠ owner := by
        intro hzo
        subst z
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hp.1⟩, hp.2⟩
  refine ⟨hone, ?_⟩
  rw [← hzeroFilter]
  exact hWcard

/-- Profile-level translation of incidence saturation: the order-34 low set
contains fifteen bin-one points and two bin-zero points besides its unique
bin-three owner. -/
theorem orderNine_secondProfile_lowSet_bin_cards_of_owner_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (Z : Finset V)
    (hZsub : Z ⊆ (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (hZcard : Z.card = 18)
    (hsum : (∑ z ∈ Z, squareOrderHighIncidenceCount G 9 z) = 18)
    (hownerZ : owner ∈ Z) :
    (Z ∩ squareOrderNineLowIncidenceBin G 1).card = 15 ∧
      (Z ∩ squareOrderNineLowIncidenceBin G 0).card = 2 := by
  classical
  let k := squareOrderHighIncidenceCount G 9
  have hkowner : k owner = 3 := (Finset.mem_filter.mp howner).2
  have hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1 := by
    intro z hz hzowner
    exact orderNine_secondProfile_nonowner_ordinary_highIncidence_le_one
      G hp hhigh hc2 hc3 owner z howner (hZsub hz) hzowner
  have hcounts := lowSet_incidence_one_zero_card_of_owner_mem
    owner Z k hZcard hsum hownerZ hkowner hcap
  have hfilter (i : ℕ) : Z.filter (fun z ↦ k z = i) =
      Z ∩ squareOrderNineLowIncidenceBin G i := by
    ext z
    constructor
    · intro hz
      have hpz := Finset.mem_filter.mp hz
      exact Finset.mem_inter.mpr ⟨hpz.1,
        Finset.mem_filter.mpr ⟨hZsub hpz.1, hpz.2⟩⟩
    · intro hz
      have hpz := Finset.mem_inter.mp hz
      exact Finset.mem_filter.mpr ⟨hpz.1,
        (Finset.mem_filter.mp hpz.2).2⟩
  rw [hfilter 1, hfilter 0] at hcounts
  exact hcounts

/-- Membership of the deleted owner in the lower level turns the global
`A1_R = 4·1 - 1_Z` identity into an exact shore degree of three. -/
theorem orderNine_order34_owner_neighbor_inter_shore_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ owner : V) (R : Finset V)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 4)
    (hownerZ : owner ∈ orderNineOrdinaryLowSet G h₁ h₂ h₃ R 3) :
    (G.neighborFinset owner ∩ R).card = 3 := by
  have hv := orderNineOrdinaryExplicitPartition_global_lowSet
    G h₁ h₂ h₃ R 3 60 hpart hhigh₁ hhigh₂ hhigh₃ owner
  simp [hownerZ] at hv
  omega

/-- A low-degree bin-three owner has nine neighbors, three high and hence
six ordinary; deleting the owner itself does not change that neighborhood. -/
theorem orderNine_binThree_owner_ordinary_erase_neighbor_card_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (hdegree : G.degree owner = 9)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    let O := (Finset.univ : Finset V) \ squareOrderHighVertices G 9
    (G.neighborFinset owner ∩ O.erase owner).card = 6 := by
  classical
  let H := squareOrderHighVertices G 9
  let O := (Finset.univ : Finset V) \ H
  have hk : (G.neighborFinset owner ∩ H).card = 3 :=
    (Finset.mem_filter.mp howner).2
  have hsplit : (G.neighborFinset owner ∩ H) ∪
      (G.neighborFinset owner ∩ O) = G.neighborFinset owner := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hzH | hzO
      · exact (Finset.mem_inter.mp hzH).1
      · exact (Finset.mem_inter.mp hzO).1
    · intro hz
      by_cases hzH : z ∈ H
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzH⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzH⟩⟩)
  have hdisj : Disjoint (G.neighborFinset owner ∩ H)
      (G.neighborFinset owner ∩ O) := by
    rw [Finset.disjoint_left]
    intro z hzH hzO
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hzO).2).2
      (Finset.mem_inter.mp hzH).2
  have hcards : (G.neighborFinset owner ∩ H).card +
      (G.neighborFinset owner ∩ O).card = G.degree owner := by
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hsplit, G.card_neighborFinset_eq_degree] at hc
    exact hc.symm
  have hordinary : (G.neighborFinset owner ∩ O).card = 6 := by omega
  have herase : G.neighborFinset owner ∩ O.erase owner =
      G.neighborFinset owner ∩ O := by
    ext z
    constructor
    · intro hz
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
        (Finset.mem_erase.mp (Finset.mem_inter.mp hz).2).2⟩
    · intro hz
      have hadj := (G.mem_neighborFinset owner z).mp (Finset.mem_inter.mp hz).1
      have hne : z ≠ owner := by
        intro hzo
        subst z
        exact G.loopless.irrefl owner hadj
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
        Finset.mem_erase.mpr ⟨hne, (Finset.mem_inter.mp hz).2⟩⟩
  change (G.neighborFinset owner ∩ O.erase owner).card = 6
  rw [herase]
  exact hordinary

/-- If two disjoint shores partition the six ordinary neighbors of the
owner, a degree three into one shore forces degree three into the other. -/
theorem owner_neighbor_complementary_shores_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (U S T : Finset V)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hU : (G.neighborFinset owner ∩ U).card = 6)
    (hS : (G.neighborFinset owner ∩ S).card = 3) :
    (G.neighborFinset owner ∩ T).card = 3 := by
  have hset : (G.neighborFinset owner ∩ S) ∪
      (G.neighborFinset owner ∩ T) = G.neighborFinset owner ∩ U := by
    ext z
    simp only [Finset.mem_union, Finset.mem_inter]
    rw [← hunion, Finset.mem_union]
    aesop
  have hinterDisj : Disjoint (G.neighborFinset owner ∩ S)
      (G.neighborFinset owner ∩ T) := by
    exact hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  have hcards : (G.neighborFinset owner ∩ S).card +
      (G.neighborFinset owner ∩ T).card =
      (G.neighborFinset owner ∩ U).card := by
    rw [← hset, Finset.card_union_of_disjoint hinterDisj]
  omega

/-- **Audit equation (24).**  If the low set is the disjoint union of the
owner, an incidence-one part `P`, and a two-point incidence-zero part `W`,
then four owner neighbors in the low set, together with the profile bounds
`p ≤ 3` and `q ≤ 2`, leave only `(p,q)=(2,2)` or `(3,1)`. -/
theorem owner_lowSet_neighbor_type_card_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPW : Disjoint P W)
    (hownerZ : (G.neighborFinset owner ∩ Z).card = 4)
    (hownerP : (G.neighborFinset owner ∩ P).card ≤ 3)
    (hownerW : (G.neighborFinset owner ∩ W).card ≤ 2) :
    ((G.neighborFinset owner ∩ P).card = 2 ∧
      (G.neighborFinset owner ∩ W).card = 2) ∨
    ((G.neighborFinset owner ∩ P).card = 3 ∧
      (G.neighborFinset owner ∩ W).card = 1) := by
  classical
  have hset : G.neighborFinset owner ∩ Z =
      (G.neighborFinset owner ∩ P) ∪
        (G.neighborFinset owner ∩ W) := by
    ext z
    constructor
    · intro hz
      have hzN := (Finset.mem_inter.mp hz).1
      have hzZ := (Finset.mem_inter.mp hz).2
      rw [hpartition] at hzZ
      rcases Finset.mem_insert.mp hzZ with hzo | hzPW
      · subst z
        exact (G.loopless.irrefl owner
          ((G.mem_neighborFinset owner owner).mp hzN)).elim
      · rcases Finset.mem_union.mp hzPW with hzP | hzW
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hzN, hzP⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hzN, hzW⟩)
    · intro hz
      rcases Finset.mem_union.mp hz with hzP | hzW
      · have hp := Finset.mem_inter.mp hzP
        exact Finset.mem_inter.mpr ⟨hp.1, by
          rw [hpartition]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hp.2)⟩
      · have hw := Finset.mem_inter.mp hzW
        exact Finset.mem_inter.mpr ⟨hw.1, by
          rw [hpartition]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hw.2)⟩
  have hdisj : Disjoint (G.neighborFinset owner ∩ P)
      (G.neighborFinset owner ∩ W) :=
    hPW.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsum : (G.neighborFinset owner ∩ P).card +
      (G.neighborFinset owner ∩ W).card = 4 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hset, hownerZ]
  omega

/-- A low set containing its incidence-three owner and capped by one away
from it is exactly the owner together with its incidence-one and zero parts. -/
theorem lowSet_eq_insert_incidence_one_union_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (owner : V) (Z : Finset V) (k : V → ℕ)
    (howner : owner ∈ Z)
    (hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1) :
    Z = insert owner ((Z.filter fun z ↦ k z = 1) ∪
      (Z.filter fun z ↦ k z = 0)) := by
  classical
  ext z
  constructor
  · intro hz
    by_cases hzo : z = owner
    · exact Finset.mem_insert.mpr (Or.inl hzo)
    · have hle := hcap z hz hzo
      have hk : k z = 0 ∨ k z = 1 := by omega
      refine Finset.mem_insert.mpr (Or.inr ?_)
      rcases hk with hk | hk
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hk⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hk⟩)
  · intro hz
    rcases Finset.mem_insert.mp hz with hzo | hz
    · simpa [hzo] using howner
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1

/-- Profile-facing form of audit (24), with `P=Z∩B₁` and `W=Z∩B₀`. -/
theorem orderNine_secondProfile_owner_lowSet_neighbor_bin_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (Z : Finset V)
    (hZsub : Z ⊆ (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (hZcard : Z.card = 18)
    (hsum : (∑ z ∈ Z, squareOrderHighIncidenceCount G 9 z) = 18)
    (hownerMem : owner ∈ Z)
    (hownerZ : (G.neighborFinset owner ∩ Z).card = 4)
    (hownerB₁ : (G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1).card = 3) :
    let P := Z ∩ squareOrderNineLowIncidenceBin G 1
    let W := Z ∩ squareOrderNineLowIncidenceBin G 0
    ((G.neighborFinset owner ∩ P).card = 2 ∧
      (G.neighborFinset owner ∩ W).card = 2) ∨
    ((G.neighborFinset owner ∩ P).card = 3 ∧
      (G.neighborFinset owner ∩ W).card = 1) := by
  classical
  let k := squareOrderHighIncidenceCount G 9
  let B₁ := squareOrderNineLowIncidenceBin G 1
  let B₀ := squareOrderNineLowIncidenceBin G 0
  let P := Z ∩ B₁
  let W := Z ∩ B₀
  have hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1 := by
    intro z hz hzowner
    exact orderNine_secondProfile_nonowner_ordinary_highIncidence_le_one
      G hp hhigh hc2 hc3 owner z howner (hZsub hz) hzowner
  have hcounts := orderNine_secondProfile_lowSet_bin_cards_of_owner_mem
    G hp hhigh hc2 hc3 owner howner Z hZsub hZcard hsum hownerMem
  have hfilter (i : ℕ) : Z.filter (fun z ↦ k z = i) =
      Z ∩ squareOrderNineLowIncidenceBin G i := by
    ext z
    constructor
    · intro hz
      have hpz := Finset.mem_filter.mp hz
      exact Finset.mem_inter.mpr ⟨hpz.1,
        Finset.mem_filter.mpr ⟨hZsub hpz.1, hpz.2⟩⟩
    · intro hz
      have hpz := Finset.mem_inter.mp hz
      exact Finset.mem_filter.mpr ⟨hpz.1,
        (Finset.mem_filter.mp hpz.2).2⟩
  have hpartition := lowSet_eq_insert_incidence_one_union_zero
    owner Z k hownerMem hcap
  rw [hfilter 1, hfilter 0] at hpartition
  change Z = insert owner (P ∪ W) at hpartition
  have hPW : Disjoint P W := by
    rw [Finset.disjoint_left]
    intro z hzP hzW
    have hpz := (Finset.mem_filter.mp (Finset.mem_inter.mp hzP).2).2
    have hwz := (Finset.mem_filter.mp (Finset.mem_inter.mp hzW).2).2
    omega
  have hPbound : (G.neighborFinset owner ∩ P).card ≤ 3 := by
    calc
      (G.neighborFinset owner ∩ P).card ≤
          (G.neighborFinset owner ∩ B₁).card := Finset.card_le_card (by
            intro z hz
            exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
              (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).2⟩)
      _ = 3 := hownerB₁
  have hWbound : (G.neighborFinset owner ∩ W).card ≤ 2 := by
    calc
      (G.neighborFinset owner ∩ W).card ≤ W.card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = 2 := hcounts.2
  exact owner_lowSet_neighbor_type_card_dichotomy G owner Z P W
    hpartition hPW hownerZ hPbound hWbound

/-- Evaluating audit equation (23) at an ordinary bin-one point whose defect
neighbors are all on its own shore: its `Z`-degree is one on the order-34
shore and two on the opposite shore. -/
theorem orderNine_order34_lowSet_degree_of_defect_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ z : V) (R : Finset V)
    (hRcard : R.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 4)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hzOrd : z ∉ ({h₁, h₂, h₃} : Finset V))
    (hdefectShore :
      ((secondOrderDefectGraph G).neighborFinset z ∩ R).card =
        if z ∈ R then 7 else 0) :
    (G.neighborFinset z ∩
      orderNineOrdinaryLowSet G h₁ h₂ h₃ R 3).card =
        if z ∈ R then 1 else 2 := by
  classical
  have hv := orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    G hfree h₁ h₂ h₃ R 3 60 hpart hhigh₁ hhigh₂ hhigh₃
      hRH hdegOrd hdegHigh z
  rw [hRcard, hdefectShore] at hv
  simp [hzOrd] at hv
  by_cases hzR : z ∈ R <;> simp [hzR] at hv ⊢ <;> omega

/-- Evaluating audit equation (23) at an ordinary bin-zero point whose eight
defect neighbors stay on its own shore gives `Z`-degree two on either shore.
This is the degree input used to eliminate the surviving placement in (26)
and all placements in (27). -/
theorem orderNine_order34_binZero_lowSet_degree_eq_two_of_defect_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ z : V) (R : Finset V)
    (hRcard : R.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 4)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hzOrd : z ∉ ({h₁, h₂, h₃} : Finset V))
    (hdefectShore :
      ((secondOrderDefectGraph G).neighborFinset z ∩ R).card =
        if z ∈ R then 8 else 0) :
    (G.neighborFinset z ∩
      orderNineOrdinaryLowSet G h₁ h₂ h₃ R 3).card = 2 := by
  classical
  have hv := orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    G hfree h₁ h₂ h₃ R 3 60 hpart hhigh₁ hhigh₂ hhigh₃
      hRH hdegOrd hdegHigh z
  rw [hRcard, hdefectShore] at hv
  simp [hzOrd] at hv
  by_cases hzR : z ∈ R <;> simp [hzR] at hv <;> omega

/-- Removing the owner contribution and a zero-neighbor `P` part from the
low-set degree gives audit equation (25): `W`-degree zero on the order-34
shore and one off it. -/
theorem owner_partner_W_degree_of_lowSet_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner z : V) (R Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hownerW : owner ∉ W)
    (hadj : G.Adj z owner)
    (hPzero : (G.neighborFinset z ∩ P).card = 0)
    (hZdegree : (G.neighborFinset z ∩ Z).card =
      if z ∈ R then 1 else 2) :
    (G.neighborFinset z ∩ W).card = if z ∈ R then 0 else 1 := by
  classical
  have hPempty : G.neighborFinset z ∩ P = ∅ :=
    Finset.card_eq_zero.mp hPzero
  have hset : G.neighborFinset z ∩ Z =
      insert owner (G.neighborFinset z ∩ W) := by
    ext u
    constructor
    · intro hu
      have huParts := Finset.mem_inter.mp hu
      rw [hpartition] at huParts
      rcases Finset.mem_insert.mp huParts.2 with huo | huPW
      · exact Finset.mem_insert.mpr (Or.inl huo)
      · rcases Finset.mem_union.mp huPW with huP | huW
        · have : u ∈ G.neighborFinset z ∩ P :=
            Finset.mem_inter.mpr ⟨huParts.1, huP⟩
          rw [hPempty] at this
          exact (Finset.notMem_empty u this).elim
        · exact Finset.mem_insert.mpr (Or.inr
            (Finset.mem_inter.mpr ⟨huParts.1, huW⟩))
    · intro hu
      rcases Finset.mem_insert.mp hu with huo | huW
      · subst u
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z owner).mpr hadj,
          by rw [hpartition]; exact Finset.mem_insert_self owner _⟩
      · have huParts := Finset.mem_inter.mp huW
        exact Finset.mem_inter.mpr ⟨huParts.1, by
          rw [hpartition]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ huParts.2)⟩
  have hownerNot : owner ∉ G.neighborFinset z ∩ W := by
    intro h
    exact hownerW (Finset.mem_inter.mp h).2
  have hcard : (G.neighborFinset z ∩ Z).card =
      (G.neighborFinset z ∩ W).card + 1 := by
    rw [hset, Finset.card_insert_of_notMem hownerNot]
  by_cases hzR : z ∈ R
  · rw [if_pos hzR] at hZdegree ⊢
    omega
  · rw [if_neg hzR] at hZdegree ⊢
    omega

/-- A degree-`k` vertex in one of two complementary relatively closed
shores has all `k` defect neighbors in its own shore and none across. -/
theorem neighbor_inter_shore_card_eq_if_of_complementary_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (U S T : Finset V) (z : V)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hzU : z ∈ U)
    (hzNeighborsU : D.neighborFinset z ⊆ U)
    (hSclosed : ∀ x ∈ S, D.neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T, D.neighborFinset x ∩ U ⊆ T)
    {k : ℕ} (hzdegree : D.degree z = k) :
    (D.neighborFinset z ∩ S).card = if z ∈ S then k else 0 := by
  classical
  by_cases hzS : z ∈ S
  · rw [if_pos hzS]
    have hsub : D.neighborFinset z ⊆ S := by
      intro y hy
      exact hSclosed z hzS (Finset.mem_inter.mpr
        ⟨hy, hzNeighborsU hy⟩)
    have heq : D.neighborFinset z ∩ S = D.neighborFinset z := by
      exact Finset.inter_eq_left.mpr hsub
    rw [heq, D.card_neighborFinset_eq_degree, hzdegree]
  · rw [if_neg hzS]
    have hzT : z ∈ T := by
      have hzUnion : z ∈ S ∪ T := by rw [hunion]; exact hzU
      rcases Finset.mem_union.mp hzUnion with hzS' | hzT
      · exact (hzS hzS').elim
      · exact hzT
    have hsub : D.neighborFinset z ⊆ T := by
      intro y hy
      exact hTclosed z hzT (Finset.mem_inter.mpr
        ⟨hy, hzNeighborsU hy⟩)
    have hempty : D.neighborFinset z ∩ S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      have hyParts := Finset.mem_inter.mp hy
      exact (Finset.disjoint_left.mp hdisj) hyParts.2 (hsub hyParts.1)
    rw [hempty, Finset.card_empty]

/-- Owner-punctured variant of the closed-shore count.  The universe `U`
omits one distinguished defect neighbor `owner`; all other defect neighbors
stay in the point's shore.  Thus a degree-eight point adjacent to the owner
has seven defect neighbors on its shore and none across. -/
theorem neighbor_inter_shore_card_eq_if_of_complementary_closed_punctured_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (owner : V) (U S T : Finset V) (z : V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hzU : z ∈ U) (hzOwner : D.Adj z owner)
    (hneighbors : ∀ x ∈ U, D.neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S, D.neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T, D.neighborFinset x ∩ U ⊆ T)
    (hzdegree : D.degree z = 8) :
    (D.neighborFinset z ∩ S).card = if z ∈ S then 7 else 0 := by
  classical
  have hSsubU : S ⊆ U := by
    intro x hx
    have : x ∈ S ∪ T := Finset.mem_union_left _ hx
    rw [hunion] at this
    exact this
  by_cases hzS : z ∈ S
  · rw [if_pos hzS]
    have hownerNotS : owner ∉ S := fun h ↦ hownerNotU (hSsubU h)
    have heq : D.neighborFinset z ∩ S = (D.neighborFinset z).erase owner := by
      ext y
      constructor
      · intro hy
        have hyParts := Finset.mem_inter.mp hy
        exact Finset.mem_erase.mpr ⟨fun h ↦ hownerNotS (h ▸ hyParts.2), hyParts.1⟩
      · intro hy
        have hyParts := Finset.mem_erase.mp hy
        have hyInsert := hneighbors z hzU hyParts.2
        have hyU : y ∈ U := by
          rcases Finset.mem_insert.mp hyInsert with h | h
          · exact (hyParts.1 h).elim
          · exact h
        exact Finset.mem_inter.mpr ⟨hyParts.2,
          hSclosed z hzS (Finset.mem_inter.mpr ⟨hyParts.2, hyU⟩)⟩
    have hownerMem : owner ∈ D.neighborFinset z :=
      (D.mem_neighborFinset z owner).mpr hzOwner
    rw [heq, Finset.card_erase_of_mem hownerMem,
      D.card_neighborFinset_eq_degree, hzdegree]
  · rw [if_neg hzS]
    have hzT : z ∈ T := by
      have hzUnion : z ∈ S ∪ T := by rw [hunion]; exact hzU
      rcases Finset.mem_union.mp hzUnion with h | h
      · exact (hzS h).elim
      · exact h
    have hempty : D.neighborFinset z ∩ S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      have hyParts := Finset.mem_inter.mp hy
      have hyT := hTclosed z hzT (Finset.mem_inter.mpr
        ⟨hyParts.1, hSsubU hyParts.2⟩)
      exact (Finset.disjoint_left.mp hdisj) hyParts.2 hyT
    rw [hempty, Finset.card_empty]

/-- Second-profile specialization of the closed-shore count: a bin-one
vertex has defect degree seven, hence seven defect neighbors on the shore
containing it and zero on the other. -/
theorem orderNine_binOne_defect_neighbor_inter_shore_card_eq_if
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (U S T : Finset V) (z : V)
    (hzB₁ : z ∈ squareOrderNineLowIncidenceBin G 1)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hzU : z ∈ U)
    (hneighborsU : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T) :
    ((secondOrderDefectGraph G).neighborFinset z ∩ S).card =
      if z ∈ S then 7 else 0 := by
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hzB₁
  dsimp only at hledger
  have hzdegree : (secondOrderDefectGraph G).degree z = 7 := by
    omega
  exact neighbor_inter_shore_card_eq_if_of_complementary_closed
    (secondOrderDefectGraph G) U S T z hunion hdisj hzU
      (hneighborsU z hzU) hSclosed hTclosed hzdegree

/-- Bin-zero specialization of the closed-shore count.  A second-profile
bin-zero point has defect degree eight, hence all eight defect neighbors lie
on its own shore and none lie across. -/
theorem orderNine_binZero_defect_neighbor_inter_shore_card_eq_if
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (U S T : Finset V) (z : V)
    (hzB₀ : z ∈ squareOrderNineLowIncidenceBin G 0)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hzU : z ∈ U)
    (hneighborsU : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T) :
    ((secondOrderDefectGraph G).neighborFinset z ∩ S).card =
      if z ∈ S then 8 else 0 := by
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hzB₀
  dsimp only at hledger
  have hzdegree : (secondOrderDefectGraph G).degree z = 8 := by
    omega
  exact neighbor_inter_shore_card_eq_if_of_complementary_closed
    (secondOrderDefectGraph G) U S T z hunion hdisj hzU
      (hneighborsU z hzU) hSclosed hTclosed hzdegree

/-- Corrected exceptional-bin-zero evaluation of audit equation (23) on
owner-punctured shores.  An exceptional point has seven defect neighbors on
the order-34 shore and none on the other shore, so its low-set degree is one
on the order-34 side and two on the order-43 side. -/
theorem orderNine_order34_exceptional_binZero_lowSet_degree_eq_if
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ z : V) (R : Finset V)
    (hRcard : R.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = 4)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hzOrd : z ∉ ({h₁, h₂, h₃} : Finset V))
    (hdefectShore :
      ((secondOrderDefectGraph G).neighborFinset z ∩ R).card =
        if z ∈ R then 7 else 0) :
    (G.neighborFinset z ∩
      orderNineOrdinaryLowSet G h₁ h₂ h₃ R 3).card =
        if z ∈ R then 1 else 2 := by
  classical
  have hv := orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    G hfree h₁ h₂ h₃ R 3 60 hpart hhigh₁ hhigh₂ hhigh₃
      hRH hdegOrd hdegHigh z
  rw [hRcard, hdefectShore] at hv
  simp [hzOrd] at hv
  by_cases hzR : z ∈ R <;> simp [hzR] at hv ⊢ <;> omega

/-- An owner-adjacent bin-one point has no original neighbors in any subset
of the bin-one class; this is the zero-`P` input to audit equation (25). -/
theorem orderNine_secondProfile_owner_partner_neighbor_inter_binOneSubset_eq_zero
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
    (owner z : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hzB₁ : z ∈ squareOrderNineLowIncidenceBin G 1)
    (hadj : G.Adj z owner)
    (P : Finset V) (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1) :
    (G.neighborFinset z ∩ P).card = 0 := by
  have hdegrees := squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner hzB₁
  dsimp only at hdegrees
  have hB₁zero : (G.neighborFinset z ∩
      squareOrderNineLowIncidenceBin G 1).card = 0 := by
    simpa [hadj] using hdegrees.1
  apply Nat.eq_zero_of_le_zero
  calc
    (G.neighborFinset z ∩ P).card ≤
        (G.neighborFinset z ∩ squareOrderNineLowIncidenceBin G 1).card :=
      Finset.card_le_card (by
        intro y hy
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).1,
          hPsub (Finset.mem_inter.mp hy).2⟩)
    _ = 0 := hB₁zero

/-- **Audit equation (25), composed.**  Every owner-adjacent bin-one point
has no `P`-neighbors; defect closure gives seven defect neighbors on the
order-34 shore and zero across; equation (23) then forces `W`-degree zero
on that shore and one on the complementary shore. -/
theorem orderNine_secondProfile_owner_partner_W_degree_eq_if_order34_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner z : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hzB₁ : z ∈ squareOrderNineLowIncidenceBin G 1)
    (hadj : G.Adj z owner)
    (U S T : Finset V)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hzOrd : z ∉ ({h₁, h₂, h₃} : Finset V))
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hzU : z ∈ U)
    (hneighborsU : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (Z P W : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hP : P = Z ∩ squareOrderNineLowIncidenceBin G 1)
    (hW : W = Z ∩ squareOrderNineLowIncidenceBin G 0)
    (hpartition : Z = insert owner (P ∪ W)) :
    (G.neighborFinset z ∩ W).card = if z ∈ S then 0 else 1 := by
  classical
  have hdefect := orderNine_binOne_defect_neighbor_inter_shore_card_eq_if
    G hfree hmin hcover hcard U S T z hzB₁ hunion hdisj hzU
      hneighborsU hSclosed hTclosed
  have hZdegree := orderNine_order34_lowSet_degree_of_defect_shore
    G hfree h₁ h₂ h₃ z S hScard hpart hhigh₁ hhigh₂ hhigh₃
      hSH hdegOrd hdegHigh hzOrd hdefect
  rw [← hZ] at hZdegree
  have hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1 := by
    rw [hP]
    exact Finset.inter_subset_right
  have hPzero :=
    orderNine_secondProfile_owner_partner_neighbor_inter_binOneSubset_eq_zero
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 owner z howner hzB₁
        hadj P hPsub
  have hownerW : owner ∉ W := by
    intro how
    have howB₀ : owner ∈ squareOrderNineLowIncidenceBin G 0 := by
      rw [hW] at how
      exact (Finset.mem_inter.mp how).2
    have hk3 := (Finset.mem_filter.mp howner).2
    have hk0 := (Finset.mem_filter.mp howB₀).2
    omega
  exact owner_partner_W_degree_of_lowSet_partition
    G owner z S Z P W hpartition hownerW hadj hPzero hZdegree

/-- Two distinct neighbors of an owner cannot both meet a second vertex:
the owner and that vertex would be two distinct common neighbors, producing
a four-cycle.  This is the repeated terminal contradiction in the order-34
placement analysis. -/
theorem false_of_distinct_owner_neighbors_share_second
    {V : Type*} (G : SimpleGraph V)
    (hfree : ¬ containsC4 V G)
    {owner w a b : V}
    (hab : a ≠ b) (how : owner ≠ w)
    (haOwner : G.Adj a owner) (hbOwner : G.Adj b owner)
    (haw : G.Adj a w) (hbw : G.Adj b w) : False := by
  exact hfree (containsC4_of_two_common hab how
    haOwner.symm hbOwner.symm haw.symm hbw.symm)

/-- **Audit equation (27).**  Let `W` have two bin-zero points, exactly one
adjacent to the universal bin-three owner.  Among the owner's bin-one
neighbors, at most one can have `W`-degree one.  Indeed, no such bin-one
point can meet the owner-adjacent member of `W`, so two of them would both
meet the other member and form a four-cycle with the owner. -/
theorem orderNine_secondProfile_owner_partners_W_degree_one_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (W K : Finset V)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hKB₁ : K ⊆ squareOrderNineLowIncidenceBin G 1)
    (hKowner : ∀ z ∈ K, G.Adj z owner)
    (hKWdegree : ∀ z ∈ K, (G.neighborFinset z ∩ W).card = 1) :
    K.card ≤ 1 := by
  classical
  let C := W \ G.neighborFinset owner
  have hCcard : C.card = 1 := by
    dsimp only [C]
    rw [Finset.card_sdiff]
    rw [hownerW, hWcard]
  apply Finset.card_le_one.mpr
  intro z hz z' hz'
  by_contra hzz'
  have hzNonempty : (G.neighborFinset z ∩ W).Nonempty := by
    rw [← Finset.card_pos, hKWdegree z hz]
    omega
  have hz'Nonempty : (G.neighborFinset z' ∩ W).Nonempty := by
    rw [← Finset.card_pos, hKWdegree z' hz']
    omega
  obtain ⟨w, hw⟩ := hzNonempty
  obtain ⟨w', hw'⟩ := hz'Nonempty
  have hwParts := Finset.mem_inter.mp hw
  have hw'Parts := Finset.mem_inter.mp hw'
  have hwC : w ∈ C := by
    exact Finset.mem_sdiff.mpr ⟨hwParts.2, by
      intro hwOwner
      have hwB₀ := hWsub hwParts.2
      have hnot := squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
        G hfree hhigh howner hwB₀ (hKB₁ hz) ((G.mem_neighborFinset owner w).mp hwOwner)
      exact hnot ((G.adj_comm z w).mp ((G.mem_neighborFinset z w).mp hwParts.1))⟩
  have hw'C : w' ∈ C := by
    exact Finset.mem_sdiff.mpr ⟨hw'Parts.2, by
      intro hw'Owner
      have hw'B₀ := hWsub hw'Parts.2
      have hnot := squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
        G hfree hhigh howner hw'B₀ (hKB₁ hz')
          ((G.mem_neighborFinset owner w').mp hw'Owner)
      exact hnot ((G.adj_comm z' w').mp
        ((G.mem_neighborFinset z' w').mp hw'Parts.1))⟩
  have hww' : w = w' :=
    Finset.card_le_one.mp (Nat.le_of_eq hCcard) w hwC w' hw'C
  have hOwnerW : owner ≠ w := by
    intro how
    have hk3 : squareOrderHighIncidenceCount G 9 owner = 3 :=
      (Finset.mem_filter.mp howner).2
    have hownerB₀ : owner ∈ squareOrderNineLowIncidenceBin G 0 :=
      how.symm ▸ hWsub hwParts.2
    have hk0 : squareOrderHighIncidenceCount G 9 owner = 0 :=
      (Finset.mem_filter.mp hownerB₀).2
    omega
  exact false_of_distinct_owner_neighbors_share_second G hfree
    hzz' hOwnerW (hKowner z hz) (hKowner z' hz')
      ((G.mem_neighborFinset z w).mp hwParts.1)
      (by rw [hww']; exact (G.mem_neighborFinset z' w').mp hw'Parts.1)

/-- Repeated terminal in the `b = 1` and `b = 0` analyses following (27).
Two distinct bin-zero neighbors of the owner, each of `Z`-degree two and
each avoiding the owner-adjacent point of `W`, must both meet the unique
point of `W \ N(owner)`.  Together with the owner this is a four-cycle. -/
theorem false_of_orderNine_order34_two_binZero_neighbors_avoid_owner_W
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (owner y z : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hyB₀ : y ∈ squareOrderNineLowIncidenceBin G 0)
    (hzB₀ : z ∈ squareOrderNineLowIncidenceBin G 0)
    (hyz : y ≠ z)
    (hyOwner : G.Adj y owner) (hzOwner : G.Adj z owner)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hyZ : (G.neighborFinset y ∩ Z).card = 2)
    (hzZ : (G.neighborFinset z ∩ Z).card = 2)
    (hyAvoid : (G.neighborFinset y ∩
      (G.neighborFinset owner ∩ W)).card = 0)
    (hzAvoid : (G.neighborFinset z ∩
      (G.neighborFinset owner ∩ W)).card = 0) : False := by
  classical
  let C := W \ G.neighborFinset owner
  have hCcard : C.card = 1 := by
    dsimp only [C]
    rw [Finset.card_sdiff, hownerW, hWcard]
  obtain ⟨wy, hwyMem, hwyNe⟩ := Finset.exists_mem_ne
    (by rw [hyZ]; omega : 1 < (G.neighborFinset y ∩ Z).card) owner
  obtain ⟨wz, hwzMem, hwzNe⟩ := Finset.exists_mem_ne
    (by rw [hzZ]; omega : 1 < (G.neighborFinset z ∩ Z).card) owner
  have hwyParts := Finset.mem_inter.mp hwyMem
  have hwzParts := Finset.mem_inter.mp hwzMem
  have hwyW : wy ∈ W := by
    rw [hpartition] at hwyParts
    rcases Finset.mem_insert.mp hwyParts.2 with hwyOwner | hwyPW
    · exact (hwyNe hwyOwner).elim
    · rcases Finset.mem_union.mp hwyPW with hwyP | hwyW
      · have hpB₁ := hPsub hwyP
        have hnot := squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
          G hfree hhigh howner hyB₀ hpB₁ hyOwner.symm
        exact (hnot ((G.mem_neighborFinset y wy).mp hwyParts.1)).elim
      · exact hwyW
  have hwzW : wz ∈ W := by
    rw [hpartition] at hwzParts
    rcases Finset.mem_insert.mp hwzParts.2 with hwzOwner | hwzPW
    · exact (hwzNe hwzOwner).elim
    · rcases Finset.mem_union.mp hwzPW with hwzP | hwzW
      · have hpB₁ := hPsub hwzP
        have hnot := squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
          G hfree hhigh howner hzB₀ hpB₁ hzOwner.symm
        exact (hnot ((G.mem_neighborFinset z wz).mp hwzParts.1)).elim
      · exact hwzW
  have hwyC : wy ∈ C := Finset.mem_sdiff.mpr ⟨hwyW, by
    intro hOwnerWy
    have hmem : wy ∈ G.neighborFinset y ∩
        (G.neighborFinset owner ∩ W) :=
      Finset.mem_inter.mpr ⟨hwyParts.1,
        Finset.mem_inter.mpr ⟨hOwnerWy, hwyW⟩⟩
    have hempty := Finset.card_eq_zero.mp hyAvoid
    rw [hempty] at hmem
    simp at hmem⟩
  have hwzC : wz ∈ C := Finset.mem_sdiff.mpr ⟨hwzW, by
    intro hOwnerWz
    have hmem : wz ∈ G.neighborFinset z ∩
        (G.neighborFinset owner ∩ W) :=
      Finset.mem_inter.mpr ⟨hwzParts.1,
        Finset.mem_inter.mpr ⟨hOwnerWz, hwzW⟩⟩
    have hempty := Finset.card_eq_zero.mp hzAvoid
    rw [hempty] at hmem
    simp at hmem⟩
  have hwywz : wy = wz :=
    Finset.card_le_one.mp (Nat.le_of_eq hCcard) wy hwyC wz hwzC
  exact false_of_distinct_owner_neighbors_share_second G hfree hyz
    hwyNe.symm hyOwner hzOwner
      ((G.mem_neighborFinset y wy).mp hwyParts.1)
      (by rw [hwywz]; exact (G.mem_neighborFinset z wz).mp hwzParts.1)

/-- Terminal for the sole placement left by audit (26).  A bin-zero neighbor
of the universal owner has no original neighbor in the bin-one part `P`.
If the placement also leaves it with no neighbor in the two-point part `W`,
then its only neighbor in `Z = {owner} ∪ P ∪ W` is the owner, contradicting
the `Z`-degree two forced by equation (23). -/
theorem false_of_orderNine_order34_owner_neighbor_outside_low_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (owner y : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hyB₀ : y ∈ squareOrderNineLowIncidenceBin G 0)
    (hyOwner : G.Adj y owner)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWzero : (G.neighborFinset y ∩ W).card = 0)
    (hZtwo : (G.neighborFinset y ∩ Z).card = 2) : False := by
  classical
  have hPzero : (G.neighborFinset y ∩ P).card = 0 := by
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have hpParts := Finset.mem_inter.mp hp
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh howner hyB₀ (hPsub hpParts.2) hyOwner.symm)
        ((G.mem_neighborFinset y p).mp hpParts.1)
  have hPempty : G.neighborFinset y ∩ P = ∅ := Finset.card_eq_zero.mp hPzero
  have hWempty : G.neighborFinset y ∩ W = ∅ := Finset.card_eq_zero.mp hWzero
  have hset : G.neighborFinset y ∩ Z = {owner} := by
    ext u
    constructor
    · intro hu
      have huParts := Finset.mem_inter.mp hu
      rw [hpartition] at huParts
      rcases Finset.mem_insert.mp huParts.2 with huOwner | huPW
      · simp [huOwner]
      · rcases Finset.mem_union.mp huPW with huP | huW
        · have huEmpty : u ∈ (∅ : Finset V) := by
            rw [← hPempty]
            exact Finset.mem_inter.mpr ⟨huParts.1, huP⟩
          simp at huEmpty
        · have huEmpty : u ∈ (∅ : Finset V) := by
            rw [← hWempty]
            exact Finset.mem_inter.mpr ⟨huParts.1, huW⟩
          simp at huEmpty
    · intro hu
      have huOwner : u = owner := Finset.mem_singleton.mp hu
      subst u
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y owner).mpr hyOwner,
        by rw [hpartition]; exact Finset.mem_insert_self owner _⟩
  rw [hset, Finset.card_singleton] at hZtwo
  omega

/-- Local package used in audit (26).  For the three original bin-zero
neighbors of the universal bin-three owner, either the three-edge branch has
no nondefect neighbor, or the four-edge branch has exactly two.  In the
latter branch those two vertices are adjacent, have the regular defect type
`(B₀,B₁,B₃)=(5,3,0)`, and have no original bin-one neighbor. -/
theorem orderNine_secondProfile_owner_binZero_local_type_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let R := (G.neighborFinset owner ∩ B 0) \ D.neighborFinset owner
    ((G.induce (G.neighborSet owner)).edgeFinset.card = 3 ∧ R.card = 0) ∨
      ((G.induce (G.neighborSet owner)).edgeFinset.card = 4 ∧ R.card = 2 ∧
        ∀ y ∈ R,
          ((D.neighborFinset y ∩ B 0).card = 5 ∧
            (D.neighborFinset y ∩ B 1).card = 3 ∧
            (D.neighborFinset y ∩ B 3).card = 0) ∧
          (∀ z ∈ R, y ≠ z → G.Adj y z) ∧
          (∀ p ∈ B 1, ¬ G.Adj y p)) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let R := (G.neighborFinset owner ∩ B 0) \ D.neighborFinset owner
  have hsplit :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hsplit
  rcases hsplit with hthree | hfour
  · exact Or.inl hthree
  · right
    refine ⟨hfour.1, hfour.2, ?_⟩
    intro y hyR
    have hyRegular :=
      squareOrderNine_threeHigh_secondProfile_nondefect_binZero_is_regular
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hyR
    dsimp only at hyRegular
    refine ⟨hyRegular, ?_, ?_⟩
    · intro z hzR hyz
      exact
        squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
          G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
            hyR hzR hyz hfour.1
    · intro p hpB
      have hyB : y ∈ B 0 :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp hyR).1).2
      have hOwnerY : G.Adj owner y :=
        (G.mem_neighborFinset owner y).mp
          (Finset.mem_inter.mp (Finset.mem_sdiff.mp hyR).1).1
      exact squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
        G hfree hhigh howner hyB hpB hOwnerY

/-- An exceptional original bin-zero neighbor of the universal owner avoids
every other original owner-neighbor.  Such a point is precisely an original
defect neighbor of the owner, hence its owner edge is triangle-free and has
no common neighbor.  This supplies the avoidance hypotheses in the
post-(27) placement terminals. -/
theorem orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner y z : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0 ∩
      (secondOrderDefectGraph G).neighborFinset owner)
    (hzOwner : G.Adj owner z) :
    ¬ G.Adj y z := by
  intro hyz
  have heq :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hyTf : y ∈ triangleFreeNeighbors G owner := by
    rw [← heq]
    exact hy
  have htfParts := (mem_triangleFreeNeighbors G owner y).mp hyTf
  have hzCommon : z ∈ G.neighborFinset owner ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset owner z).mpr hzOwner,
      (G.mem_neighborFinset y z).mpr hyz⟩
  have hpos : 0 < (G.neighborFinset owner ∩ G.neighborFinset y).card :=
    Finset.card_pos.mpr ⟨z, hzCommon⟩
  rw [htfParts.2] at hpos
  omega

/-- Exact four-edge geometry at the universal owner.  Its three original
bin-zero neighbors split into one exceptional defect point and two regular
nondefect points.  The regular pair is adjacent, while the exceptional point
is adjacent to neither member of that pair. -/
theorem orderNine_secondProfile_owner_four_edge_binZero_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 4) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let U := G.neighborFinset owner ∩ B 0
    let E := U ∩ D.neighborFinset owner
    let R := U \ D.neighborFinset owner
    E.card = 1 ∧ R.card = 2 ∧
      (∀ e ∈ E, ∀ r ∈ R, ¬ G.Adj e r) ∧
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → G.Adj r s) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let U := G.neighborFinset owner ∩ B 0
  let E := U ∩ D.neighborFinset owner
  let R := U \ D.neighborFinset owner
  have heq :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hEcard : E.card = 1 := by
    have hEtf : E = triangleFreeNeighbors G owner := by
      simpa [E, U, B, D] using heq
    rw [hEtf]
    rcases hprofile with hthree | hfour
    · omega
    · exact hfour.2.1
  have hRpair :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hRpair
  have hRcard : R.card = 2 := by
    rcases hRpair with hthree | hfour
    · omega
    · simpa [R, U, B, D] using hfour.2
  refine ⟨hEcard, hRcard, ?_, ?_⟩
  · intro e he r hr
    have hrParts := Finset.mem_sdiff.mp hr
    have hrU := Finset.mem_inter.mp hrParts.1
    exact orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner he
        ((G.mem_neighborFinset owner r).mp hrU.1)
  · intro r hr s hs hrs
    exact
      squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
          (by simpa [R, U, B, D] using hr)
          (by simpa [R, U, B, D] using hs) hrs hloc

/-- Composed post-(27) terminal for two exceptional points.  Under the
`(3,1)` low-set data, two distinct original bin-zero defect neighbors of the
owner each have `Z`-degree two.  Their triangle-free owner edges make both
avoid the owner-adjacent point of `W`, so the two-point forcing terminal
produces a four-cycle. -/
theorem false_of_orderNine_order34_two_owner_defect_binZero_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner y z : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0 ∩
      (secondOrderDefectGraph G).neighborFinset owner)
    (hz : z ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0 ∩
      (secondOrderDefectGraph G).neighborFinset owner)
    (hyz : y ≠ z)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hyZ : (G.neighborFinset y ∩ Z).card = 2)
    (hzZ : (G.neighborFinset z ∩ Z).card = 2) : False := by
  classical
  have hyParts := Finset.mem_inter.mp hy
  have hzParts := Finset.mem_inter.mp hz
  have hyInner := Finset.mem_inter.mp hyParts.1
  have hzInner := Finset.mem_inter.mp hzParts.1
  have hyOwner : G.Adj y owner :=
    (G.adj_comm owner y).mp ((G.mem_neighborFinset owner y).mp hyInner.1)
  have hzOwner : G.Adj z owner :=
    (G.adj_comm owner z).mp ((G.mem_neighborFinset owner z).mp hzInner.1)
  have hyAvoid : (G.neighborFinset y ∩
      (G.neighborFinset owner ∩ W)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hwParts := Finset.mem_inter.mp hw
    have hwOwner := (Finset.mem_inter.mp hwParts.2).1
    exact (orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hy
        ((G.mem_neighborFinset owner w).mp hwOwner))
          ((G.mem_neighborFinset y w).mp hwParts.1)
  have hzAvoid : (G.neighborFinset z ∩
      (G.neighborFinset owner ∩ W)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hwParts := Finset.mem_inter.mp hw
    have hwOwner := (Finset.mem_inter.mp hwParts.2).1
    exact (orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hz
        ((G.mem_neighborFinset owner w).mp hwOwner))
          ((G.mem_neighborFinset z w).mp hwParts.1)
  exact false_of_orderNine_order34_two_binZero_neighbors_avoid_owner_W
    G hfree hhigh owner y z howner hyInner.2 hzInner.2 hyz
      hyOwner hzOwner Z P W hpartition hPsub hWcard hownerW
      hyZ hzZ hyAvoid hzAvoid

/-- The three-local-edge branch of the `(3,1)` placement is impossible.
All three original bin-zero owner-neighbors are exceptional defect points;
choosing two of them invokes the preceding two-exceptional terminal. -/
theorem false_of_orderNine_order34_three_edge_owner_W_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 3)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hZdegree : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset y ∩ Z).card = 2) : False := by
  classical
  let E := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
    (secondOrderDefectGraph G).neighborFinset owner
  have heq :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hEcard : E.card = 3 := by
    have hEtf : E = triangleFreeNeighbors G owner := by
      simpa [E] using heq
    rw [hEtf]
    rcases hprofile with hthree | hfour
    · exact hthree.2.1
    · omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp
    (by rw [hEcard]; omega : 1 < E.card)
  exact false_of_orderNine_order34_two_owner_defect_binZero_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
      (by simpa [E] using hy) (by simpa [E] using hz) hyz
      Z P W hpartition hPsub hWcard hownerW
      (hZdegree y (by simpa [E] using hy))
      (hZdegree z (by simpa [E] using hz))

/-- The four-local-edge branch of the `(3,1)` placement is impossible.  If
the owner's unique point in `W` is exceptional, the two regular points both
avoid it; if it is regular, that point and the unique exceptional point both
avoid it (the regular point by irreflexivity).  In either case two bin-zero
owner-neighbors satisfy the singleton-complement forcing terminal. -/
theorem false_of_orderNine_order34_four_edge_owner_W_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 4)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hZdegree : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0),
      (G.neighborFinset y ∩ Z).card = 2) : False := by
  classical
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let U := G.neighborFinset owner ∩ B 0
  let E := U ∩ D.neighborFinset owner
  let R := U \ D.neighborFinset owner
  have hgeom := orderNine_secondProfile_owner_four_edge_binZero_partition
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hloc
  dsimp only at hgeom
  have hEcard : E.card = 1 := by simpa [E, U, B, D] using hgeom.1
  have hRcard : R.card = 2 := by simpa [R, U, B, D] using hgeom.2.1
  have hER : ∀ e ∈ E, ∀ r ∈ R, ¬ G.Adj e r := by
    simpa [E, R, U, B, D] using hgeom.2.2.1
  obtain ⟨s, hOeq⟩ := Finset.card_eq_one.mp hownerW
  have hsO : s ∈ G.neighborFinset owner ∩ W := by rw [hOeq]; simp
  have hsOParts := Finset.mem_inter.mp hsO
  have hsU : s ∈ U := Finset.mem_inter.mpr ⟨hsOParts.1, hWsub hsOParts.2⟩
  by_cases hsE : s ∈ E
  · obtain ⟨r, hr, t, ht, hrt⟩ := Finset.one_lt_card.mp
      (by rw [hRcard]; omega : 1 < R.card)
    have hrParts := Finset.mem_sdiff.mp hr
    have htParts := Finset.mem_sdiff.mp ht
    have hrU := Finset.mem_inter.mp hrParts.1
    have htU := Finset.mem_inter.mp htParts.1
    have hrAvoid : (G.neighborFinset r ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      rw [hOeq]
      simp [G.adj_comm, hER s hsE r hr]
    have htAvoid : (G.neighborFinset t ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      rw [hOeq]
      simp [G.adj_comm, hER s hsE t ht]
    exact false_of_orderNine_order34_two_binZero_neighbors_avoid_owner_W
      G hfree hhigh owner r t howner hrU.2 htU.2 hrt
        ((G.adj_comm owner r).mp ((G.mem_neighborFinset owner r).mp hrU.1))
        ((G.adj_comm owner t).mp ((G.mem_neighborFinset owner t).mp htU.1))
        Z P W hpartition hPsub hWcard hownerW
        (hZdegree r (by simpa [U, B] using hrParts.1))
        (hZdegree t (by simpa [U, B] using htParts.1))
        hrAvoid htAvoid
  · have hsNotD : s ∉ D.neighborFinset owner := by
      intro hsD
      exact hsE (Finset.mem_inter.mpr ⟨hsU, hsD⟩)
    have hsR : s ∈ R := Finset.mem_sdiff.mpr ⟨hsU, hsNotD⟩
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by rw [hEcard]; omega)
    have heParts := Finset.mem_inter.mp he
    have heU := Finset.mem_inter.mp heParts.1
    have hse : s ≠ e := by
      intro h
      subst e
      exact hsE he
    have hsAvoid : (G.neighborFinset s ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      rw [hOeq]
      simp
    have heAvoid : (G.neighborFinset e ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      rw [hOeq]
      apply Finset.card_eq_zero.mpr
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have hwParts := Finset.mem_inter.mp hw
      have hws : w = s := Finset.mem_singleton.mp hwParts.2
      subst w
      exact (hER e he s hsR) ((G.mem_neighborFinset e s).mp hwParts.1)
    have hsU' : s ∈ G.neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0 := by
      simpa [U, B] using hsU
    have hsU'Parts := Finset.mem_inter.mp hsU'
    exact false_of_orderNine_order34_two_binZero_neighbors_avoid_owner_W
      G hfree hhigh owner s e howner
        hsU'Parts.2 heU.2 hse
        ((G.adj_comm owner s).mp ((G.mem_neighborFinset owner s).mp hsU'Parts.1))
        ((G.adj_comm owner e).mp ((G.mem_neighborFinset owner e).mp heU.1))
        Z P W hpartition hPsub hWcard hownerW
        (hZdegree s hsU')
        (hZdegree e (by simpa [U, B] using heParts.1))
        hsAvoid heAvoid

/-- Full `(3,1)` local assembly.  The owner's local-triangle profile has
either three or four edges, and the preceding two capstones eliminate the
respective alternatives under the same sharp low-set data. -/
theorem false_of_orderNine_order34_owner_W_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hZdegree : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0),
      (G.neighborFinset y ∩ Z).card = 2) : False := by
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  rcases hprofile with hthree | hfour
  · exact false_of_orderNine_order34_three_edge_owner_W_one
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
        hthree.2.2 Z P W hpartition hPsub hWcard hownerW
        (by
          intro y hy
          exact hZdegree y (Finset.mem_inter.mp hy).1)
  · exact false_of_orderNine_order34_four_edge_owner_W_one
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
        hfour.2.2 Z P W hpartition hPsub hWsub hWcard hownerW hZdegree

/-- Full `(2,2)` local capstone.  If the owner meets both points of the
two-point bin-zero set `W`, then every point of `W` is an owner-neighbor.
The local profile always supplies an exceptional original bin-zero defect
neighbor `e`; its triangle-free owner edge makes it avoid all of `W`.
Since it also has no original neighbor in `P`, its only neighbor in `Z` is
the owner, contradicting its required `Z`-degree two. -/
theorem false_of_orderNine_order34_owner_W_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 2)
    (hZdegree : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0),
      (G.neighborFinset y ∩ Z).card = 2) : False := by
  classical
  let E := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
    (secondOrderDefectGraph G).neighborFinset owner
  have hEcardAlt :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_card
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hEcardAlt' : E.card = 3 ∨ E.card = 1 := by
    simpa [E] using hEcardAlt
  have hEpos : 0 < E.card := by rcases hEcardAlt' with h | h <;> omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hEpos
  have heParts := Finset.mem_inter.mp he
  have heU := Finset.mem_inter.mp heParts.1
  have hWinter : G.neighborFinset owner ∩ W = W := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · rw [hWcard, hownerW]
  have hWzero : (G.neighborFinset e ∩ W).card = 0 := by
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hwParts := Finset.mem_inter.mp hw
    have hwOwnerMem : w ∈ G.neighborFinset owner := by
      have : w ∈ G.neighborFinset owner ∩ W := by
        rw [hWinter]
        exact hwParts.2
      exact (Finset.mem_inter.mp this).1
    exact (orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner he
        ((G.mem_neighborFinset owner w).mp hwOwnerMem))
          ((G.mem_neighborFinset e w).mp hwParts.1)
  exact false_of_orderNine_order34_owner_neighbor_outside_low_parts
    G hfree hhigh owner e howner heU.2
      ((G.adj_comm owner e).mp ((G.mem_neighborFinset owner e).mp heU.1))
      Z P W hpartition hPsub hWzero (hZdegree e heParts.1)

/-- Conditional global-to-local order-34 assembly.  Complementary fully
defect-closed shores
turn every bin-zero owner-neighbor's defect degree eight into the exact
`8/0` shore count; equation (23) then gives `Z`-degree two.  The sharp owner
split is either `(2,2)` or `(3,1)`, dispatched respectively to the two local
capstones above.  The actual articulation shores omit the owner and therefore
require the punctured `7/0` transfer, not this full-closure interface. -/
theorem false_of_orderNine_order34_owner_W_dichotomy_of_closed_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (U S T : Finset V)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsU : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hownerB₀U : ∀ y ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0, y ∈ U)
    (hownerB₀Ord : ∀ y ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0,
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (Z P W : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerWAlt :
      (G.neighborFinset owner ∩ W).card = 2 ∨
      (G.neighborFinset owner ∩ W).card = 1) : False := by
  have hZdegree : ∀ y ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0,
      (G.neighborFinset y ∩ Z).card = 2 := by
    intro y hy
    have hyParts := Finset.mem_inter.mp hy
    have hdefect := orderNine_binZero_defect_neighbor_inter_shore_card_eq_if
      G hfree hmin hcover hcard U S T y hyParts.2 hunion hdisj
        (hownerB₀U y hy) hneighborsU hSclosed hTclosed
    have hlow := orderNine_order34_binZero_lowSet_degree_eq_two_of_defect_shore
      G hfree h₁ h₂ h₃ y S hScard hpart hhigh₁ hhigh₂ hhigh₃
        hSH hdegOrd hdegHigh (hownerB₀Ord y hy) hdefect
    rw [← hZ] at hlow
    exact hlow
  rcases hownerWAlt with htwo | hone
  · exact false_of_orderNine_order34_owner_W_two
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
        Z P W hpartition hPsub hWcard htwo hZdegree
  · exact false_of_orderNine_order34_owner_W_one
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
        Z P W hpartition hPsub hWsub hWcard hone hZdegree

/-- Conditional sharp-data wrapper for the full-closure interface above.
The order-34 explicit
partition and its 18-point low set determine
`Z = {owner} ∪ (Z∩B₁) ∪ (Z∩B₀)`, with two bin-zero points.  The owner-degree
calculation gives exactly the `(2,2)`/`(3,1)` dichotomy, while defect-closed
shores provide the bin-zero `Z`-degree input.  The preceding master theorem
then eliminates both alternatives.  This is not the actual owner-punctured
articulation capstone: its `hneighborsU` hypothesis fails for exceptional
points adjacent to the deleted owner. -/
theorem false_of_orderNine_order34_sharp_lowSet_of_closed_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (U S T : Finset V)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsU : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hownerB₀U : ∀ y ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0, y ∈ U)
    (hownerB₀Ord : ∀ y ∈ G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0,
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (Z : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hZsub : Z ⊆ (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (hZcard : Z.card = 18)
    (hsum : (∑ z ∈ Z, squareOrderHighIncidenceCount G 9 z) = 18)
    (hownerMem : owner ∈ Z)
    (hownerZ : (G.neighborFinset owner ∩ Z).card = 4)
    (hownerB₁ : (G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1).card = 3) : False := by
  classical
  let k := squareOrderHighIncidenceCount G 9
  let P := Z ∩ squareOrderNineLowIncidenceBin G 1
  let W := Z ∩ squareOrderNineLowIncidenceBin G 0
  have hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1 := by
    intro z hz hzowner
    exact orderNine_secondProfile_nonowner_ordinary_highIncidence_le_one
      G hp hhigh hc2 hc3 owner z howner (hZsub hz) hzowner
  have hfilter (i : ℕ) : Z.filter (fun z ↦ k z = i) =
      Z ∩ squareOrderNineLowIncidenceBin G i := by
    ext z
    constructor
    · intro hz
      have hzParts := Finset.mem_filter.mp hz
      exact Finset.mem_inter.mpr ⟨hzParts.1,
        Finset.mem_filter.mpr ⟨hZsub hzParts.1, hzParts.2⟩⟩
    · intro hz
      have hzParts := Finset.mem_inter.mp hz
      exact Finset.mem_filter.mpr ⟨hzParts.1,
        (Finset.mem_filter.mp hzParts.2).2⟩
  have hpartition := lowSet_eq_insert_incidence_one_union_zero
    owner Z k hownerMem hcap
  rw [hfilter 1, hfilter 0] at hpartition
  change Z = insert owner (P ∪ W) at hpartition
  have hcounts := orderNine_secondProfile_lowSet_bin_cards_of_owner_mem
    G hp hhigh hc2 hc3 owner howner Z hZsub hZcard hsum hownerMem
  have hWcard : W.card = 2 := by simpa [W] using hcounts.2
  have hdich := orderNine_secondProfile_owner_lowSet_neighbor_bin_dichotomy
    G hp hhigh hc2 hc3 owner howner Z hZsub hZcard hsum
      hownerMem hownerZ hownerB₁
  dsimp only at hdich
  have hownerWAlt :
      (G.neighborFinset owner ∩ W).card = 2 ∨
      (G.neighborFinset owner ∩ W).card = 1 := by
    rcases hdich with htwo | hone
    · exact Or.inl (by simpa [W] using htwo.2)
    · exact Or.inr (by simpa [W] using hone.2)
  have hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1 := by
    exact Finset.inter_subset_right
  have hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0 := by
    exact Finset.inter_subset_right
  exact false_of_orderNine_order34_owner_W_dichotomy_of_closed_shores
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
      h₁ h₂ h₃ owner howner U S T hScard hpart
      hhigh₁ hhigh₂ hhigh₃ hSH hdegOrd hdegHigh
      hunion hdisj hneighborsU hSclosed hTclosed
      hownerB₀U hownerB₀Ord Z P W hZ hpartition
      hPsub hWsub hWcard hownerWAlt

/-- Corrected owner-punctured elimination of the three-edge `(2,2)` branch.
All three local exceptional/original bin-zero neighbors avoid both points of
`W`, because owner-W degree two makes every point of `W` an owner-neighbor.
An exceptional point off `S` would have `Z`-degree two but only the owner as
a `Z`-neighbor, so all three lie on `S`.  They form a subset of the total
five-point defect neighborhood, whose FullType shore intersection has card
two, a contradiction. -/
theorem false_of_orderNine_order34_three_edge_owner_W_two_punctured
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 3)
    (S Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 2)
    (hTotalDefectS :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card = 2)
    (hZdegree : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset y ∩ Z).card = if y ∈ S then 1 else 2) : False := by
  classical
  let E := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
    (secondOrderDefectGraph G).neighborFinset owner
  let F := (secondOrderDefectGraph G).neighborFinset owner ∩
    squareOrderNineLowIncidenceBin G 0
  have heq :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hEcard : E.card = 3 := by
    have hEtf : E = triangleFreeNeighbors G owner := by simpa [E] using heq
    rw [hEtf]
    rcases hprofile with hthree | hfour
    · exact hthree.2.1
    · omega
  have hWinter : G.neighborFinset owner ∩ W = W := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · rw [hWcard, hownerW]
  have hESub : E ⊆ F ∩ S := by
    intro y hy
    have hyParts := Finset.mem_inter.mp hy
    have hyU := Finset.mem_inter.mp hyParts.1
    have hyF : y ∈ F := Finset.mem_inter.mpr ⟨hyParts.2, hyU.2⟩
    have hyS : y ∈ S := by
      by_contra hyNotS
      have hyZtwo : (G.neighborFinset y ∩ Z).card = 2 := by
        simpa [hyNotS] using hZdegree y (by simpa [E] using hy)
      have hWzero : (G.neighborFinset y ∩ W).card = 0 := by
        apply Finset.card_eq_zero.mpr
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        have hwParts := Finset.mem_inter.mp hw
        have hwOwnerMem : w ∈ G.neighborFinset owner := by
          have : w ∈ G.neighborFinset owner ∩ W := by
            rw [hWinter]
            exact hwParts.2
          exact (Finset.mem_inter.mp this).1
        exact (orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
          G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
            (by simpa [E] using hy)
            ((G.mem_neighborFinset owner w).mp hwOwnerMem))
              ((G.mem_neighborFinset y w).mp hwParts.1)
      exact false_of_orderNine_order34_owner_neighbor_outside_low_parts
        G hfree hhigh owner y howner hyU.2
          ((G.adj_comm owner y).mp ((G.mem_neighborFinset owner y).mp hyU.1))
          Z P W hpartition hPsub hWzero hyZtwo
    exact Finset.mem_inter.mpr ⟨hyF, hyS⟩
  have hcardLe := Finset.card_le_card hESub
  change (F ∩ S).card = 2 at hTotalDefectS
  rw [hEcard, hTotalDefectS] at hcardLe
  omega

/-- Corrected three-edge `(3,1)` placement split.  At most one local
exceptional point lies off `S`: two such points have `Z`-degree two, avoid
the owner-adjacent point of `W`, and are forced through its unique other
point, making a four-cycle.  FullType bounds the local exceptional points on
`S` by two, so the three-point local exceptional set splits exactly `2+1`. -/
theorem orderNine_order34_three_edge_owner_W_one_exceptional_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 3)
    (S Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hTotalDefectS :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card = 2)
    (hZdegree : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset y ∩ Z).card = if y ∈ S then 1 else 2) :
    ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
      (secondOrderDefectGraph G).neighborFinset owner) ∩ S).card = 2 := by
  classical
  let E := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
    (secondOrderDefectGraph G).neighborFinset owner
  let F := (secondOrderDefectGraph G).neighborFinset owner ∩
    squareOrderNineLowIncidenceBin G 0
  have heq :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hEcard : E.card = 3 := by
    have hEtf : E = triangleFreeNeighbors G owner := by simpa [E] using heq
    rw [hEtf]
    rcases hprofile with hthree | hfour
    · exact hthree.2.1
    · omega
  have hOutsideLe : (E \ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    by_contra hyz
    have hyParts := Finset.mem_sdiff.mp hy
    have hzParts := Finset.mem_sdiff.mp hz
    have hyEParts := Finset.mem_inter.mp hyParts.1
    have hzEParts := Finset.mem_inter.mp hzParts.1
    have hyU := Finset.mem_inter.mp hyEParts.1
    have hzU := Finset.mem_inter.mp hzEParts.1
    have hyZtwo : (G.neighborFinset y ∩ Z).card = 2 := by
      simpa [hyParts.2] using hZdegree y (by simpa [E] using hyParts.1)
    have hzZtwo : (G.neighborFinset z ∩ Z).card = 2 := by
      simpa [hzParts.2] using hZdegree z (by simpa [E] using hzParts.1)
    have hyAvoid : (G.neighborFinset y ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have hwParts := Finset.mem_inter.mp hw
      have hwOwner := (Finset.mem_inter.mp hwParts.2).1
      exact (orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
          (by simpa [E] using hyParts.1)
          ((G.mem_neighborFinset owner w).mp hwOwner))
            ((G.mem_neighborFinset y w).mp hwParts.1)
    have hzAvoid : (G.neighborFinset z ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have hwParts := Finset.mem_inter.mp hw
      have hwOwner := (Finset.mem_inter.mp hwParts.2).1
      exact (orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
          (by simpa [E] using hzParts.1)
          ((G.mem_neighborFinset owner w).mp hwOwner))
            ((G.mem_neighborFinset z w).mp hwParts.1)
    exact false_of_orderNine_order34_two_binZero_neighbors_avoid_owner_W
      G hfree hhigh owner y z howner hyU.2 hzU.2 hyz
        ((G.adj_comm owner y).mp ((G.mem_neighborFinset owner y).mp hyU.1))
        ((G.adj_comm owner z).mp ((G.mem_neighborFinset owner z).mp hzU.1))
        Z P W hpartition hPsub hWcard hownerW
        hyZtwo hzZtwo hyAvoid hzAvoid
  have hESubF : E ∩ S ⊆ F ∩ S := by
    intro y hy
    have hyParts := Finset.mem_inter.mp hy
    have hyEParts := Finset.mem_inter.mp hyParts.1
    have hyU := Finset.mem_inter.mp hyEParts.1
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_inter.mpr ⟨hyEParts.2, hyU.2⟩, hyParts.2⟩
  have hInsideLe := Finset.card_le_card hESubF
  change (F ∩ S).card = 2 at hTotalDefectS
  have hsplit := Finset.card_inter_add_card_sdiff E S
  have hInside : (E ∩ S).card = 2 := by
    rw [hTotalDefectS] at hInsideLe
    rw [hEcard] at hsplit
    omega
  simpa [E] using hInside

/-- Corrected three-edge `(3,1)` partner terminal.  If the two local
exceptional points on `S` account for two of the owner's three ordinary
shore-neighbors, exactly one of the three bin-one partners lies on `S` and
two lie on `T`.  Equation (25) gives both off-shore partners `W`-degree one,
contradicting the at-most-one partner bound (27). -/
theorem false_of_orderNine_order34_three_edge_owner_W_one_partner_split
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
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S T W : Finset V)
    (hdisjST : Disjoint S T)
    (hownerS : (G.neighborFinset owner ∩ S).card = 3)
    (hExceptionalS :
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner) ∩ S).card = 2)
    (hownerSPartition : G.neighborFinset owner ∩ S =
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner) ∩ S) ∪
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ S))
    (hpartnersSub : G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1 ⊆ S ∪ T)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hpartnerWdegree : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      (G.neighborFinset z ∩ W).card = 1) : False := by
  classical
  let E := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
    (secondOrderDefectGraph G).neighborFinset owner
  let K := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hcensus
  have hKcard : K.card = 3 := by simpa [K] using hcensus.2.1
  have hEKdisj : Disjoint E K := by
    rw [Finset.disjoint_left]
    intro z hzE hzK
    have hzEParts := Finset.mem_inter.mp hzE
    have hzU := Finset.mem_inter.mp hzEParts.1
    have hzKParts := Finset.mem_inter.mp hzK
    have hk0 := (Finset.mem_filter.mp hzU.2).2
    have hk1 := (Finset.mem_filter.mp hzKParts.2).2
    omega
  have hshoreDisj : Disjoint (E ∩ S) (K ∩ S) :=
    hEKdisj.mono Finset.inter_subset_left Finset.inter_subset_left
  have hKScard : (K ∩ S).card = 1 := by
    have hcards := Finset.card_union_of_disjoint hshoreDisj
    rw [← hownerSPartition] at hcards
    change (E ∩ S).card = 2 at hExceptionalS
    rw [hownerS, hExceptionalS] at hcards
    omega
  have hKpartition : (K ∩ S) ∪ (K ∩ T) = K := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_inter.mp hz).1
      · exact (Finset.mem_inter.mp hz).1
    · intro hz
      have hzUnion := hpartnersSub hz
      rcases Finset.mem_union.mp hzUnion with hzS | hzT
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzS⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, hzT⟩)
  have hKTdisj : Disjoint (K ∩ S) (K ∩ T) :=
    hdisjST.mono Finset.inter_subset_right Finset.inter_subset_right
  have hKTcard : (K ∩ T).card = 2 := by
    have hcards := Finset.card_union_of_disjoint hKTdisj
    rw [hKpartition, hKcard, hKScard] at hcards
    omega
  have hle := orderNine_secondProfile_owner_partners_W_degree_one_card_le_one
    G hfree hhigh owner howner W (K ∩ T)
      hWsub hWcard hownerW
      (by
        intro z hz
        exact (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2)
      (by
        intro z hz
        exact (G.mem_neighborFinset owner z).mp
          (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1 |>.symm)
      hpartnerWdegree
  rw [hKTcard] at hle
  omega

/-- End-to-end corrected three-edge `(3,1)` assembly.  On an ordinary shore,
the owner's original neighbors split exactly into the three exceptional
bin-zero points and the three bin-one partners.  The punctured `1/2` degree
formula and FullType first force the exceptional `2+1` shore split; the
owner's `3+3` ordinary-neighbor split then forces two partners off `S`, and
equation (25) contradicts the partner bound. -/
theorem false_of_orderNine_order34_three_edge_owner_W_one_punctured
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 3)
    (S T Z P W : Finset V)
    (hSsub : S ⊆ (Finset.univ : Finset V) \
      squareOrderHighVertices G 9)
    (hdisjST : Disjoint S T)
    (hownerS : (G.neighborFinset owner ∩ S).card = 3)
    (hpartnersSub : G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1 ⊆ S ∪ T)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hTotalDefectS :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card = 2)
    (hZdegree : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset y ∩ Z).card = if y ∈ S then 1 else 2)
    (hpartnerWdegree : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      (G.neighborFinset z ∩ W).card = 1) : False := by
  classical
  let A := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
  let E := A ∩ (secondOrderDefectGraph G).neighborFinset owner
  let K := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hcensus
  have hAcard : A.card = 3 := by simpa [A] using hcensus.2.2
  have heq :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  have hEcard : E.card = 3 := by
    have hEtf : E = triangleFreeNeighbors G owner := by
      simpa [E, A] using heq
    rw [hEtf]
    rcases hprofile with hthree | hfour
    · exact hthree.2.1
    · omega
  have hEA : E = A := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_left
    · rw [hEcard, hAcard]
  have hExceptionalS :=
    orderNine_order34_three_edge_owner_W_one_exceptional_split
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hloc
        S Z P W hpartition hPsub hWcard hownerW hTotalDefectS hZdegree
  have hownerSPartition : G.neighborFinset owner ∩ S =
      (E ∩ S) ∪ (K ∩ S) := by
    ext y
    constructor
    · intro hy
      have hyParts := Finset.mem_inter.mp hy
      have hyOrd := hSsub hyParts.2
      have hne : y ≠ owner := by
        intro h
        subst y
        exact G.loopless.irrefl owner
          ((G.mem_neighborFinset owner owner).mp hyParts.1)
      have hle := orderNine_secondProfile_nonowner_ordinary_highIncidence_le_one
        G hp hhigh hc2 hc3 owner y howner hyOrd hne
      have hk : squareOrderHighIncidenceCount G 9 y = 0 ∨
          squareOrderHighIncidenceCount G 9 y = 1 := by omega
      rcases hk with hk | hk
      · have hyA : y ∈ A := Finset.mem_inter.mpr ⟨hyParts.1,
          Finset.mem_filter.mpr ⟨hyOrd, hk⟩⟩
        exact Finset.mem_union_left _ (Finset.mem_inter.mpr
          ⟨by rw [hEA]; exact hyA, hyParts.2⟩)
      · have hyK : y ∈ K := Finset.mem_inter.mpr ⟨hyParts.1,
          Finset.mem_filter.mpr ⟨hyOrd, hk⟩⟩
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr
          ⟨hyK, hyParts.2⟩)
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · have hyParts := Finset.mem_inter.mp hy
        have hyE := Finset.mem_inter.mp hyParts.1
        have hyA := Finset.mem_inter.mp hyE.1
        exact Finset.mem_inter.mpr ⟨hyA.1, hyParts.2⟩
      · have hyParts := Finset.mem_inter.mp hy
        have hyK := Finset.mem_inter.mp hyParts.1
        exact Finset.mem_inter.mpr ⟨hyK.1, hyParts.2⟩
  exact false_of_orderNine_order34_three_edge_owner_W_one_partner_split
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner S T W
      hdisjST hownerS (by simpa [E, A] using hExceptionalS)
      (by simpa [E, A, K] using hownerSPartition)
      (by simpa [K] using hpartnersSub) hWsub hWcard hownerW
      (by simpa [K] using hpartnerWdegree)

/-- Corrected four-edge `(3,1)` placement reduction.  Write `E` for the
unique exceptional bin-zero owner-neighbor and `R` for the two regular
bin-zero owner-neighbors.  If the owner has a unique neighbor in `W`, that
neighbor must be regular, and the exceptional point must lie on the small
shore.  Thus the old four-edge contradiction reduces honestly to one
residual placement instead of using the false uniform degree-two assertion
at the exceptional point. -/
theorem orderNine_order34_four_edge_owner_W_one_residual_placement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 4)
    (S Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hExceptionalDegree : ∀ e ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset e ∩ Z).card = if e ∈ S then 1 else 2)
    (hRegularDegree : ∀ r ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) \
        (secondOrderDefectGraph G).neighborFinset owner,
      (G.neighborFinset r ∩ Z).card = 2) :
    let U := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
    let E := U ∩ (secondOrderDefectGraph G).neighborFinset owner
    let R := U \ (secondOrderDefectGraph G).neighborFinset owner
    ∀ s, G.neighborFinset owner ∩ W = {s} →
      s ∈ R ∧ ∀ e ∈ E, e ∈ S := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let U := G.neighborFinset owner ∩ B 0
  let E := U ∩ D.neighborFinset owner
  let R := U \ D.neighborFinset owner
  have hgeom := orderNine_secondProfile_owner_four_edge_binZero_partition
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hloc
  dsimp only at hgeom
  have hEcard : E.card = 1 := by simpa [E, U, B, D] using hgeom.1
  have hRcard : R.card = 2 := by simpa [R, U, B, D] using hgeom.2.1
  have hER : ∀ e ∈ E, ∀ r ∈ R, ¬ G.Adj e r := by
    simpa [E, R, U, B, D] using hgeom.2.2.1
  intro s hOeq
  have hsO : s ∈ G.neighborFinset owner ∩ W := by rw [hOeq]; simp
  have hsOParts := Finset.mem_inter.mp hsO
  have hsU : s ∈ U := Finset.mem_inter.mpr ⟨hsOParts.1, hWsub hsOParts.2⟩
  have hsNotE : s ∉ E := by
    intro hsE
    obtain ⟨r, hr, t, ht, hrt⟩ := Finset.one_lt_card.mp
      (by rw [hRcard]; omega : 1 < R.card)
    have hrParts := Finset.mem_sdiff.mp hr
    have htParts := Finset.mem_sdiff.mp ht
    have hrU := Finset.mem_inter.mp hrParts.1
    have htU := Finset.mem_inter.mp htParts.1
    have hrAvoid : (G.neighborFinset r ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      rw [hOeq]
      simp [G.adj_comm, hER s hsE r hr]
    have htAvoid : (G.neighborFinset t ∩
        (G.neighborFinset owner ∩ W)).card = 0 := by
      rw [hOeq]
      simp [G.adj_comm, hER s hsE t ht]
    exact false_of_orderNine_order34_two_binZero_neighbors_avoid_owner_W
      G hfree hhigh owner r t howner hrU.2 htU.2 hrt
        ((G.adj_comm owner r).mp ((G.mem_neighborFinset owner r).mp hrU.1))
        ((G.adj_comm owner t).mp ((G.mem_neighborFinset owner t).mp htU.1))
        Z P W hpartition hPsub hWcard hownerW
        (hRegularDegree r (by simpa [R, U, B, D] using hr))
        (hRegularDegree t (by simpa [R, U, B, D] using ht))
        hrAvoid htAvoid
  have hsNotD : s ∉ D.neighborFinset owner := by
    intro hsD
    exact hsNotE (Finset.mem_inter.mpr ⟨hsU, hsD⟩)
  have hsR : s ∈ R := Finset.mem_sdiff.mpr ⟨hsU, hsNotD⟩
  refine ⟨by simpa [R, U, B, D] using hsR, ?_⟩
  intro e he
  by_contra heS
  have heParts := Finset.mem_inter.mp he
  have heU := Finset.mem_inter.mp heParts.1
  have hse : s ≠ e := by
    intro h
    subst e
    exact hsNotE he
  have hsAvoid : (G.neighborFinset s ∩
      (G.neighborFinset owner ∩ W)).card = 0 := by
    rw [hOeq]
    simp
  have heAvoid : (G.neighborFinset e ∩
      (G.neighborFinset owner ∩ W)).card = 0 := by
    rw [hOeq]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hwParts := Finset.mem_inter.mp hw
    have hws : w = s := Finset.mem_singleton.mp hwParts.2
    subst w
    exact (hER e he s hsR) ((G.mem_neighborFinset e s).mp hwParts.1)
  exact false_of_orderNine_order34_two_binZero_neighbors_avoid_owner_W
    G hfree hhigh owner s e howner
      (Finset.mem_inter.mp hsU).2 heU.2 hse
      ((G.adj_comm owner s).mp
        ((G.mem_neighborFinset owner s).mp (Finset.mem_inter.mp hsU).1))
      ((G.adj_comm owner e).mp ((G.mem_neighborFinset owner e).mp heU.1))
      Z P W hpartition hPsub hWcard hownerW
      (hRegularDegree s (by simpa [R, U, B, D] using hsR))
      (by simpa [heS] using hExceptionalDegree e (by simpa [E, U, B, D] using he))
      hsAvoid heAvoid

/-- Partner-count consequence of the four-edge residual.  Once its unique
exceptional owner-neighbor lies on `S`, equation (27) forces exactly two of
the three bin-one partners onto `S` and exactly one onto `T`; consequently
the exceptional point is the owner's only bin-zero neighbor on `S`. -/
theorem orderNine_order34_four_edge_owner_W_one_partner_shore_cards
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
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S T W : Finset V)
    (hdisjST : Disjoint S T)
    (hownerS : (G.neighborFinset owner ∩ S).card = 3)
    (hExceptionalS :
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner) ∩ S).card = 1)
    (hownerSPartition : G.neighborFinset owner ∩ S =
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) ∩ S) ∪
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ S))
    (hpartnersSub : G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1 ⊆ S ∪ T)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1)
    (hpartnerWdegree : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      (G.neighborFinset z ∩ W).card = 1) :
    let A := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
    let K := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1
    (A ∩ S).card = 1 ∧ (K ∩ S).card = 2 ∧ (K ∩ T).card = 1 := by
  classical
  dsimp only
  let A := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
  let E := A ∩ (secondOrderDefectGraph G).neighborFinset owner
  let K := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hcensus
  have hKcard : K.card = 3 := by simpa [K] using hcensus.2.1
  have hAKdisj : Disjoint A K := by
    rw [Finset.disjoint_left]
    intro z hzA hzK
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzA).2).2
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzK).2).2
    omega
  have hshoreDisj : Disjoint (A ∩ S) (K ∩ S) :=
    hAKdisj.mono Finset.inter_subset_left Finset.inter_subset_left
  have hKpartition : (K ∩ S) ∪ (K ∩ T) = K := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_inter.mp hz).1
      · exact (Finset.mem_inter.mp hz).1
    · intro hz
      rcases Finset.mem_union.mp (hpartnersSub hz) with hzS | hzT
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzS⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, hzT⟩)
  have hKTdisj : Disjoint (K ∩ S) (K ∩ T) :=
    hdisjST.mono Finset.inter_subset_right Finset.inter_subset_right
  have hKTle : (K ∩ T).card ≤ 1 :=
    orderNine_secondProfile_owner_partners_W_degree_one_card_le_one
      G hfree hhigh owner howner W (K ∩ T) hWsub hWcard hownerW
        (fun z hz ↦ (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2)
        (fun z hz ↦ ((G.mem_neighborFinset owner z).mp
          (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1).symm)
        hpartnerWdegree
  have hsumK : (K ∩ S).card + (K ∩ T).card = 3 := by
    have hcards := Finset.card_union_of_disjoint hKTdisj
    rw [hKpartition, hKcard] at hcards
    exact hcards.symm
  have hASpos : 1 ≤ (A ∩ S).card := by
    have hsub : E ∩ S ⊆ A ∩ S :=
      Finset.inter_subset_inter Finset.inter_subset_left (fun _ h ↦ h)
    have hle := Finset.card_le_card hsub
    change (E ∩ S).card = 1 at hExceptionalS
    omega
  have hsumOwner : (A ∩ S).card + (K ∩ S).card = 3 := by
    have hcards := Finset.card_union_of_disjoint hshoreDisj
    rw [← hownerSPartition, hownerS] at hcards
    exact hcards.symm
  have hcards : (A ∩ S).card = 1 ∧ (K ∩ S).card = 2 ∧
      (K ∩ T).card = 1 := by omega
  simpa [A, K] using hcards

/-- Actual owner-punctured provider for the corrected exceptional-point
`Z`-degree function.  The articulation universe omits `owner` but contains
every local exceptional point; its defect neighborhoods are closed after
allowing the single deleted owner.  Consequently equation (23) gives degree
one on `S` and degree two on `T`. -/
theorem orderNine_order34_exceptional_owner_neighbors_lowSet_degree_eq_if_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ owner : V)
    (U S T : Finset V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighbors : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner), y ∈ U)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (Z : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3) :
    ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset y ∩ Z).card = if y ∈ S then 1 else 2 := by
  classical
  intro y hy
  let D := secondOrderDefectGraph G
  have hyParts := Finset.mem_inter.mp hy
  have hyUParts := Finset.mem_inter.mp hyParts.1
  have hyDadj : D.Adj y owner := by
    have : D.Adj owner y :=
      (D.mem_neighborFinset owner y).mp hyParts.2
    exact (D.adj_comm owner y).mp this
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hyUParts.2
  have hyDegree : D.degree y = 8 := by
    simpa [D] using hledger.1
  have hdefect :=
    neighbor_inter_shore_card_eq_if_of_complementary_closed_punctured_owner
      D owner U S T y hownerNotU hunion hdisj (hlocalU y hy)
        hyDadj hneighbors hSclosed hTclosed hyDegree
  have hlow := orderNine_order34_exceptional_binZero_lowSet_degree_eq_if
    G hfree h₁ h₂ h₃ y S hScard hpart hhigh₁ hhigh₂ hhigh₃
      hSH hdegOrd hdegHigh (hlocalOrd y hy) hdefect
  rw [← hZ] at hlow
  exact hlow

/-- The complementary provider for regular bin-zero owner-neighbors.  Such
a point is not defect-adjacent to the deleted owner, so owner-punctured
closure sharpens to genuine closure in `U`; equation (23) therefore gives
low-set degree two on either shore. -/
theorem orderNine_order34_regular_owner_neighbors_lowSet_degree_two_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ owner : V)
    (U S T : Finset V)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0), y ∈ U)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0),
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (Z : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3) :
    ∀ y ∈ (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset owner,
      (G.neighborFinset y ∩ Z).card = 2 := by
  classical
  intro y hy
  have hyParts := Finset.mem_sdiff.mp hy
  have hyLocal := Finset.mem_inter.mp hyParts.1
  have hyClosed : (secondOrderDefectGraph G).neighborFinset y ⊆ U := by
    intro z hz
    rcases Finset.mem_insert.mp
        (hneighborsPunctured y (hlocalU y hyParts.1) hz) with hzo | hzU
    · subst z
      have hAdj : (secondOrderDefectGraph G).Adj y owner :=
        ((secondOrderDefectGraph G).mem_neighborFinset y owner).mp hz
      have hAdj' : (secondOrderDefectGraph G).Adj owner y :=
        ((secondOrderDefectGraph G).adj_comm y owner).mp hAdj
      exact (hyParts.2
        (((secondOrderDefectGraph G).mem_neighborFinset owner y).mpr hAdj')).elim
    · exact hzU
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hyLocal.2
  have hyDegree : (secondOrderDefectGraph G).degree y = 8 := by
    simpa using hledger.1
  have hdefect := neighbor_inter_shore_card_eq_if_of_complementary_closed
    (secondOrderDefectGraph G) U S T y hunion hdisj
      (hlocalU y hyParts.1) hyClosed hSclosed hTclosed hyDegree
  have hlow := orderNine_order34_binZero_lowSet_degree_eq_two_of_defect_shore
    G hfree h₁ h₂ h₃ y S hScard hpart hhigh₁ hhigh₂ hhigh₃
      hSH hdegOrd hdegHigh (hlocalOrd y hyParts.1) hdefect
  rw [← hZ] at hlow
  exact hlow

/-- Directly instantiable punctured-shore form of the corrected four-edge
`(3,1)` reduction.  It derives both exceptional and regular bin-zero degree
laws internally, leaving precisely the honest residual placement. -/
theorem orderNine_order34_four_edge_owner_W_one_residual_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 4)
    (U S T : Finset V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0), y ∈ U)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0),
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (Z P W : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1) :
    let A := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
    let E := A ∩ (secondOrderDefectGraph G).neighborFinset owner
    let R := A \ (secondOrderDefectGraph G).neighborFinset owner
    ∀ s, G.neighborFinset owner ∩ W = {s} →
      s ∈ R ∧ ∀ e ∈ E, e ∈ S := by
  have hExceptionalDegree :=
    orderNine_order34_exceptional_owner_neighbors_lowSet_degree_eq_if_of_punctured_shores
      G hfree hmin hcover hcard h₁ h₂ h₃ owner U S T
        hownerNotU hunion hdisj hneighborsPunctured hSclosed hTclosed
        (fun y hy ↦ hlocalU y (Finset.mem_inter.mp hy).1)
        hScard hpart hhigh₁ hhigh₂ hhigh₃ hSH hdegOrd hdegHigh
        (fun y hy ↦ hlocalOrd y (Finset.mem_inter.mp hy).1) Z hZ
  have hRegularDegree :=
    orderNine_order34_regular_owner_neighbors_lowSet_degree_two_of_punctured_shores
      G hfree hmin hcover hcard h₁ h₂ h₃ owner U S T
        hunion hdisj hneighborsPunctured hSclosed hTclosed hlocalU
        hScard hpart hhigh₁ hhigh₂ hhigh₃ hSH hdegOrd hdegHigh
        hlocalOrd Z hZ
  exact orderNine_order34_four_edge_owner_W_one_residual_placement
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hloc
      S Z P W hpartition hPsub hWsub hWcard hownerW
      hExceptionalDegree hRegularDegree

/-- Pointwise, satisfiable equation-(25) provider for off-shore bin-one
partners.  Unlike the earlier global-closure wrapper, this assumes defect
closure only for the partner currently being evaluated; exceptional
bin-zero points elsewhere in the punctured universe create no vacuous
obligation. -/
theorem orderNine_order34_owner_partners_offshore_W_degree_one_of_pointwise_closure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (U S T : Finset V)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hpartnerU : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      z ∈ U)
    (hpartnerDclosed : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      (secondOrderDefectGraph G).neighborFinset z ⊆ U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hpartnerOrd : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      z ∉ ({h₁, h₂, h₃} : Finset V))
    (Z P W : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0) :
    ∀ z ∈ ((G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1) ∩ T),
      (G.neighborFinset z ∩ W).card = 1 := by
  classical
  intro z hz
  have hzParts := Finset.mem_inter.mp hz
  have hzPartner := Finset.mem_inter.mp hzParts.1
  have hzNotS : z ∉ S := by
    intro hzS
    exact (Finset.disjoint_left.mp hdisj) hzS hzParts.2
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hzPartner.2
  have hzDegree : (secondOrderDefectGraph G).degree z = 7 := by
    simpa using hledger.1
  have hdefect := neighbor_inter_shore_card_eq_if_of_complementary_closed
    (secondOrderDefectGraph G) U S T z hunion hdisj (hpartnerU z hz)
      (hpartnerDclosed z hz) hSclosed hTclosed hzDegree
  have hlow := orderNine_order34_lowSet_degree_of_defect_shore
    G hfree h₁ h₂ h₃ z S hScard hpart hhigh₁ hhigh₂ hhigh₃
      hSH hdegOrd hdegHigh (hpartnerOrd z hz) hdefect
  rw [← hZ] at hlow
  have hPzero :=
    orderNine_secondProfile_owner_partner_neighbor_inter_binOneSubset_eq_zero
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 owner z howner
        hzPartner.2
        ((G.adj_comm owner z).mp
          ((G.mem_neighborFinset owner z).mp hzPartner.1))
        P hPsub
  have hownerW : owner ∉ W := by
    intro how
    have hownerB₀ := hWsub how
    have hk3 := (Finset.mem_filter.mp howner).2
    have hk0 := (Finset.mem_filter.mp hownerB₀).2
    omega
  have hWdegree := owner_partner_W_degree_of_lowSet_partition
    G owner z S Z P W hpartition hownerW
      ((G.adj_comm owner z).mp
        ((G.mem_neighborFinset owner z).mp hzPartner.1))
      hPzero hlow
  simpa [hzNotS] using hWdegree

/-- Satisfiable corrected master for the three-edge `(3,1)` branch.  It
instantiates FullType, the owner-punctured exceptional-degree provider, and
the pointwise partner equation-(25) provider before invoking the corrected
three-edge assembly.  No full-neighborhood closure is required for the
exceptional points in the owner-deleted universe. -/
theorem false_of_orderNine_order34_three_edge_owner_W_one_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 3)
    (U S T : Finset V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hSsub : S ⊆ (Finset.univ : Finset V) \
      squareOrderHighVertices G 9)
    (hownerS : (G.neighborFinset owner ∩ S).card = 3)
    (hpartnersSub : G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1 ⊆ S ∪ T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner), y ∈ U)
    (hpartnerU : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      z ∈ U)
    (hpartnerDclosed : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      (secondOrderDefectGraph G).neighborFinset z ⊆ U)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (hpartnerOrd : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      z ∉ ({h₁, h₂, h₃} : Finset V))
    (hfull : orderNineArticulationSmallShoreFullType G
      ((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S)
    (Z P W : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 1) : False := by
  have hTotalDefectS :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card = 2 :=
    hfull.2.2.2 hScard
  have hZdegree :=
    orderNine_order34_exceptional_owner_neighbors_lowSet_degree_eq_if_of_punctured_shores
      G hfree hmin hcover hcard h₁ h₂ h₃ owner U S T
        hownerNotU hunion hdisj hneighborsPunctured hSclosed hTclosed
        hlocalU hScard hpart hhigh₁ hhigh₂ hhigh₃ hSH
        hdegOrd hdegHigh hlocalOrd Z hZ
  have hpartnerWdegree :=
    orderNine_order34_owner_partners_offshore_W_degree_one_of_pointwise_closure
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ owner howner U S T hScard hpart
        hhigh₁ hhigh₂ hhigh₃ hSH hdegOrd hdegHigh
        hunion hdisj hpartnerU hpartnerDclosed hSclosed hTclosed
        hpartnerOrd Z P W hZ hpartition hPsub hWsub
  exact false_of_orderNine_order34_three_edge_owner_W_one_punctured
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hloc
      S T Z P W hSsub hdisj hownerS hpartnersSub
      hpartition hPsub hWsub hWcard hownerW hTotalDefectS
      hZdegree hpartnerWdegree

/-- Satisfiable corrected master for the three-edge `(2,2)` branch.  It
instantiates FullType and the owner-punctured exceptional-degree provider,
then invokes the corrected three-edge owner-W-two contradiction. -/
theorem false_of_orderNine_order34_three_edge_owner_W_two_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 3)
    (U S T : Finset V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner), y ∈ U)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (hfull : orderNineArticulationSmallShoreFullType G
      ((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S)
    (Z P W : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 2) : False := by
  have hTotalDefectS :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card = 2 :=
    hfull.2.2.2 hScard
  have hZdegree :=
    orderNine_order34_exceptional_owner_neighbors_lowSet_degree_eq_if_of_punctured_shores
      G hfree hmin hcover hcard h₁ h₂ h₃ owner U S T
        hownerNotU hunion hdisj hneighborsPunctured hSclosed hTclosed
        hlocalU hScard hpart hhigh₁ hhigh₂ hhigh₃ hSH
        hdegOrd hdegHigh hlocalOrd Z hZ
  exact false_of_orderNine_order34_three_edge_owner_W_two_punctured
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hloc
      S Z P W hpartition hPsub hWcard hownerW hTotalDefectS hZdegree

/-- An owner-adjacent bin-one partner is not defect-adjacent to the owner.
The partner has a high neighbor, and the universal bin-three owner is
adjacent to every high vertex, so that high root is a common original
neighbor of the pair. -/
theorem orderNine_secondProfile_owner_partner_not_defectAdjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    {owner z : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hzB₁ : z ∈ squareOrderNineLowIncidenceBin G 1) :
    ¬ (secondOrderDefectGraph G).Adj z owner := by
  classical
  let H := squareOrderHighVertices G 9
  have hzCard : (G.neighborFinset z ∩ H).card = 1 :=
    (Finset.mem_filter.mp hzB₁).2
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by rw [hzCard]; omega)
  have hrParts := Finset.mem_inter.mp hr
  have hownerAll : G.neighborFinset owner ∩ H = H := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · have hownerCard : (G.neighborFinset owner ∩ H).card = 3 :=
        (Finset.mem_filter.mp howner).2
      rw [hownerCard, hhigh]
  have hrOwner : G.Adj owner r := by
    have : r ∈ G.neighborFinset owner ∩ H := by
      rw [hownerAll]
      exact hrParts.2
    exact (G.mem_neighborFinset owner r).mp (Finset.mem_inter.mp this).1
  have hzOwner : z ≠ owner := by
    intro h
    subst z
    have hk3 := (Finset.mem_filter.mp howner).2
    have hk1 := (Finset.mem_filter.mp hzB₁).2
    omega
  exact not_secondOrderDefect_adj_of_commonNeighbor
    G hfree hzOwner
      ((G.mem_neighborFinset z r).mp hrParts.1) hrOwner

/-- Removing the sole deleted owner from a partner's punctured defect
closure.  The preceding theorem rules out the owner itself as a defect
neighbor, so containment in `{owner} ∪ U` sharpens to containment in `U`. -/
theorem orderNine_secondProfile_owner_partner_defectNeighbors_subset_punctured
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    {owner z : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hzB₁ : z ∈ squareOrderNineLowIncidenceBin G 1)
    (U : Finset V)
    (hpunctured : (secondOrderDefectGraph G).neighborFinset z ⊆
      insert owner U) :
    (secondOrderDefectGraph G).neighborFinset z ⊆ U := by
  intro y hy
  rcases Finset.mem_insert.mp (hpunctured hy) with h | h
  · subst y
    have hAdj : (secondOrderDefectGraph G).Adj z owner :=
      ((secondOrderDefectGraph G).mem_neighborFinset z owner).mp hy
    exact (orderNine_secondProfile_owner_partner_not_defectAdjacent
      G hfree hhigh howner hzB₁ hAdj).elim
  · exact h

/-- Family form used to discharge the corrected three-edge master's
pointwise partner-closure hypothesis directly from the articulation's
owner-punctured closure. -/
theorem orderNine_secondProfile_owner_partners_defectNeighbors_subset_of_punctured_closure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (U T : Finset V)
    (hpartnerU : ∀ z ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1) ∩ T),
      z ∈ U)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U) :
    ∀ z ∈ ((G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1) ∩ T),
      (secondOrderDefectGraph G).neighborFinset z ⊆ U := by
  intro z hz
  have hzB₁ := (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2
  exact orderNine_secondProfile_owner_partner_defectNeighbors_subset_punctured
    G hfree hhigh howner hzB₁ U
      (hneighborsPunctured z (hpartnerU z hz))

end

end Erdos85

#print axioms Erdos85.orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
