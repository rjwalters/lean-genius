import Proofs.Erdos85DegreeSixBoundaryPackage
import Proofs.Erdos85EvenExcessOneDefectKernel
import Proofs.Erdos85BoundedReplacementObstruction
import Proofs.Erdos85EvenExcessOneThirdMoment

/-!
# The degree-six excess-one plateau kernel

The order-34 residue of the degree-six plateau band feeds directly into the
mod-two defect-kernel theorem.  This file exports that consequence without
requiring later assembly code to unpack `PositiveExcessPlateauData`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Decode the mod-two defect-set equation when the set has even order. -/
theorem oddDefectSet_neighborParity_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    (∀ v ∈ W, Odd (D.neighborFinset v ∩ W).card) ∧
      (∀ v ∉ W, Even (D.neighborFinset v ∩ W).card) := by
  have hWcast : (W.card : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hW
  constructor
  · intro v hv
    have h := hparity v
    rw [if_pos hv, hWcast] at h
    have hone : (((D.neighborFinset v ∩ W).card : ZMod 2)) = 1 := by
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination h - htwo
    exact ZMod.natCast_eq_one_iff_odd.mp hone
  · intro v hv
    have h := hparity v
    rw [if_neg hv, hWcast] at h
    exact ZMod.natCast_eq_zero_iff_even.mp (by simpa using h)

/-- Decode the mod-two defect-set equation when the set has odd order. -/
theorem oddDefectSet_neighborParity_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    (∀ v ∈ W, Even (D.neighborFinset v ∩ W).card) ∧
      (∀ v ∉ W, Odd (D.neighborFinset v ∩ W).card) := by
  have hWcast : (W.card : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr hW
  constructor
  · intro v hv
    have h := hparity v
    rw [if_pos hv, hWcast] at h
    apply ZMod.natCast_eq_zero_iff_even.mp
    have htwo : (2 : ZMod 2) = 0 := by decide
    linear_combination h - htwo
  · intro v hv
    have h := hparity v
    rw [if_neg hv, hWcast] at h
    have hone : (((D.neighborFinset v ∩ W).card : ZMod 2)) = 1 := by
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination h - htwo
    exact ZMod.natCast_eq_one_iff_odd.mp hone

/-- If an odd defect set has odd cardinality, every vertex outside it has a
defect neighbor inside it. -/
theorem oddDefectSet_dominates_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∉ W, ∃ w ∈ W, D.Adj v w := by
  have hout := (oddDefectSet_neighborParity_of_odd D W hW hparity).2
  intro v hv
  have hpos : 0 < (D.neighborFinset v ∩ W).card :=
    (hout v hv).pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, (Finset.mem_inter.mp hw).2,
    (D.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1⟩

/-- If an odd defect set has even cardinality, every vertex inside it has a
defect neighbor inside it. -/
theorem oddDefectSet_no_isolated_inside_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∈ W, ∃ w ∈ W, D.Adj v w := by
  have hin := (oddDefectSet_neighborParity_of_even D W hW hparity).1
  intro v hv
  have hpos : 0 < (D.neighborFinset v ∩ W).card :=
    (hin v hv).pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, (Finset.mem_inter.mp hw).2,
    (D.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1⟩

/-- In a cubic graph on 34 vertices, an odd-cardinality defect set satisfying
the kernel law has at least nine vertices.  Every outside vertex contributes
at least one cut incidence, while the set supplies at most three per vertex. -/
theorem oddDefectSet_nine_le_card_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    9 ≤ W.card := by
  have hdom := oddDefectSet_dominates_of_odd D W hW hparity
  have hpoint : ∀ v : {v : V // v ∉ W},
      1 ≤ (D.neighborFinset v.1 ∩ W).card := by
    intro v
    obtain ⟨w, hwW, hvw⟩ := hdom v.1 v.2
    exact Finset.one_le_card.mpr ⟨w, Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v.1 w).mpr hvw, hwW⟩⟩
  have hlower : Fintype.card {v : V // v ∉ W} ≤
      ∑ v : {v : V // v ∉ W}, (D.neighborFinset v.1 ∩ W).card := by
    have hsum := Finset.sum_le_sum (s :=
      (Finset.univ : Finset {v : V // v ∉ W})) fun v _hv => hpoint v
    simpa using hsum
  have hupper := sum_card_neighbor_inter_deleted_le_sum_degrees D W
  have hrhs : (∑ x ∈ W, D.degree x) = W.card * 3 := by
    simp [hreg]
  have hcut : Fintype.card {v : V // v ∉ W} ≤ W.card * 3 := by
    rw [← hrhs]
    exact hlower.trans hupper
  have hinside : Fintype.card {v : V // v ∈ W} = W.card := by
    simpa using Fintype.card_coe W
  have houtside : Fintype.card {v : V // v ∉ W} = 34 - W.card := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ W), hcard, hinside]
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  rw [houtside] at hcut
  omega

/-- In the odd-cardinality branch of a cubic defect graph, every vertex of
the defect set also has a neighbor outside it. -/
theorem oddDefectSet_complement_dominates_inside_of_odd_of_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hreg : ∀ v, D.degree v = 3) (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∈ W, ∃ w ∉ W, D.Adj v w := by
  have hin := (oddDefectSet_neighborParity_of_odd D W hW hparity).1
  intro v hv
  by_contra hnone
  push Not at hnone
  have hsubset : D.neighborFinset v ⊆ W := by
    intro w hw
    by_contra hwW
    exact hnone w hwW ((D.mem_neighborFinset v w).mp hw)
  have hinter : D.neighborFinset v ∩ W = D.neighborFinset v :=
    Finset.inter_eq_left.mpr hsubset
  have hthree : (D.neighborFinset v ∩ W).card = 3 := by
    rw [hinter, D.card_neighborFinset_eq_degree, hreg v]
  have heven := hin v hv
  rw [hthree] at heven
  norm_num at heven

/-- The symmetric cubic cut count bounds an odd-cardinality defect set on 34
vertices from above by 25. -/
theorem oddDefectSet_card_le_twentyFive_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    W.card ≤ 25 := by
  let S : Finset V := Wᶜ
  have hdom := oddDefectSet_complement_dominates_inside_of_odd_of_cubic
    D W hreg hW hparity
  have hpoint : ∀ v : {v : V // v ∉ S},
      1 ≤ (D.neighborFinset v.1 ∩ S).card := by
    intro v
    have hvW : v.1 ∈ W := by simpa [S] using v.2
    obtain ⟨w, hwW, hvw⟩ := hdom v.1 hvW
    have hwS : w ∈ S := by simpa [S] using hwW
    exact Finset.one_le_card.mpr ⟨w, Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v.1 w).mpr hvw, hwS⟩⟩
  have hlower : Fintype.card {v : V // v ∉ S} ≤
      ∑ v : {v : V // v ∉ S}, (D.neighborFinset v.1 ∩ S).card := by
    have hsum := Finset.sum_le_sum (s :=
      (Finset.univ : Finset {v : V // v ∉ S})) fun v _hv => hpoint v
    simpa using hsum
  have hupper := sum_card_neighbor_inter_deleted_le_sum_degrees D S
  have hrhs : (∑ x ∈ S, D.degree x) = S.card * 3 := by
    simp [hreg]
  have hcut : Fintype.card {v : V // v ∉ S} ≤ S.card * 3 := by
    rw [← hrhs]
    exact hlower.trans hupper
  have houtside : Fintype.card {v : V // v ∉ S} = W.card := by
    simp [S]
  have hScard : S.card = 34 - W.card := by
    simp [S, Finset.card_compl, hcard]
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  rw [houtside, hScard] at hcut
  omega

/-- Combined size window for the odd-cardinality branch of the order-34
cubic defect kernel. -/
theorem oddDefectSet_card_mem_nine_twentyFive_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    9 ≤ W.card ∧ W.card ≤ 25 :=
  ⟨oddDefectSet_nine_le_card_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity,
    oddDefectSet_card_le_twentyFive_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity⟩

/-- On 34 vertices with cubic defect degree, the complement of an
odd-cardinality defect-kernel set satisfies the same kernel law. -/
theorem oddDefectSet_compl_parity_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v : V,
      (if v ∈ Wᶜ then (1 : ZMod 2) else 0) + (Wᶜ.card : ZMod 2) +
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 := by
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  have hScard : Wᶜ.card = 34 - W.card := by
    simp [Finset.card_compl, hcard]
  have hSodd : Odd Wᶜ.card := by
    rcases hW with ⟨k, hk⟩
    rw [hScard]
    refine ⟨16 - k, ?_⟩
    omega
  have hScast : (Wᶜ.card : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr hSodd
  have hdecoded := oddDefectSet_neighborParity_of_odd D W hW hparity
  intro v
  have hinter : D.neighborFinset v ∩ Wᶜ = D.neighborFinset v \ W := by
    ext x
    simp
  have hsplit : (D.neighborFinset v ∩ W).card +
      (D.neighborFinset v ∩ Wᶜ).card = 3 := by
    rw [hinter]
    simpa [D.card_neighborFinset_eq_degree, hreg v] using
      Finset.card_inter_add_card_sdiff (D.neighborFinset v) W
  by_cases hv : v ∈ W
  · have hvS : v ∉ Wᶜ := by simpa using hv
    have hleftEven := hdecoded.1 v hv
    have hrightOdd : Odd (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftEven with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 1 :=
      ZMod.natCast_eq_one_iff_odd.mpr hrightOdd
    rw [if_neg hvS, hScast, hrightCast]
    decide
  · have hvS : v ∈ Wᶜ := by simpa using hv
    have hleftOdd := hdecoded.2 v hv
    have hrightEven : Even (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftOdd with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr hrightEven
    rw [if_pos hvS, hScast, hrightCast]
    decide

/-- On 34 vertices with cubic defect degree, the complement of an
even-cardinality defect-kernel set also satisfies the kernel law. -/
theorem oddDefectSet_compl_parity_of_even_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v : V,
      (if v ∈ Wᶜ then (1 : ZMod 2) else 0) + (Wᶜ.card : ZMod 2) +
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 := by
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  have hScard : Wᶜ.card = 34 - W.card := by
    simp [Finset.card_compl, hcard]
  have hSeven : Even Wᶜ.card := by
    rcases hW with ⟨k, hk⟩
    rw [hScard]
    refine ⟨17 - k, ?_⟩
    omega
  have hScast : (Wᶜ.card : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hSeven
  have hdecoded := oddDefectSet_neighborParity_of_even D W hW hparity
  intro v
  have hinter : D.neighborFinset v ∩ Wᶜ = D.neighborFinset v \ W := by
    ext x
    simp
  have hsplit : (D.neighborFinset v ∩ W).card +
      (D.neighborFinset v ∩ Wᶜ).card = 3 := by
    rw [hinter]
    simpa [D.card_neighborFinset_eq_degree, hreg v] using
      Finset.card_inter_add_card_sdiff (D.neighborFinset v) W
  by_cases hv : v ∈ W
  · have hvS : v ∉ Wᶜ := by simpa using hv
    have hleftOdd := hdecoded.1 v hv
    have hrightEven : Even (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftOdd with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr hrightEven
    rw [if_neg hvS, hScast, hrightCast]
    norm_num
  · have hvS : v ∈ Wᶜ := by simpa using hv
    have hleftEven := hdecoded.2 v hv
    have hrightOdd : Odd (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftEven with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 1 :=
      ZMod.natCast_eq_one_iff_odd.mpr hrightOdd
    rw [if_pos hvS, hScast, hrightCast]
    decide

/-- Normalize an odd-cardinality kernel set by complementing if necessary.
The resulting representative has one of the five possible odd sizes
`9, 11, 13, 15, 17`. -/
theorem exists_normalized_oddDefectSet_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V, Odd S.card ∧ 9 ≤ S.card ∧ S.card ≤ 17 ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  have hwindow :=
    oddDefectSet_card_mem_nine_twentyFive_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity
  by_cases hsmall : W.card ≤ 17
  · exact ⟨W, hW, hwindow.1, hsmall, hparity⟩
  · have hWle : W.card ≤ 34 := by
      rw [← hcard]
      exact Finset.card_le_univ W
    have hScard : Wᶜ.card = 34 - W.card := by
      simp [Finset.card_compl, hcard]
    have hSodd : Odd Wᶜ.card := by
      rcases hW with ⟨k, hk⟩
      rw [hScard]
      refine ⟨16 - k, ?_⟩
      omega
    refine ⟨Wᶜ, hSodd, ?_, ?_,
      oddDefectSet_compl_parity_of_odd_of_cubic_thirtyFour
        D W hcard hreg hW hparity⟩
    · rw [hScard]
      omega
    · rw [hScard]
      omega

/-- Finite size dispatcher for normalized odd defect-kernel sets. -/
theorem exists_oddDefectSet_card_nine_or_eleven_or_thirteen_or_fifteen_or_seventeen
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V,
      (S.card = 9 ∨ S.card = 11 ∨ S.card = 13 ∨
        S.card = 15 ∨ S.card = 17) ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  obtain ⟨S, hSodd, hSlo, hShi, hSparity⟩ :=
    exists_normalized_oddDefectSet_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity
  refine ⟨S, ?_, hSparity⟩
  rcases hSodd with ⟨k, hk⟩
  omega

/-- Normalize a nontrivial even-cardinality kernel set by complementing if
necessary.  The smaller representative has even size between two and 16. -/
theorem exists_normalized_even_oddDefectSet_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hWempty : W ≠ ∅) (hWuniv : W ≠ Finset.univ) (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V, Even S.card ∧ 2 ≤ S.card ∧ S.card ≤ 16 ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  have hWpos : 0 < W.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hWempty)
  have hWlt : W.card < 34 := by
    rw [← hcard]
    exact (Finset.card_lt_iff_ne_univ W).2 hWuniv
  by_cases hsmall : W.card ≤ 17
  · refine ⟨W, hW, ?_, ?_, hparity⟩
    · rcases hW with ⟨k, hk⟩
      omega
    · rcases hW with ⟨k, hk⟩
      omega
  · have hScard : Wᶜ.card = 34 - W.card := by
      simp [Finset.card_compl, hcard]
    have hSeven : Even Wᶜ.card := by
      rcases hW with ⟨k, hk⟩
      rw [hScard]
      refine ⟨17 - k, ?_⟩
      omega
    refine ⟨Wᶜ, hSeven, ?_, ?_,
      oddDefectSet_compl_parity_of_even_of_cubic_thirtyFour
        D W hcard hreg hW hparity⟩
    · rw [hScard]
      rcases hSeven with ⟨k, hk⟩
      omega
    · rw [hScard]
      omega

/-- Finite size dispatcher for normalized nontrivial even kernel sets. -/
theorem exists_even_oddDefectSet_card_two_or_four_or_six_or_eight_or_ten_or_twelve_or_fourteen_or_sixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hWempty : W ≠ ∅) (hWuniv : W ≠ Finset.univ) (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V,
      (S.card = 2 ∨ S.card = 4 ∨ S.card = 6 ∨ S.card = 8 ∨
        S.card = 10 ∨ S.card = 12 ∨ S.card = 14 ∨ S.card = 16) ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  obtain ⟨S, hSeven, hSlo, hShi, hSparity⟩ :=
    exists_normalized_even_oddDefectSet_of_cubic_thirtyFour
      D W hcard hreg hWempty hWuniv hW hparity
  refine ⟨S, ?_, hSparity⟩
  rcases hSeven with ⟨k, hk⟩
  omega

/-- A two-vertex even kernel set is an adjacent-twin pair in the defect
graph: the two vertices are adjacent and have identical adjacency to every
other vertex. -/
theorem oddDefectSet_card_two_exists_adjacent_twins
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hWcard : W.card = 2)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ a b : V, a ≠ b ∧ W = {a, b} ∧ D.Adj a b ∧
      ∀ v, v ≠ a → v ≠ b → (D.Adj a v ↔ D.Adj b v) := by
  obtain ⟨a, b, hab, hW⟩ := Finset.card_eq_two.mp hWcard
  have hWeven : Even W.card := by rw [hWcard]; decide
  have hinside := oddDefectSet_no_isolated_inside_of_even D W hWeven hparity
  have haW : a ∈ W := by simp [hW]
  obtain ⟨w, hwW, haw⟩ := hinside a haW
  have hw : w = a ∨ w = b := by simpa [hW] using hwW
  have habAdj : D.Adj a b := by
    rcases hw with rfl | rfl
    · exact (D.ne_of_adj haw rfl).elim
    · exact haw
  refine ⟨a, b, hab, hW, habAdj, ?_⟩
  intro v hva hvb
  have hvW : v ∉ W := by simp [hW, hva, hvb]
  have hout := (oddDefectSet_neighborParity_of_even D W hWeven hparity).2 v hvW
  have hsub : D.neighborFinset v ∩ W ⊆ W := Finset.inter_subset_right
  have hle : (D.neighborFinset v ∩ W).card ≤ 2 := by
    rw [← hWcard]
    exact Finset.card_le_card hsub
  constructor
  · intro hav
    have haMem : a ∈ D.neighborFinset v ∩ W := Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v a).mpr hav.symm, haW⟩
    have hpos : 0 < (D.neighborFinset v ∩ W).card :=
      Finset.card_pos.mpr ⟨a, haMem⟩
    have heq : (D.neighborFinset v ∩ W).card = 2 := by
      rcases hout with ⟨k, hk⟩
      omega
    have hall : D.neighborFinset v ∩ W = W :=
      Finset.eq_of_subset_of_card_le hsub (by rw [heq, hWcard])
    have hbMem : b ∈ D.neighborFinset v := by
      have : b ∈ D.neighborFinset v ∩ W := by rw [hall]; simp [hW]
      exact (Finset.mem_inter.mp this).1
    exact ((D.mem_neighborFinset v b).mp hbMem).symm
  · intro hbv
    have hbMem : b ∈ D.neighborFinset v ∩ W := Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v b).mpr hbv.symm, by simp [hW]⟩
    have hpos : 0 < (D.neighborFinset v ∩ W).card :=
      Finset.card_pos.mpr ⟨b, hbMem⟩
    have heq : (D.neighborFinset v ∩ W).card = 2 := by
      rcases hout with ⟨k, hk⟩
      omega
    have hall : D.neighborFinset v ∩ W = W :=
      Finset.eq_of_subset_of_card_le hsub (by rw [heq, hWcard])
    have haMem : a ∈ D.neighborFinset v := by
      have : a ∈ D.neighborFinset v ∩ W := by rw [hall]; simp [hW]
      exact (Finset.mem_inter.mp this).1
    exact ((D.mem_neighborFinset v a).mp haMem).symm

/-- Adjacent twins in a cubic graph have exactly two common neighbors, so
their shared edge belongs to exactly two triangles. -/
theorem adjacent_twins_commonNeighbor_card_eq_two_of_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 3) {a b : V} (hadj : D.Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b → (D.Adj a v ↔ D.Adj b v)) :
    (D.neighborFinset a ∩ D.neighborFinset b).card = 2 := by
  have heq : D.neighborFinset a ∩ D.neighborFinset b =
      (D.neighborFinset a).erase b := by
    ext v
    constructor
    · intro hv
      have hva := (Finset.mem_inter.mp hv).1
      have hvb := (Finset.mem_inter.mp hv).2
      have hvne : v ≠ b := fun h => by
        subst v
        exact D.loopless.irrefl b ((D.mem_neighborFinset b b).mp hvb)
      exact Finset.mem_erase.mpr ⟨hvne, hva⟩
    · intro hv
      have hv' := Finset.mem_erase.mp hv
      have hav : D.Adj a v := (D.mem_neighborFinset a v).mp hv'.2
      have hva : v ≠ a := fun h => by
        subst v
        exact D.loopless.irrefl a hav
      have hbv : D.Adj b v := (htwins v hva hv'.1).mp hav
      exact Finset.mem_inter.mpr
        ⟨hv'.2, (D.mem_neighborFinset b v).mpr hbv⟩
  rw [heq, Finset.card_erase_of_mem
    ((D.mem_neighborFinset a b).mpr hadj),
    D.card_neighborFinset_eq_degree, hreg a]

/-- Cubic specialization of the two-vertex kernel classification: the
forced adjacent twins have exactly two common defect neighbors. -/
theorem oddDefectSet_card_two_exists_adjacent_twins_with_two_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hreg : ∀ v, D.degree v = 3) (hWcard : W.card = 2)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ a b : V, a ≠ b ∧ W = {a, b} ∧ D.Adj a b ∧
      (∀ v, v ≠ a → v ≠ b → (D.Adj a v ↔ D.Adj b v)) ∧
      (D.neighborFinset a ∩ D.neighborFinset b).card = 2 := by
  obtain ⟨a, b, hab, hW, hadj, htwins⟩ :=
    oddDefectSet_card_two_exists_adjacent_twins D W hWcard hparity
  exact ⟨a, b, hab, hW, hadj, htwins,
    adjacent_twins_commonNeighbor_card_eq_two_of_cubic D hreg hadj htwins⟩

/-- In an even-degree excess-one graph, the shared edge of adjacent twins in
the combined defect graph cannot have the triangle-free color. -/
theorem excessOne_even_adjacent_defect_twins_not_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V}
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    ¬ (triangleFreeEdgeGraph G).Adj a b := by
  intro habT
  have hsubset : (triangleFreeEdgeGraph G).neighborFinset a ⊆ {b} := by
    intro v hv
    have havT : (triangleFreeEdgeGraph G).Adj a v :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset a v).mp hv
    by_cases hvb : v = b
    · simp [hvb]
    · have hva : v ≠ a :=
        (triangleFreeEdgeGraph G).ne_of_adj havT |>.symm
      have havD : (secondOrderDefectGraph G).Adj a v := by
        simp only [secondOrderDefectGraph, SimpleGraph.sup_adj]
        exact Or.inr havT
      have hbvD : (secondOrderDefectGraph G).Adj b v :=
        (htwins v hva hvb).mp havD
      exact (not_two_adjacent_triangleFree_in_defect_triangle
        G habT.symm havT hbvD.symm).elim
  have hbmem : b ∈ (triangleFreeEdgeGraph G).neighborFinset a :=
    ((triangleFreeEdgeGraph G).mem_neighborFinset a b).mpr habT
  have heq : (triangleFreeEdgeGraph G).neighborFinset a = {b} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hbmem, fun v hv => by
      have := hsubset hv
      simpa using this⟩
  have hdegOne : (triangleFreeEdgeGraph G).degree a = 1 := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, heq]
    simp
  rcases excessOne_even_triangleFree_degree_zero_or_two
      G hfree heven hreg hcard a with hzero | htwo <;> omega

/-- Therefore the shared edge of adjacent defect twins has the antipodal
color. -/
theorem excessOne_even_adjacent_defect_twins_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    (antipodalGraph G).Adj a b := by
  simp only [secondOrderDefectGraph, SimpleGraph.sup_adj] at habD
  rcases habD with habC | habT
  · exact habC
  · exact (excessOne_even_adjacent_defect_twins_not_triangleFree
      G hfree heven hreg hcard htwins habT).elim

/-- Every hypothetical degree-six plateau core at order 34 carries a proper,
nonempty defect set satisfying the exact mod-two neighborhood law. -/
theorem C4PlateauCore.degreeSix_thirtyFour_exists_odd_defect_set
    (hcore : C4PlateauCore 34 6) :
    ∃ (G : SimpleGraph (Fin 34)) (_ : DecidableRel G.Adj)
        (W : Finset (Fin 34)),
      ¬ containsC4 (Fin 34) G ∧
      (∀ x, G.degree x = 6) ∧
      W ≠ ∅ ∧ W ≠ Finset.univ ∧ ∀ v : Fin 34,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) = 0 := by
  rcases hcore.degreeSix_thirtyFour_positiveExcessOne with
    ⟨_hm, _he, G, hdec, hfree, hreg, _hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨W, hWempty, hWuniv, hWparity⟩ :=
    excessOne_even_exists_odd_defect_set G hfree (by decide) hreg (by norm_num)
  exact ⟨G, hdec, W, hfree, hreg, hWempty, hWuniv, hWparity⟩

/-- Plateau-facing structural dichotomy for the order-34 excess-one kernel.
The even-cardinality branch has no isolated vertex in the induced defect
subgraph; the odd branch admits a normalized representative of one of five
explicit sizes. -/
theorem C4PlateauCore.degreeSix_thirtyFour_defectKernel_dichotomy
    (hcore : C4PlateauCore 34 6) :
    ∃ (G : SimpleGraph (Fin 34)) (_ : DecidableRel G.Adj)
        (W : Finset (Fin 34)),
      ¬ containsC4 (Fin 34) G ∧
      (∀ x, G.degree x = 6) ∧
      (∀ x, (secondOrderDefectGraph G).degree x = 3) ∧
      W ≠ ∅ ∧ W ≠ Finset.univ ∧
      (∀ v : Fin 34,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) = 0) ∧
      ((Even W.card ∧ (∀ v ∈ W, ∃ w ∈ W,
          (secondOrderDefectGraph G).Adj v w) ∧
          ∃ S : Finset (Fin 34),
            (S.card = 2 ∨ S.card = 4 ∨ S.card = 6 ∨ S.card = 8 ∨
              S.card = 10 ∨ S.card = 12 ∨ S.card = 14 ∨ S.card = 16) ∧
            ∀ v : Fin 34,
              (if v ∈ S then (1 : ZMod 2) else 0) +
                (S.card : ZMod 2) +
                ((((secondOrderDefectGraph G).neighborFinset v ∩ S).card :
                  ZMod 2)) = 0) ∨
        ∃ S : Finset (Fin 34),
          (S.card = 9 ∨ S.card = 11 ∨ S.card = 13 ∨
            S.card = 15 ∨ S.card = 17) ∧
          ∀ v : Fin 34,
            (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
              ((((secondOrderDefectGraph G).neighborFinset v ∩ S).card :
                ZMod 2)) = 0) := by
  rcases hcore.degreeSix_thirtyFour_positiveExcessOne with
    ⟨_hm, _he, G, hdec, hfree, hreg, hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨W, hWempty, hWuniv, hWparity⟩ :=
    excessOne_even_exists_odd_defect_set G hfree (by decide) hreg (by norm_num)
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 3 := by
    intro x
    simpa using hregD x
  refine ⟨G, hdec, W, hfree, hreg, hDreg, hWempty, hWuniv,
    hWparity, ?_⟩
  rcases Nat.even_or_odd W.card with hWeven | hWodd
  · left
    exact ⟨hWeven,
      oddDefectSet_no_isolated_inside_of_even
        (secondOrderDefectGraph G) W hWeven hWparity,
      exists_even_oddDefectSet_card_two_or_four_or_six_or_eight_or_ten_or_twelve_or_fourteen_or_sixteen
        (secondOrderDefectGraph G) W (by simp) hDreg hWempty hWuniv
          hWeven hWparity⟩
  · right
    exact exists_oddDefectSet_card_nine_or_eleven_or_thirteen_or_fifteen_or_seventeen
      (secondOrderDefectGraph G) W (by simp) hDreg hWodd hWparity

end

end Erdos85
