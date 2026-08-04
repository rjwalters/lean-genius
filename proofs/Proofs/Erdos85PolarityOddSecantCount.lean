import Proofs.Erdos85PolarityEven
import Proofs.Erdos85SafeSetCounting

/-!
# Counting odd-characteristic secant defects

After deleting the full absolute conic, a surviving vertex loses two degree
units exactly when its polar line is a secant.  Distinct absolute pairs have
unique nonabsolute common neighbors, while the odd two-secant theorem makes
the pair recoverable from that neighbor.  This gives an explicit bijection
and an exact count of the degree-loss-two vertices.
-/

open SimpleGraph Matrix
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

variable (K : Type u) [Field K] [Finite K] [DecidableEq K]

private abbrev P := Projectivization K (Fin 3 → K)
private abbrev AbsolutePairs :=
  {D : Finset (P K) // D ∈ (absolutePoints K).powersetCard 2}

private noncomputable def pairFirst (D : AbsolutePairs K) : P K :=
  Classical.choose ((Finset.card_eq_two.mp
    (Finset.mem_powersetCard.mp D.2).2))

private noncomputable def pairSecond (D : AbsolutePairs K) : P K :=
  Classical.choose (Classical.choose_spec ((Finset.card_eq_two.mp
    (Finset.mem_powersetCard.mp D.2).2)))

omit [DecidableEq K] in
private theorem pair_spec (D : AbsolutePairs K) :
    pairFirst K D ≠ pairSecond K D ∧
      D.1 = {pairFirst K D, pairSecond K D} := by
  exact Classical.choose_spec (Classical.choose_spec
    ((Finset.card_eq_two.mp (Finset.mem_powersetCard.mp D.2).2)))

omit [DecidableEq K] in
private theorem pair_first_absolute (D : AbsolutePairs K) :
    pairFirst K D ∈ absolutePoints K := by
  have hsub := (Finset.mem_powersetCard.mp D.2).1
  apply hsub
  rw [(pair_spec K D).2]
  simp

omit [DecidableEq K] in
private theorem pair_second_absolute (D : AbsolutePairs K) :
    pairSecond K D ∈ absolutePoints K := by
  have hsub := (Finset.mem_powersetCard.mp D.2).1
  apply hsub
  rw [(pair_spec K D).2]
  simp

private noncomputable def pairCommonNeighbor (D : AbsolutePairs K) : P K :=
  Classical.choose (existsUnique_nonabsolute_commonNeighbor_of_absolute K
    ((mem_absolutePoints K _).mp (pair_first_absolute K D))
    ((mem_absolutePoints K _).mp (pair_second_absolute K D))
    (pair_spec K D).1)

private theorem pairCommonNeighbor_spec (D : AbsolutePairs K) :
    (graph K).Adj (pairFirst K D) (pairCommonNeighbor K D) ∧
    (graph K).Adj (pairSecond K D) (pairCommonNeighbor K D) ∧
    ¬ Projectivization.orthogonal (pairCommonNeighbor K D)
      (pairCommonNeighbor K D) := by
  exact (Classical.choose_spec
    (existsUnique_nonabsolute_commonNeighbor_of_absolute K
      ((mem_absolutePoints K _).mp (pair_first_absolute K D))
      ((mem_absolutePoints K _).mp (pair_second_absolute K D))
      (pair_spec K D).1)).1

noncomputable def oddSecantVertices : Finset (P K) :=
  by
    classical
    exact Finset.univ.filter fun v =>
      ¬ Projectivization.orthogonal v v ∧
        ((graph K).neighborFinset v ∩ absolutePoints K).card = 2

omit [DecidableEq K] in
@[simp] theorem mem_oddSecantVertices (v : P K) :
    v ∈ oddSecantVertices K ↔
      ¬ Projectivization.orthogonal v v ∧
        ((graph K).neighborFinset v ∩ absolutePoints K).card = 2 := by
  classical
  simp [oddSecantVertices]

private theorem pair_incidence_eq (h2 : (2 : K) ≠ 0)
    (D : AbsolutePairs K) :
    (graph K).neighborFinset (pairCommonNeighbor K D) ∩ absolutePoints K = D.1 := by
  let N := (graph K).neighborFinset (pairCommonNeighbor K D) ∩ absolutePoints K
  have hsub : D.1 ⊆ N := by
    intro a ha
    rw [(pair_spec K D).2] at ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_inter.mpr ⟨by
        simpa only [SimpleGraph.mem_neighborFinset] using
          (pairCommonNeighbor_spec K D).1.symm,
        pair_first_absolute K D⟩
    · have haeq : a = pairSecond K D := Finset.mem_singleton.mp ha
      subst a
      exact Finset.mem_inter.mpr ⟨by
        simpa only [SimpleGraph.mem_neighborFinset] using
          (pairCommonNeighbor_spec K D).2.1.symm,
        pair_second_absolute K D⟩
  have hNle : N.card ≤ 2 :=
    absoluteTwoSecant_of_two_ne_zero K h2 (pairCommonNeighbor K D)
      (pairCommonNeighbor_spec K D).2.2
  have hDcard : D.1.card = 2 := (Finset.mem_powersetCard.mp D.2).2
  have hNge : 2 ≤ N.card := by
    rw [← hDcard]
    exact Finset.card_le_card hsub
  have heq : D.1 = N := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact heq.symm

private noncomputable def pairToSecant (h2 : (2 : K) ≠ 0) :
    AbsolutePairs K → {v : P K // v ∈ oddSecantVertices K} := fun D =>
  ⟨pairCommonNeighbor K D, (mem_oddSecantVertices K _).mpr
    ⟨(pairCommonNeighbor_spec K D).2.2, by
      rw [pair_incidence_eq K h2 D]
      exact (Finset.mem_powersetCard.mp D.2).2⟩⟩

private theorem pairToSecant_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (pairToSecant K h2) := by
  intro D E hDE
  apply Subtype.ext
  rw [← pair_incidence_eq K h2 D, ← pair_incidence_eq K h2 E]
  have hv : pairCommonNeighbor K D = pairCommonNeighbor K E :=
    congrArg Subtype.val hDE
  rw [hv]

private noncomputable def secantToPair :
    {v : P K // v ∈ oddSecantVertices K} → AbsolutePairs K := fun v =>
  ⟨(graph K).neighborFinset v.1 ∩ absolutePoints K,
    Finset.mem_powersetCard.mpr ⟨by
      intro a ha
      exact (Finset.mem_inter.mp ha).2,
      (mem_oddSecantVertices K v.1).mp v.2 |>.2⟩⟩

omit [DecidableEq K] in
private theorem secantToPair_injective :
    Function.Injective (secantToPair K) := by
  intro v w hvw
  have hN : (graph K).neighborFinset v.1 ∩ absolutePoints K =
      (graph K).neighborFinset w.1 ∩ absolutePoints K :=
    congrArg Subtype.val hvw
  have hvcard : ((graph K).neighborFinset v.1 ∩ absolutePoints K).card = 2 :=
    (mem_oddSecantVertices K v.1).mp v.2 |>.2
  obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp hvcard
  apply Subtype.ext
  by_contra hvwval
  have hle := Finset.card_le_one.mp (commonNeighbors_le_one v.1 w.1 hvwval)
  have haV : (graph K).Adj v.1 a := by
    have : a ∈ (graph K).neighborFinset v.1 ∩ absolutePoints K := by
      rw [hpairs]
      simp
    exact (by simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp this).1)
  have hbV : (graph K).Adj v.1 b := by
    have : b ∈ (graph K).neighborFinset v.1 ∩ absolutePoints K := by
      rw [hpairs]
      simp
    exact (by simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp this).1)
  have haW : (graph K).Adj w.1 a := by
    have ha : a ∈ (graph K).neighborFinset w.1 ∩ absolutePoints K := by
      rw [← hN, hpairs]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp ha).1
  have hbW : (graph K).Adj w.1 b := by
    have hb : b ∈ (graph K).neighborFinset w.1 ∩ absolutePoints K := by
      rw [← hN, hpairs]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hb).1
  apply hab
  apply hle a
  · simp [haV, haW]
  · simp [hbV, hbW]

/-- In odd characteristic, the vertices incident with exactly two absolute
points are in bijection with unordered pairs of absolute points.  Hence there
are exactly `choose (q + 1) 2` such secant vertices. -/
theorem card_oddSecantVertices (h2 : (2 : K) ≠ 0) :
    (oddSecantVertices K).card = Nat.choose (Nat.card K + 1) 2 := by
  letI := Fintype.ofFinite K
  apply Nat.le_antisymm
  · have hc := Fintype.card_le_of_injective (secantToPair K)
      (secantToPair_injective K)
    change Fintype.card {v // v ∈ oddSecantVertices K} ≤
      Fintype.card {D // D ∈ (absolutePoints K).powersetCard 2} at hc
    rw [Fintype.card_coe, Fintype.card_coe,
      Finset.card_powersetCard,
      card_absolutePoints_eq_card_add_one K] at hc
    simpa [Nat.card_eq_fintype_card] using hc
  · exact (show Nat.choose (Nat.card K + 1) 2 ≤
        (oddSecantVertices K).card from by
      letI := Fintype.ofFinite K
      have hc := Fintype.card_le_of_injective (pairToSecant K h2)
        (pairToSecant_injective K h2)
      change Fintype.card {D // D ∈ (absolutePoints K).powersetCard 2} ≤
        Fintype.card {v // v ∈ oddSecantVertices K} at hc
      rw [Fintype.card_coe, Fintype.card_coe,
        Finset.card_powersetCard,
        card_absolutePoints_eq_card_add_one K] at hc
      simpa [Nat.card_eq_fintype_card] using hc)

/-- The total number of incidences between all projective points and the
absolute conic is `q(q+1)`.  This is the same incidence set counted first by
points and then by absolute vertices, each of which has degree `q`. -/
theorem sum_absoluteIncidences :
    ∑ v : P K, ((graph K).neighborFinset v ∩ absolutePoints K).card =
      (absolutePoints K).card * Nat.card K := by
  classical
  calc
    ∑ v : P K, ((graph K).neighborFinset v ∩ absolutePoints K).card
        = ∑ v : P K, ∑ a ∈ absolutePoints K,
            if a ∈ (graph K).neighborFinset v then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.sum_boole]
              congr 1
              ext a
              simp [and_comm]
    _ = ∑ a ∈ absolutePoints K, ∑ v : P K,
          if a ∈ (graph K).neighborFinset v then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ a ∈ absolutePoints K, (graph K).degree a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [SimpleGraph.degree, Finset.sum_boole]
          apply congrArg Finset.card
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            SimpleGraph.mem_neighborFinset]
          exact ((graph K).adj_comm a v).symm
    _ = (absolutePoints K).card * Nat.card K := by
          calc
            ∑ a ∈ absolutePoints K, (graph K).degree a =
                ∑ _a ∈ absolutePoints K, Nat.card K := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  exact degree_eq_card_of_selfOrthogonal
                    ((mem_absolutePoints K a).mp ha)
            _ = (absolutePoints K).card * Nat.card K := by simp

/-- In odd characteristic a nonabsolute point cannot be tangent to the
absolute conic.  The classified secants already contribute all `q(q+1)`
point-conic incidences, so one further incidence would exceed the double
count. -/
theorem absoluteIncidences_ne_one (h2 : (2 : K) ≠ 0) (v : P K)
    (hvnon : ¬ Projectivization.orthogonal v v) :
    ((graph K).neighborFinset v ∩ absolutePoints K).card ≠ 1 := by
  intro hvone
  let w : P K → ℕ := fun x =>
    ((graph K).neighborFinset x ∩ absolutePoints K).card
  have hvnot : v ∉ oddSecantVertices K := by
    rw [mem_oddSecantVertices]
    simp [hvnon, hvone]
  have hsumS : ∑ x ∈ oddSecantVertices K, w x =
      2 * (oddSecantVertices K).card := by
    calc
      ∑ x ∈ oddSecantVertices K, w x =
          ∑ _x ∈ oddSecantVertices K, 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (mem_oddSecantVertices K x).mp hx |>.2
      _ = 2 * (oddSecantVertices K).card := by simp [Nat.mul_comm]
  have hle : ∑ x ∈ insert v (oddSecantVertices K), w x ≤
      ∑ x : P K, w x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      (fun _ _ _ => Nat.zero_le _)
  have hwv : w v = 1 := hvone
  rw [Finset.sum_insert hvnot, hwv, hsumS] at hle
  have htotal : ∑ x : P K, w x = (Nat.card K + 1) * Nat.card K := by
    dsimp [w]
    rw [sum_absoluteIncidences K, card_absolutePoints_eq_card_add_one K]
  rw [htotal, card_oddSecantVertices K h2, mul_comm 2,
    Nat.choose_two_right,
    Nat.div_two_mul_two_of_even
      (Nat.even_mul_pred_self (Nat.card K + 1))] at hle
  simp only [Nat.add_sub_cancel] at hle
  omega

/-- The induced graph after deleting the full odd-characteristic absolute
conic. -/
noncomputable abbrev oddCore :=
  deleteVertexSetGraph (graph K) (absolutePoints K)

/-- The vertices of the deleted-conic core whose degree realizes the lower
value `q - 1`. -/
noncomputable def oddCoreLowVertices :
    Finset {v : P K // v ∉ absolutePoints K} := by
  classical
  exact Finset.univ.filter fun v => (oddCore K).degree v = Nat.card K - 1

omit [DecidableEq K] in
@[simp] theorem mem_oddCoreLowVertices
    (v : {v : P K // v ∉ absolutePoints K}) :
    v ∈ oddCoreLowVertices K ↔ (oddCore K).degree v = Nat.card K - 1 := by
  classical
  simp [oddCoreLowVertices]

theorem mem_oddCoreLowVertices_iff_secant
    (h2 : (2 : K) ≠ 0)
    (v : {v : P K // v ∉ absolutePoints K}) :
    v ∈ oddCoreLowVertices K ↔ v.1 ∈ oddSecantVertices K := by
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    simpa [mem_absolutePoints] using v.2
  have hinc : ((graph K).neighborFinset v.1 ∩ absolutePoints K).card ≤ 2 :=
    absoluteTwoSecant_of_two_ne_zero K h2 v.1 hvnon
  have hs := degree_deleteVertexSetGraph_add (graph K) (absolutePoints K) v
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hvnon] at hs
  have hs' : (oddCore K).degree v +
      ((graph K).neighborFinset v.1 ∩ absolutePoints K).card =
      Nat.card K + 1 := by
    simpa [oddCore] using hs
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  rw [mem_oddCoreLowVertices, mem_oddSecantVertices]
  constructor
  · intro hdeg
    refine ⟨hvnon, ?_⟩
    change (oddCore K).degree v = Nat.card K - 1 at hdeg
    omega
  · rintro ⟨_, hcard⟩
    omega

theorem card_oddCoreLowVertices (h2 : (2 : K) ≠ 0) :
    (oddCoreLowVertices K).card = Nat.choose (Nat.card K + 1) 2 := by
  let emb : {v : P K // v ∉ absolutePoints K} ↪ P K :=
    Function.Embedding.subtype _
  have hmap : (oddCoreLowVertices K).map emb = oddSecantVertices K := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      dsimp [emb]
      exact (mem_oddCoreLowVertices_iff_secant K h2 v).mp hv
    · intro hz
      have hznon : ¬ Projectivization.orthogonal z z :=
        (mem_oddSecantVertices K z).mp hz |>.1
      have hzcore : z ∉ absolutePoints K := by
        simpa [mem_absolutePoints] using hznon
      let v : {v : P K // v ∉ absolutePoints K} := ⟨z, hzcore⟩
      rw [Finset.mem_map]
      refine ⟨v, ?_, rfl⟩
      exact (mem_oddCoreLowVertices_iff_secant K h2 v).mpr hz
  have hc : (oddCoreLowVertices K).card = (oddSecantVertices K).card := by
    rw [← hmap]
    exact (Finset.card_map emb).symm
  rw [hc, card_oddSecantVertices K h2]

/-- The complementary degree class in the deleted-conic odd core. -/
noncomputable def oddCoreHighVertices :
    Finset {v : P K // v ∉ absolutePoints K} := by
  classical
  exact Finset.univ.filter fun v => (oddCore K).degree v = Nat.card K + 1

omit [DecidableEq K] in
@[simp] theorem mem_oddCoreHighVertices
    (v : {v : P K // v ∉ absolutePoints K}) :
    v ∈ oddCoreHighVertices K ↔ (oddCore K).degree v = Nat.card K + 1 := by
  classical
  simp [oddCoreHighVertices]

/-- Every vertex of the odd deleted-conic core has one of exactly two
degrees: `q-1` for a secant pole and `q+1` for an external pole. -/
theorem oddCore_degree_eq_low_or_high (h2 : (2 : K) ≠ 0)
    (v : {v : P K // v ∉ absolutePoints K}) :
    (oddCore K).degree v = Nat.card K - 1 ∨
      (oddCore K).degree v = Nat.card K + 1 := by
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    simpa [mem_absolutePoints] using v.2
  let c := ((graph K).neighborFinset v.1 ∩ absolutePoints K).card
  have hcle : c ≤ 2 :=
    absoluteTwoSecant_of_two_ne_zero K h2 v.1 hvnon
  have hcne : c ≠ 1 := absoluteIncidences_ne_one K h2 v.1 hvnon
  have hs := degree_deleteVertexSetGraph_add (graph K) (absolutePoints K) v
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hvnon] at hs
  have hs' : (oddCore K).degree v + c = Nat.card K + 1 := by
    simpa [oddCore, c] using hs
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  omega

/-- The low- and high-degree classes partition the whole odd core. -/
theorem oddCoreLowVertices_union_highVertices (h2 : (2 : K) ≠ 0) :
    oddCoreLowVertices K ∪ oddCoreHighVertices K = Finset.univ := by
  ext v
  rw [Finset.mem_union, mem_oddCoreLowVertices, mem_oddCoreHighVertices]
  simp only [Finset.mem_univ, iff_true]
  exact oddCore_degree_eq_low_or_high K h2 v

omit [DecidableEq K] in
theorem oddCoreLowVertices_disjoint_highVertices :
    Disjoint (oddCoreLowVertices K) (oddCoreHighVertices K) := by
  apply Finset.disjoint_left.mpr
  intro v hlo hhi
  rw [mem_oddCoreLowVertices] at hlo
  rw [mem_oddCoreHighVertices] at hhi
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  omega

/-- Exact count of the high-degree (`q+1`) vertices.  Together with
`card_oddCoreLowVertices`, this is the full odd-core degree distribution. -/
theorem card_oddCoreHighVertices_compl (h2 : (2 : K) ≠ 0) :
    (oddCoreHighVertices K).card =
      Fintype.card {v : P K // v ∉ absolutePoints K} -
        Nat.choose (Nat.card K + 1) 2 := by
  have hcard := Finset.card_union_of_disjoint
    (oddCoreLowVertices_disjoint_highVertices K)
  rw [oddCoreLowVertices_union_highVertices K h2, Finset.card_univ,
    card_oddCoreLowVertices K h2] at hcard
  omega

private theorem three_le_card_of_two_ne_zero (h2 : (2 : K) ≠ 0) :
    3 ≤ Nat.card K := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  by_contra hq3
  have hq2 : Nat.card K = 2 := by omega
  obtain ⟨y, hy, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hq2
  have hsum0 : (1 : K) + 1 = 0 := by
    by_contra hsum
    have hsumy : (1 : K) + 1 = y := hyuniq _ hsum
    have h1y : (1 : K) = y := hyuniq _ one_ne_zero
    have hbad : (1 : K) + 1 = 1 := hsumy.trans h1y.symm
    have : (1 : K) = 0 := by
      apply add_left_cancel (a := (1 : K))
      rw [add_zero]
      exact hbad
    exact one_ne_zero this
  apply h2
  rw [← one_add_one_eq_two]
  exact hsum0

theorem card_oddCore :
    Fintype.card {v : P K // v ∉ absolutePoints K} =
      Nat.card K * Nat.card K := by
  rw [Fintype.card_subtype_compl (fun v : P K => v ∈ absolutePoints K)]
  rw [Fintype.card_coe, Fintype.card_eq_nat_card, card_points_tight K,
    card_absolutePoints_eq_card_add_one K]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  have hN : (Nat.card K + 1) * Nat.card K + 1 =
      Nat.card K * Nat.card K + Nat.card K + 1 := by ring
  rw [hN]
  omega

theorem card_oddCoreHighVertices (h2 : (2 : K) ≠ 0) :
    (oddCoreHighVertices K).card =
      Nat.card K * Nat.card K - Nat.choose (Nat.card K + 1) 2 := by
  rw [card_oddCoreHighVertices_compl K h2, card_oddCore K]

theorem oddCore_minDegree_ge (h2 : (2 : K) ≠ 0) :
    Nat.card K - 1 ≤ (oddCore K).minDegree := by
  letI : Nonempty {v : P K // v ∉ absolutePoints K} := by
    apply Fintype.card_pos_iff.mp
    rw [card_oddCore K]
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
    positivity
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    simpa [mem_absolutePoints] using v.2
  have hinc : ((graph K).neighborFinset v.1 ∩ absolutePoints K).card ≤ 2 :=
    absoluteTwoSecant_of_two_ne_zero K h2 v.1 hvnon
  have hs := degree_deleteVertexSetGraph_add (graph K) (absolutePoints K) v
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hvnon] at hs
  have hs' : (oddCore K).degree v +
      ((graph K).neighborFinset v.1 ∩ absolutePoints K).card =
      Nat.card K + 1 := by simpa [oddCore] using hs
  omega

/-- The full deleted-conic core cannot be repaired by attaching one vertex at
degree `q`: every degree-`q-1` defect would have to lie in the attachment
selector, but there are `choose (q+1) 2` defects, more than any safe selector
can contain by the disjoint-neighborhood count. -/
theorem not_exists_safeSet_covering_oddCoreLowVertices
    (h2 : (2 : K) ≠ 0) :
    ¬ ∃ S : Finset {v : P K // v ∉ absolutePoints K},
      oddCoreLowVertices K ⊆ S ∧ CommonNeighborIndependent (oddCore K) S := by
  rintro ⟨S, hcover, hsafe⟩
  have hq3 : 3 ≤ Nat.card K := three_le_card_of_two_ne_zero K h2
  have hchoose : Nat.card K + 2 ≤ Nat.choose (Nat.card K + 1) 2 := by
    rw [Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le (by omega)).2
    rw [Nat.add_sub_cancel_right]
    nlinarith
  have hlarge : Nat.card K + 2 ≤ S.card := by
    calc
      Nat.card K + 2 ≤ Nat.choose (Nat.card K + 1) 2 := hchoose
      _ = (oddCoreLowVertices K).card := (card_oddCoreLowVertices K h2).symm
      _ ≤ S.card := Finset.card_le_card hcover
  have hcount := hsafe.card_mul_le_card_of_minDegree (oddCore K) S
    (oddCore_minDegree_ge K h2)
  rw [card_oddCore K] at hcount
  have hprod : (Nat.card K + 2) * (Nat.card K - 1) ≤
      Nat.card K * Nat.card K :=
    (Nat.mul_le_mul_right (Nat.card K - 1) hlarge).trans hcount
  have hqeq : Nat.card K = (Nat.card K - 1) + 1 := by omega
  rw [hqeq] at hprod
  nlinarith

end Erdos85.Polarity
