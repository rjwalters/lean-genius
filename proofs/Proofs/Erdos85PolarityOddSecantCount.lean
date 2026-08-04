import Proofs.Erdos85PolarityEven
import Proofs.Erdos85SafeSetCounting
import Proofs.Erdos85IntersectingPairs

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

/-- Absolute neighbors of a point, typed as elements of the absolute locus. -/
noncomputable def absoluteNeighborPair (v : P K) :
    Finset {a : P K // a ∈ absolutePoints K} := by
  classical
  exact Finset.univ.filter fun a => (graph K).Adj v a.1

omit [DecidableEq K] in
@[simp] theorem mem_absoluteNeighborPair (v : P K)
    (a : {a : P K // a ∈ absolutePoints K}) :
    a ∈ absoluteNeighborPair K v ↔ (graph K).Adj v a.1 := by
  classical
  simp [absoluteNeighborPair]

omit [DecidableEq K] in
theorem card_absoluteNeighborPair (v : P K) :
    (absoluteNeighborPair K v).card =
      ((graph K).neighborFinset v ∩ absolutePoints K).card := by
  let emb : {a : P K // a ∈ absolutePoints K} ↪ P K :=
    Function.Embedding.subtype _
  have heq : (absoluteNeighborPair K v).map emb =
      (graph K).neighborFinset v ∩ absolutePoints K := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      exact Finset.mem_inter.mpr
        ⟨by simpa [emb] using (mem_absoluteNeighborPair K v b).mp hb, b.2⟩
    · intro ha
      have ha' := Finset.mem_inter.mp ha
      rw [Finset.mem_map]
      refine ⟨⟨a, ha'.2⟩, ?_, rfl⟩
      exact (mem_absoluteNeighborPair K v _).mpr (by simpa using ha'.1)
  rw [← heq, Finset.card_map]

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

/-- Distinct nonabsolute points whose absolute-neighbor pairs are disjoint
have a common neighbor that is itself nonabsolute. -/
theorem exists_nonabsolute_commonNeighbor_of_disjoint_absoluteIncidences
    (x y : P K)
    (hxnon : ¬ Projectivization.orthogonal x x)
    (hynon : ¬ Projectivization.orthogonal y y) (hxy : x ≠ y)
    (hdisj : Disjoint
      ((graph K).neighborFinset x ∩ absolutePoints K)
      ((graph K).neighborFinset y ∩ absolutePoints K)) :
    ∃ z, ¬ Projectivization.orthogonal z z ∧
      (graph K).Adj x z ∧ (graph K).Adj y z := by
  obtain ⟨z, hzx, hzy⟩ :=
    Configuration.HasPoints.existsUnique_point
      (Projectivization K (Fin 3 → K))
      (Projectivization K (Fin 3 → K)) x y hxy |>.exists
  have hzxo : Projectivization.orthogonal z x :=
    (Configuration.ofField.mem_iff z x).mp hzx
  have hzyo : Projectivization.orthogonal z y :=
    (Configuration.ofField.mem_iff z y).mp hzy
  have hzxne : z ≠ x := by
    intro h
    apply hxnon
    simpa [h] using hzxo
  have hzyne : z ≠ y := by
    intro h
    apply hynon
    simpa [h] using hzyo
  have hxz : (graph K).Adj x z := (graph_adj_iff x z).mpr
    ⟨Ne.symm hzxne, Projectivization.orthogonal_comm.mp hzxo⟩
  have hyz : (graph K).Adj y z := (graph_adj_iff y z).mpr
    ⟨Ne.symm hzyne, Projectivization.orthogonal_comm.mp hzyo⟩
  have hznon : ¬ Projectivization.orthogonal z z := by
    intro hzabs
    have hzX : z ∈ (graph K).neighborFinset x ∩ absolutePoints K :=
      Finset.mem_inter.mpr
        ⟨by simpa using hxz, (mem_absolutePoints K z).mpr hzabs⟩
    have hzY : z ∈ (graph K).neighborFinset y ∩ absolutePoints K :=
      Finset.mem_inter.mpr
        ⟨by simpa using hyz, (mem_absolutePoints K z).mpr hzabs⟩
    exact Finset.disjoint_left.mp hdisj hzX hzY
  exact ⟨z, hznon, hxz, hyz⟩

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

private theorem absoluteNeighborPair_injective_on_low
    (h2 : (2 : K) ≠ 0)
    {x y : {v : P K // v ∉ absolutePoints K}}
    (hx : x ∈ oddCoreLowVertices K)
    (hpairs : absoluteNeighborPair K x.1 = absoluteNeighborPair K y.1) :
    x = y := by
  apply Subtype.ext
  by_contra hxy
  have hcard : (absoluteNeighborPair K x.1).card = 2 := by
    rw [card_absoluteNeighborPair]
    exact (mem_oddSecantVertices K x.1).mp
      ((mem_oddCoreLowVertices_iff_secant K h2 x).mp hx) |>.2
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp hcard
  have hle := Finset.card_le_one.mp (commonNeighbors_le_one x.1 y.1 hxy)
  apply hab
  apply Subtype.ext
  apply hle a.1
  · have haX : a ∈ absoluteNeighborPair K x.1 := by rw [hp]; simp
    have haY : a ∈ absoluteNeighborPair K y.1 := by rw [← hpairs]; exact haX
    simp [(mem_absoluteNeighborPair K x.1 a).mp haX,
      (mem_absoluteNeighborPair K y.1 a).mp haY]
  · have hbX : b ∈ absoluteNeighborPair K x.1 := by rw [hp]; simp
    have hbY : b ∈ absoluteNeighborPair K y.1 := by rw [← hpairs]; exact hbX
    simp [(mem_absoluteNeighborPair K x.1 b).mp hbX,
      (mem_absoluteNeighborPair K y.1 b).mp hbY]

/-- A safe family consisting only of odd-core defects has at most `q`
members.  Under `absoluteNeighborPair` it is an intersecting family of
two-subsets of the `q+1` absolute points, so this is the `r=2` case of the
Erdős--Ko--Rado theorem. -/
theorem safe_lowVertices_card_le (h2 : (2 : K) ≠ 0)
    (S : Finset {v : P K // v ∉ absolutePoints K})
    (hsub : S ⊆ oddCoreLowVertices K)
    (hsafe : CommonNeighborIndependent (oddCore K) S) :
    S.card ≤ Nat.card K := by
  let emb : {v // v ∈ S} ↪ Finset {a : P K // a ∈ absolutePoints K} :=
    ⟨fun v => absoluteNeighborPair K v.1.1, fun x y hxy => by
      apply Subtype.ext
      exact absoluteNeighborPair_injective_on_low K h2
        (hsub x.2) hxy⟩
  let 𝒜 := Finset.univ.map emb
  have h𝒜card : 𝒜.card = S.card := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe]
  have h𝒜sized :
      (𝒜 : Set (Finset {a : P K // a ∈ absolutePoints K})).Sized 2 := by
    intro A hA
    rw [Finset.mem_coe, Finset.mem_map] at hA
    obtain ⟨x, _, rfl⟩ := hA
    dsimp [emb]
    rw [card_absoluteNeighborPair]
    exact (mem_oddSecantVertices K x.1.1).mp
      ((mem_oddCoreLowVertices_iff_secant K h2 x.1).mp (hsub x.2)) |>.2
  have h𝒜int :
      (𝒜 : Set (Finset {a : P K // a ∈ absolutePoints K})).Intersecting := by
    intro A hA B hB hdisj
    rw [Finset.mem_coe, Finset.mem_map] at hA hB
    obtain ⟨x, _, rfl⟩ := hA
    obtain ⟨y, _, rfl⟩ := hB
    dsimp [emb] at hdisj
    by_cases hxy : x.1 = y.1
    · have hp : absoluteNeighborPair K x.1.1 =
          absoluteNeighborPair K y.1.1 := congrArg
            (fun v => absoluteNeighborPair K v.1) hxy
      rw [← hp] at hdisj
      have hcard : (absoluteNeighborPair K x.1.1).card = 2 := by
        rw [card_absoluteNeighborPair]
        exact (mem_oddSecantVertices K x.1.1).mp
          ((mem_oddCoreLowVertices_iff_secant K h2 x.1).mp (hsub x.2)) |>.2
      have hempty := disjoint_self.mp hdisj
      rw [hempty] at hcard
      simp at hcard
    · have hxnon : ¬ Projectivization.orthogonal x.1.1 x.1.1 := by
        simpa [mem_absolutePoints] using x.1.2
      have hynon : ¬ Projectivization.orthogonal y.1.1 y.1.1 := by
        simpa [mem_absolutePoints] using y.1.2
      have hraw : Disjoint
          ((graph K).neighborFinset x.1.1 ∩ absolutePoints K)
          ((graph K).neighborFinset y.1.1 ∩ absolutePoints K) := by
        rw [Finset.disjoint_left] at hdisj ⊢
        intro a haX haY
        let aa : {a : P K // a ∈ absolutePoints K} :=
          ⟨a, (Finset.mem_inter.mp haX).2⟩
        apply hdisj (a := aa)
        · apply (mem_absoluteNeighborPair K x.1.1 aa).mpr
          simpa using (Finset.mem_inter.mp haX).1
        · apply (mem_absoluteNeighborPair K y.1.1 aa).mpr
          simpa using (Finset.mem_inter.mp haY).1
      obtain ⟨z, hznon, hxz, hyz⟩ :=
        exists_nonabsolute_commonNeighbor_of_disjoint_absoluteIncidences
          K x.1.1 y.1.1 hxnon hynon (fun h => hxy (Subtype.ext h)) hraw
      have hzcore : z ∉ absolutePoints K := by
        simpa [mem_absolutePoints] using hznon
      let zc : {v : P K // v ∉ absolutePoints K} := ⟨z, hzcore⟩
      have hzero := hsafe x.2 y.2 hxy
      have hzmem : zc ∈ (oddCore K).neighborFinset x.1 ∩
          (oddCore K).neighborFinset y.1 := by
        apply Finset.mem_inter.mpr
        constructor
        · rw [SimpleGraph.mem_neighborFinset]
          change (graph K).Adj x.1.1 z
          exact hxz
        · rw [SimpleGraph.mem_neighborFinset]
          change (graph K).Adj y.1.1 z
          exact hyz
      rw [Finset.card_eq_zero] at hzero
      have := congrArg (fun T => zc ∈ T) hzero
      simp [hzmem] at this
  have habscard : Fintype.card {a : P K // a ∈ absolutePoints K} =
      Nat.card K + 1 := by
    rw [Fintype.card_coe, card_absolutePoints_eq_card_add_one K]
  have hq3 : 3 ≤ Nat.card K := three_le_card_of_two_ne_zero K h2
  have hbound := pair_intersecting_card_le 𝒜 h𝒜int h𝒜sized (by
    rw [habscard]
    omega)
  rw [h𝒜card, habscard] at hbound
  omega

private noncomputable def starPair
    (a : {a : P K // a ∈ absolutePoints K})
    (b : {b : {a : P K // a ∈ absolutePoints K} // b ≠ a}) :
    AbsolutePairs K := by
  refine ⟨{a.1, b.1.1}, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact a.2
    · exact b.1.2
  · rw [Finset.card_pair]
    intro h
    exact b.2 (Subtype.ext h.symm)

private noncomputable def starVertex
    (a : {a : P K // a ∈ absolutePoints K})
    (b : {b : {a : P K // a ∈ absolutePoints K} // b ≠ a}) :
    {v : P K // v ∉ absolutePoints K} :=
  ⟨pairCommonNeighbor K (starPair K a b), by
    simpa [mem_absolutePoints] using
      (pairCommonNeighbor_spec K (starPair K a b)).2.2⟩

private theorem starVertex_low (h2 : (2 : K) ≠ 0)
    (a : {a : P K // a ∈ absolutePoints K})
    (b : {b : {a : P K // a ∈ absolutePoints K} // b ≠ a}) :
    starVertex K a b ∈ oddCoreLowVertices K := by
  rw [mem_oddCoreLowVertices_iff_secant K h2]
  exact (pairToSecant K h2 (starPair K a b)).2

private noncomputable def starEmbedding (h2 : (2 : K) ≠ 0)
    (a : {a : P K // a ∈ absolutePoints K}) :
    {b : {a : P K // a ∈ absolutePoints K} // b ≠ a} ↪
      {v : P K // v ∉ absolutePoints K} :=
  ⟨starVertex K a, fun b c hbc => by
    have hp : pairToSecant K h2 (starPair K a b) =
        pairToSecant K h2 (starPair K a c) := by
      apply Subtype.ext
      exact congrArg (fun v : {v : P K // v ∉ absolutePoints K} => v.1) hbc
    have hD := pairToSecant_injective K h2 hp
    have hsets : ({a.1, b.1.1} : Finset (P K)) = {a.1, c.1.1} :=
      congrArg Subtype.val hD
    apply Subtype.ext
    apply Subtype.ext
    have hbmem : b.1.1 ∈ ({a.1, c.1.1} : Finset (P K)) := by
      rw [← hsets]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
    exact hbmem.resolve_left (fun h => b.2 (Subtype.ext h))⟩

/-- The `q` secant defects whose absolute-neighbor pairs contain `a`. -/
noncomputable def oddCoreDefectStar (h2 : (2 : K) ≠ 0)
    (a : {a : P K // a ∈ absolutePoints K}) :
    Finset {v : P K // v ∉ absolutePoints K} :=
  Finset.univ.map (starEmbedding K h2 a)

theorem card_oddCoreDefectStar (h2 : (2 : K) ≠ 0)
    (a : {a : P K // a ∈ absolutePoints K}) :
    (oddCoreDefectStar K h2 a).card = Nat.card K := by
  rw [oddCoreDefectStar, Finset.card_map, Finset.card_univ]
  rw [Fintype.card_subtype_compl (fun b :
    {a : P K // a ∈ absolutePoints K} => b = a)]
  simp only [Fintype.card_unique]
  rw [Fintype.card_coe, card_absolutePoints_eq_card_add_one K]
  omega

theorem oddCoreDefectStar_subset_low (h2 : (2 : K) ≠ 0)
    (a : {a : P K // a ∈ absolutePoints K}) :
    oddCoreDefectStar K h2 a ⊆ oddCoreLowVertices K := by
  intro v hv
  rw [oddCoreDefectStar, Finset.mem_map] at hv
  obtain ⟨b, _, rfl⟩ := hv
  exact starVertex_low K h2 a b

private theorem starVertex_adj_center (h2 : (2 : K) ≠ 0)
    (a : {a : P K // a ∈ absolutePoints K})
    (b : {b : {a : P K // a ∈ absolutePoints K} // b ≠ a}) :
    (graph K).Adj (starVertex K a b).1 a.1 := by
  have ha : a.1 ∈ (graph K).neighborFinset
      (pairCommonNeighbor K (starPair K a b)) ∩ absolutePoints K := by
    rw [pair_incidence_eq K h2 (starPair K a b)]
    change a.1 ∈ ({a.1, b.1.1} : Finset (P K))
    simp
  simpa [starVertex] using (Finset.mem_inter.mp ha).1

/-- The defect star is a common-neighbor-independent selector in the odd
core: two of its poles share the deleted center `a`, hence by uniqueness they
cannot share a surviving neighbor. -/
theorem oddCoreDefectStar_safe (h2 : (2 : K) ≠ 0)
    (a : {a : P K // a ∈ absolutePoints K}) :
    CommonNeighborIndependent (oddCore K) (oddCoreDefectStar K h2 a) := by
  intro x hx y hy hxy
  rw [oddCoreDefectStar, Finset.mem_map] at hx hy
  obtain ⟨b, _, rfl⟩ := hx
  obtain ⟨c, _, rfl⟩ := hy
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz' := Finset.mem_inter.mp hz
  have hxz := hz'.1
  have hyz := hz'.2
  rw [SimpleGraph.mem_neighborFinset] at hxz hyz
  change (graph K).Adj (starVertex K a b).1 z.1 at hxz
  change (graph K).Adj (starVertex K a c).1 z.1 at hyz
  have hxyval : (starVertex K a b).1 ≠ (starVertex K a c).1 := by
    intro h
    apply hxy
    exact Subtype.ext h
  have hle := Finset.card_le_one.mp
    (commonNeighbors_le_one (starVertex K a b).1
      (starVertex K a c).1 hxyval)
  have heq := hle a.1
    (by simp [starVertex_adj_center K h2 a b,
      starVertex_adj_center K h2 a c]) z.1 (by simp [hxz, hyz])
  exact z.2 (by
    rw [← heq]
    exact a.2)

/-- The EKR upper bound on safe odd defects is sharp. -/
theorem exists_safe_lowVertices_card_eq (h2 : (2 : K) ≠ 0) :
    ∃ S : Finset {v : P K // v ∉ absolutePoints K},
      S ⊆ oddCoreLowVertices K ∧
      CommonNeighborIndependent (oddCore K) S ∧ S.card = Nat.card K := by
  have habs : (absolutePoints K).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hc := card_absolutePoints_eq_card_add_one K
    rw [hempty] at hc
    simp at hc
  let a : {a : P K // a ∈ absolutePoints K} := ⟨habs.choose, habs.choose_spec⟩
  exact ⟨oddCoreDefectStar K h2 a, oddCoreDefectStar_subset_low K h2 a,
    oddCoreDefectStar_safe K h2 a, card_oddCoreDefectStar K h2 a⟩

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
