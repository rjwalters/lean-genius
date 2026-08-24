import Proofs.Erdos85DyadicStoppingSupportZeroCommonPairSqueeze

/-!
# Excess-incidence correction to the dyadic cherry squeeze

The uniform-minimum cherry bound forgets that the total incidence into the
marked support is exactly `q|B|`.  Once every center has a baseline service
degree, each incidence above baseline creates at least the smaller baseline
number of additional cherries.  This yields a genuinely stronger,
nonuniform two-shore constraint.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Raising a degree above `L` creates at least `m` new pairs per added
incidence whenever `m ≤ L`. -/
theorem choose_two_add_mul_le_choose_two_add_mul
    {m L d : ℕ} (hm : m ≤ L) (hLd : L ≤ d) :
    L.choose 2 + m * d ≤ d.choose 2 + m * L := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLd
  clear hLd
  induction k with
  | zero => simp
  | succ k ih =>
      have hrec : (L + (k + 1)).choose 2 =
          (L + k) + (L + k).choose 2 := by
        rw [show L + (k + 1) = (L + k) + 1 by omega,
          Nat.choose_succ_succ]
        simp
      have hmul : m * (L + (k + 1)) = m * (L + k) + m := by ring
      rw [hrec, hmul]
      omega

/-- The next discrete-convex layer: after the first incidence above `L`,
each further incidence creates at least one additional pair beyond the
linear `m`-charge. -/
theorem choose_two_add_mul_add_tail_le
    {m L d : ℕ} (hm : m ≤ L) (hLd : L ≤ d) :
    L.choose 2 + m * d + (d - L - 1) ≤ d.choose 2 + m * L := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLd
  clear hLd
  induction k with
  | zero => simp
  | succ k ih =>
      have hrec : (L + (k + 1)).choose 2 =
          (L + k) + (L + k).choose 2 := by
        rw [show L + (k + 1) = (L + k) + 1 by omega,
          Nat.choose_succ_succ]
        simp
      have hmul : m * (L + (k + 1)) = m * (L + k) + m := by ring
      rw [hrec, hmul]
      omega

/-- Generic excess-incidence cherry consumer for two disjoint center
populations.  The exact total `R` strengthens the baseline pair cost by
`m` times every incidence above baseline, and discrete convexity charges
one more pair for every excess incidence beyond the first at each center. -/
theorem c4Free_disjoint_subset_service_excessIncidence_cherry_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (S T B : Finset V) (F : Finset (Finset V)) (L M m R : ℕ)
    (hmL : m ≤ L) (hmM : m ≤ M)
    (hF : F ⊆ B.powersetCard 2)
    (hforbid : ∀ U ∈ F, ∀ x : V, ¬ U ⊆ G.neighborFinset x)
    (hdisj : Disjoint S T)
    (hserviceS : ∀ p ∈ S, L ≤ (G.neighborFinset p ∩ B).card)
    (hserviceT : ∀ p ∈ T, M ≤ (G.neighborFinset p ∩ B).card)
    (htotal :
      (∑ p ∈ S, (G.neighborFinset p ∩ B).card) +
        (∑ p ∈ T, (G.neighborFinset p ∩ B).card) = R) :
    S.card * L.choose 2 + T.card * M.choose 2 +
        m * (R - (S.card * L + T.card * M)) +
        ((R - (S.card * L + T.card * M)) - (S.card + T.card)) ≤
      B.card.choose 2 - F.card := by
  let d : V → ℕ := fun p => (G.neighborFinset p ∩ B).card
  have hS : S.card * L.choose 2 +
      m * (∑ p ∈ S, d p) + ∑ p ∈ S, (d p - L - 1) ≤
      (∑ p ∈ S, (d p).choose 2) + m * (S.card * L) := by
    calc
      S.card * L.choose 2 + m * (∑ p ∈ S, d p) +
          ∑ p ∈ S, (d p - L - 1) =
          ∑ p ∈ S, (L.choose 2 + m * d p + (d p - L - 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        simp
      _ ≤ ∑ p ∈ S, ((d p).choose 2 + m * L) := by
        apply Finset.sum_le_sum
        intro p hp
        exact choose_two_add_mul_add_tail_le
          hmL (hserviceS p hp)
      _ = (∑ p ∈ S, (d p).choose 2) + m * (S.card * L) := by
        rw [Finset.sum_add_distrib]
        simp
        ring
  have hT : T.card * M.choose 2 +
      m * (∑ p ∈ T, d p) + ∑ p ∈ T, (d p - M - 1) ≤
      (∑ p ∈ T, (d p).choose 2) + m * (T.card * M) := by
    calc
      T.card * M.choose 2 + m * (∑ p ∈ T, d p) +
          ∑ p ∈ T, (d p - M - 1) =
          ∑ p ∈ T, (M.choose 2 + m * d p + (d p - M - 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        simp
      _ ≤ ∑ p ∈ T, ((d p).choose 2 + m * M) := by
        apply Finset.sum_le_sum
        intro p hp
        exact choose_two_add_mul_add_tail_le
          hmM (hserviceT p hp)
      _ = (∑ p ∈ T, (d p).choose 2) + m * (T.card * M) := by
        rw [Finset.sum_add_distrib]
        simp
        ring
  have hLower :
      S.card * L.choose 2 + T.card * M.choose 2 + m * R +
          ((∑ p ∈ S, (d p - L - 1)) +
            ∑ p ∈ T, (d p - M - 1)) ≤
        ((∑ p ∈ S, (d p).choose 2) +
          ∑ p ∈ T, (d p).choose 2) +
        m * (S.card * L + T.card * M) := by
    rw [← htotal]
    calc
      S.card * L.choose 2 + T.card * M.choose 2 +
          m * ((∑ p ∈ S, d p) + ∑ p ∈ T, d p) +
          ((∑ p ∈ S, (d p - L - 1)) +
            ∑ p ∈ T, (d p - M - 1)) =
        (S.card * L.choose 2 + m * (∑ p ∈ S, d p) +
          ∑ p ∈ S, (d p - L - 1)) +
          (T.card * M.choose 2 + m * (∑ p ∈ T, d p) +
            ∑ p ∈ T, (d p - M - 1)) := by ring
      _ ≤ ((∑ p ∈ S, (d p).choose 2) + m * (S.card * L)) +
          ((∑ p ∈ T, (d p).choose 2) + m * (T.card * M)) :=
        Nat.add_le_add hS hT
      _ = ((∑ p ∈ S, (d p).choose 2) +
          ∑ p ∈ T, (d p).choose 2) +
        m * (S.card * L + T.card * M) := by ring
  have hbase : S.card * L + T.card * M ≤ R := by
    rw [← htotal]
    apply Nat.add_le_add
    · calc
        S.card * L = ∑ _p ∈ S, L := by simp
        _ ≤ ∑ p ∈ S, d p := by
          apply Finset.sum_le_sum
          intro p hp
          exact hserviceS p hp
    · calc
        T.card * M = ∑ _p ∈ T, M := by simp
        _ ≤ ∑ p ∈ T, d p := by
          apply Finset.sum_le_sum
          intro p hp
          exact hserviceT p hp
  have hexpand : m * R =
      m * (S.card * L + T.card * M) +
        m * (R - (S.card * L + T.card * M)) := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hbase]
  rw [hexpand] at hLower
  have hTailS :
      (∑ p ∈ S, d p) ≤
        S.card * L + S.card + ∑ p ∈ S, (d p - L - 1) := by
    calc
      (∑ p ∈ S, d p) ≤
          ∑ p ∈ S, (L + 1 + (d p - L - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have := hserviceS p hp
        omega
      _ = S.card * L + S.card + ∑ p ∈ S, (d p - L - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp
  have hTailT :
      (∑ p ∈ T, d p) ≤
        T.card * M + T.card + ∑ p ∈ T, (d p - M - 1) := by
    calc
      (∑ p ∈ T, d p) ≤
          ∑ p ∈ T, (M + 1 + (d p - M - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have := hserviceT p hp
        omega
      _ = T.card * M + T.card + ∑ p ∈ T, (d p - M - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp
  have hTail :
      (R - (S.card * L + T.card * M)) - (S.card + T.card) ≤
        (∑ p ∈ S, (d p - L - 1)) +
          ∑ p ∈ T, (d p - M - 1) := by
    have hsum := Nat.add_le_add hTailS hTailT
    rw [htotal] at hsum
    have hRexpand : R = (S.card * L + T.card * M) +
        (R - (S.card * L + T.card * M)) :=
      (Nat.add_sub_of_le hbase).symm
    rw [hRexpand] at hsum
    omega
  have hlocal :
      S.card * L.choose 2 + T.card * M.choose 2 +
          m * (R - (S.card * L + T.card * M)) +
          ((R - (S.card * L + T.card * M)) - (S.card + T.card)) ≤
        (∑ p ∈ S, (d p).choose 2) +
          ∑ p ∈ T, (d p).choose 2 := by
    omega
  refine hlocal.trans ?_
  calc
    (∑ p ∈ S, (d p).choose 2) +
        ∑ p ∈ T, (d p).choose 2 =
      ∑ p ∈ S ∪ T, (d p).choose 2 := by rw [sum_union hdisj]
    _ ≤ ∑ p : V, (d p).choose 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ ≤ B.card.choose 2 - F.card := by
      dsimp [d]
      exact sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
        G hfree B F hF hforbid

/-- **Nonuniform dyadic squeeze.**  In addition to the two baseline service
costs, every incidence required by the exact identity `q|B|` above those
baselines costs at least their smaller value in the pair budget.  Excess
beyond one incidence per ambient center pays an additional unit. -/
theorem c4Free_dyadicStoppingSupport_twoShore_excessIncidence_cherry_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    let L := dyadicStoppingServiceMinimum q S.card j
    let M := dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j
    let B := dyadicOccupancySupport G S j
    S.card * L.choose 2 + (Sᶜ : Finset V).card * M.choose 2 +
        min L M *
          (q * B.card - (S.card * L + (Sᶜ : Finset V).card * M)) +
        ((q * B.card - (S.card * L + (Sᶜ : Finset V).card * M)) -
          Fintype.card V) ≤
      B.card.choose 2 - (zeroCommonNeighborPairs G B).card := by
  dsimp only
  rw [← secondOrderDefectPairs_eq_zeroCommonNeighborPairs G hfree]
  have hajq : 2 ^ j ∣ q := by
    obtain ⟨u, hu⟩ := hqdiv
    refine ⟨2 * u, ?_⟩
    rw [hu, pow_succ]
    ring
  have hdivc : ∀ v, 2 ^ j ∣
      (G.neighborFinset v ∩ (Sᶜ : Finset V)).card :=
    dvd_complement_occupancy G hreg S (by positivity) hajq hdiv
  have hsupport : dyadicOccupancySupport G (Sᶜ : Finset V) j =
      dyadicOccupancySupport G S j :=
    dyadicOccupancySupport_compl G hreg S j hdiv hqdiv
  have hcardPartition : S.card + (Sᶜ : Finset V).card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ S)
  rw [← hcardPartition]
  apply c4Free_disjoint_subset_service_excessIncidence_cherry_le
    G hfree S (Sᶜ : Finset V) (dyadicOccupancySupport G S j)
    (secondOrderDefectPairs G (dyadicOccupancySupport G S j))
    (dyadicStoppingServiceMinimum q S.card j)
    (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j)
    (min (dyadicStoppingServiceMinimum q S.card j)
      (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j))
    (q * (dyadicOccupancySupport G S j).card)
    (min_le_left _ _) (min_le_right _ _)
    (secondOrderDefectPairs_subset_powersetCard G
      (dyadicOccupancySupport G S j))
    (secondOrderDefectPairs_forbidden_commonNeighbor G hfree
      (dyadicOccupancySupport G S j))
    (by
      rw [Finset.disjoint_left]
      intro x hxS hxSc
      exact (Finset.mem_compl.mp hxSc) hxS)
  · intro p hp
    exact c4Free_dyadicStoppingSupport_degree_ge_serviceMinimum
      G hfree hreg S j hdiv p hp
  · intro p hp
    rw [← hsupport]
    exact c4Free_dyadicStoppingSupport_degree_ge_serviceMinimum
      G hfree hreg (Sᶜ : Finset V) j hdivc p hp
  · exact regular_shore_compl_incidence_sum G hreg S
      (dyadicOccupancySupport G S j)

end

end Erdos85

#print axioms Erdos85.choose_two_add_mul_le_choose_two_add_mul
#print axioms Erdos85.choose_two_add_mul_add_tail_le
#print axioms Erdos85.c4Free_dyadicStoppingSupport_twoShore_excessIncidence_cherry_squeeze
