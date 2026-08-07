import Proofs.Erdos85Ramsey
import Proofs.Erdos85MinimalWitness
import Proofs.Erdos85ProblemConflict
import Proofs.Erdos85RepairSet
import Proofs.Erdos85SecondOrderStructure
import Proofs.Erdos85LayeredWitness

/-!
# Downward threshold jumps are consecutive Ramsey plateaus

At a fixed order `m`, the largest star size forced against a red `C₄` is
`m - minDegreeForC4 m`.  Hence a downward jump of the minimum-degree
threshold is exactly a jump by at least two in this Ramsey capacity.  This
module packages the equivalence without relying on delicate conventions for
the numerical Ramsey number.
-/

namespace Erdos85

/-- The largest star size predicted by the minimum-degree threshold at order
`m`. -/
noncomputable def c4StarRamseyCapacity (m : ℕ) : ℕ :=
  m - minDegreeForC4 m

/-- Pointwise inverse relation between the threshold and the star-Ramsey
capacity. -/
theorem c4StarRamseyAt_iff_le_capacity {m s : ℕ}
    (hm : 4 ≤ m) (hs : s ≤ m - 1) :
    C4StarRamseyAt m s ↔ s ≤ c4StarRamseyCapacity m := by
  rw [c4StarRamseyAt_iff_threshold hm hs]
  have hf : minDegreeForC4 m ≤ m := by
    exact le_trans (minDegreeForC4_le_sub_one hm) (by omega)
  simp only [c4StarRamseyCapacity]
  omega

/-- One-step monotonicity is equivalent to the Ramsey capacity increasing by
at most one. -/
theorem minDegreeForC4_mono_iff_capacity_succ_le {m : ℕ} (hm : 4 ≤ m) :
    minDegreeForC4 m ≤ minDegreeForC4 (m + 1) ↔
      c4StarRamseyCapacity (m + 1) ≤ c4StarRamseyCapacity m + 1 := by
  have hfm : minDegreeForC4 m ≤ m :=
    le_trans (minDegreeForC4_le_sub_one hm) (by omega)
  have hfms : minDegreeForC4 (m + 1) ≤ m + 1 :=
    le_trans (minDegreeForC4_le_sub_one (by omega)) (by omega)
  simp only [c4StarRamseyCapacity]
  omega

/-- Two consecutive star sizes first become forced when the order rises from
`m` to `m+1`.  This is the convention-free form of a plateau of two
consecutive `C₄`-versus-star Ramsey numbers. -/
def ConsecutiveC4StarPlateauAt (m s : ℕ) : Prop :=
  ¬ C4StarRamseyAt m s ∧
  ¬ C4StarRamseyAt m (s + 1) ∧
  C4StarRamseyAt (m + 1) s ∧
  C4StarRamseyAt (m + 1) (s + 1)

theorem C4StarRamseyAt.starSize_le_sub_one {m s : ℕ}
    (h : C4StarRamseyAt m s) : s ≤ m - 1 := by
  classical
  rcases h (⊥ : SimpleGraph (Fin m)) with hcycle | ⟨v, hv⟩
  · rcases hcycle with ⟨f, hf, hedge⟩
    have h01 := hedge 0 1 (by native_decide)
    simp at h01
  · simpa using hv

/-- **Exact local plateau equivalence.**  The threshold drops at `m+1` if
and only if two consecutive star parameters have their first Ramsey guarantee
at that same order. -/
theorem minDegreeForC4_drop_iff_consecutiveRamseyPlateau
    {m : ℕ} (hm : 4 ≤ m) :
    minDegreeForC4 (m + 1) < minDegreeForC4 m ↔
      ∃ s, ConsecutiveC4StarPlateauAt m s := by
  have hfm2 : 2 ≤ minDegreeForC4 m :=
    by
      have h := two_le_minDegreeForC4 (n := m - 1) (by omega)
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using h
  have hfms2 : 2 ≤ minDegreeForC4 (m + 1) :=
    two_le_minDegreeForC4 (by omega)
  have hfmle : minDegreeForC4 m ≤ m - 1 :=
    minDegreeForC4_le_sub_one hm
  have hfmsle : minDegreeForC4 (m + 1) ≤ m := by
    simpa using minDegreeForC4_le_sub_one (n := m + 1) (by omega)
  let c := c4StarRamseyCapacity m
  constructor
  · intro hdrop
    have hcap : c + 2 ≤ c4StarRamseyCapacity (m + 1) := by
      simp only [c, c4StarRamseyCapacity]
      omega
    have hc : c + 2 ≤ m := by
      dsimp [c, c4StarRamseyCapacity]
      omega
    refine ⟨c + 1, ?_⟩
    constructor
    · intro hAt
      have hfit := hAt.starSize_le_sub_one
      have hle := (c4StarRamseyAt_iff_le_capacity hm hfit).1 hAt
      simp [c] at hle
    constructor
    · intro hAt
      have hfit := hAt.starSize_le_sub_one
      have hle := (c4StarRamseyAt_iff_le_capacity hm hfit).1 hAt
      simp [c] at hle
    constructor
    · rw [c4StarRamseyAt_iff_le_capacity (by omega) (by omega)]
      omega
    · rw [c4StarRamseyAt_iff_le_capacity (by omega) (by omega)]
      omega
  · rintro ⟨s, hs⟩
    rcases hs with ⟨hnot, hnotSucc, hyes, hyesSucc⟩
    have hsle : s + 1 ≤ m := by
      simpa using hyesSucc.starSize_le_sub_one
    have hcapOldUpper : c4StarRamseyCapacity m ≤ m - 2 := by
      simp only [c4StarRamseyCapacity]
      omega
    have hcapOld : c4StarRamseyCapacity m < s := by
      by_contra h
      have hlecap : s ≤ c4StarRamseyCapacity m := Nat.le_of_not_gt h
      have hfit : s ≤ m - 1 := by omega
      exact hnot ((c4StarRamseyAt_iff_le_capacity hm hfit).2 hlecap)
    have hcapNew : s + 1 ≤ c4StarRamseyCapacity (m + 1) :=
      (c4StarRamseyAt_iff_le_capacity (by omega) (by omega)).1 hyesSucc
    simp only [c4StarRamseyCapacity] at hcapOld hcapNew
    omega

/-- **Global Ramsey-plateau reformulation of Erdős 85.**  Eventual
monotonicity holds exactly when, eventually, no two consecutive star sizes
first become forced at one and the same order. -/
theorem erdos85Question_iff_eventually_no_consecutiveRamseyPlateau :
    Erdos85Question ↔
      ∀ᶠ m in Filter.atTop, ¬ ∃ s, ConsecutiveC4StarPlateauAt m s := by
  constructor
  · intro hmono
    filter_upwards [hmono, Filter.eventually_ge_atTop 4] with m hmstep hm
    intro hplateau
    have hdrop :=
      (minDegreeForC4_drop_iff_consecutiveRamseyPlateau hm).2 hplateau
    omega
  · intro hplateau
    filter_upwards [hplateau, Filter.eventually_ge_atTop 4] with m hnone hm
    by_contra hmono
    have hdrop : minDegreeForC4 (m + 1) < minDegreeForC4 m := by omega
    exact hnone
      ((minDegreeForC4_drop_iff_consecutiveRamseyPlateau hm).1 hdrop)

/-- The negation is the existence of arbitrarily large consecutive Ramsey
plateaus. -/
theorem erdos85Negation_iff_arbitrarily_large_consecutiveRamseyPlateau :
    Erdos85Negation ↔
      ∀ N : ℕ, ∃ m ≥ N, ∃ s, ConsecutiveC4StarPlateauAt m s := by
  constructor
  · intro hneg N
    obtain ⟨m, hmN, hdrop⟩ := hneg (max N 4)
    refine ⟨m, le_trans (Nat.le_max_left N 4) hmN, ?_⟩
    exact (minDegreeForC4_drop_iff_consecutiveRamseyPlateau
      (le_trans (Nat.le_max_right N 4) hmN)).1 hdrop
  · intro hplateau N
    obtain ⟨m, hmN, s, hs⟩ := hplateau (max N 4)
    refine ⟨m, le_trans (Nat.le_max_left N 4) hmN, ?_⟩
    exact (minDegreeForC4_drop_iff_consecutiveRamseyPlateau
      (le_trans (Nat.le_max_right N 4) hmN)).2 ⟨s, hs⟩

/-- An edge-minimal graph-theoretic core for a one-step drop.  Its degree-`d`
vertices cover every edge, and degree `d` is already impossible after adding
one vertex. -/
def C4PlateauCore (m d : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
    G.minDegree = d ∧
    ¬ containsC4 (Fin m) G ∧
    (∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
    ∀ (H : SimpleGraph (Fin (m + 1))) (_ : DecidableRel H.Adj),
      d ≤ H.minDegree → containsC4 (Fin (m + 1)) H

/-- A downward jump is equivalent to the existence of an edge-minimal
plateau core at some degree. -/
theorem minDegreeForC4_drop_iff_exists_plateauCore
    {m : ℕ} (hm : 4 ≤ m) :
    minDegreeForC4 (m + 1) < minDegreeForC4 m ↔
      ∃ d, C4PlateauCore m d := by
  constructor
  · intro hdrop
    letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    let d := minDegreeForC4 (m + 1)
    have hd : 1 ≤ d := by
      have htwo := two_le_minDegreeForC4 (n := m) (by omega)
      dsimp [d]
      omega
    have hw : C4FreeMinDegreeWitness m d :=
      (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hm).2 hdrop
    obtain ⟨G, hdec, hmin, hfree⟩ := hw
    letI : DecidableRel G.Adj := hdec
    obtain ⟨K, hKdec, hKmin, hKfree, hKcover⟩ :=
      exists_c4Free_edgeCovered_minDegree_eq G hd hmin hfree
    refine ⟨d, K, hKdec, hKmin, hKfree, ?_, ?_⟩
    · intro u v huv
      exact hKcover huv
    intro H hHdec hHmin
    by_contra hHfree
    have hwH : C4FreeMinDegreeWitness (m + 1) d :=
      ⟨H, hHdec, hHmin, hHfree⟩
    have hlt :=
      (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).1 hwH
    exact (Nat.lt_irrefl d) hlt
  · rintro ⟨d, G, hdec, hmin, hfree, hcover, hnext⟩
    have hw : C4FreeMinDegreeWitness m d :=
      ⟨G, hdec, hmin.ge, hfree⟩
    have hdlt : d < minDegreeForC4 m :=
      (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hm).1 hw
    have hnextle : minDegreeForC4 (m + 1) ≤ d := by
      by_contra hnot
      have hdnext : d < minDegreeForC4 (m + 1) := by omega
      obtain ⟨H, hHdec, hHmin, hHfree⟩ :=
        (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).2 hdnext
      exact hHfree (hnext H hHdec hHmin)
    omega

/-- **Canonical core reduction.**  The existential degree in the preceding
theorem can be fixed to the new forcing threshold itself. -/
theorem minDegreeForC4_drop_iff_threshold_plateauCore
    {m : ℕ} (hm : 4 ≤ m) :
    minDegreeForC4 (m + 1) < minDegreeForC4 m ↔
      C4PlateauCore m (minDegreeForC4 (m + 1)) := by
  constructor
  · intro hdrop
    letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    let d := minDegreeForC4 (m + 1)
    have hd : 1 ≤ d := by
      have htwo := two_le_minDegreeForC4 (n := m) (by omega)
      dsimp [d]
      omega
    have hw : C4FreeMinDegreeWitness m d :=
      (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hm).2 hdrop
    obtain ⟨G, hdec, hmin, hfree⟩ := hw
    letI : DecidableRel G.Adj := hdec
    obtain ⟨K, hKdec, hKmin, hKfree, hKcover⟩ :=
      exists_c4Free_edgeCovered_minDegree_eq G hd hmin hfree
    refine ⟨K, hKdec, hKmin, hKfree, ?_, ?_⟩
    · intro u v huv
      exact hKcover huv
    · intro H hHdec hHmin
      by_contra hHfree
      have hwH : C4FreeMinDegreeWitness (m + 1) d :=
        ⟨H, hHdec, hHmin, hHfree⟩
      have hlt :=
        (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).1 hwH
      exact (Nat.lt_irrefl d) hlt
  · intro hcore
    exact (minDegreeForC4_drop_iff_exists_plateauCore hm).2
      ⟨minDegreeForC4 (m + 1), hcore⟩

theorem C4PlateauCore.threshold_bounds {m d : ℕ} (hm : 4 ≤ m)
    (hcore : C4PlateauCore m d) :
    d < minDegreeForC4 m ∧ minDegreeForC4 (m + 1) ≤ d := by
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  have hw : C4FreeMinDegreeWitness m d :=
    ⟨G, hdec, hmin.ge, hfree⟩
  refine ⟨(c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hm).1 hw, ?_⟩
  by_contra hnot
  have hdnext : d < minDegreeForC4 (m + 1) := by omega
  obtain ⟨H, hHdec, hHmin, hHfree⟩ :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).2 hdnext
  exact hHfree (hnext H hHdec hHmin)

/-- Every plateau core at a nondegenerate order has degree at least two. -/
theorem C4PlateauCore.two_le_degree {m d : ℕ} (hm : 4 ≤ m)
    (hcore : C4PlateauCore m d) : 2 ≤ d := by
  have htwo : 2 ≤ minDegreeForC4 (m + 1) :=
    two_le_minDegreeForC4 (n := m) (by omega)
  exact htwo.trans (hcore.threshold_bounds hm).2

/-- A plateau core has no safe attachment set of size `d`: equivalently, its
common-neighbour conflict graph has independence number strictly below `d`.
This is the finite extremal obstruction that must be eliminated to prove
one-step monotonicity. -/
theorem C4PlateauCore.conflict_indepNum_lt {m d : ℕ}
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin m) G ∧
      (∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
      (commonNeighborConflict G).indepNum < d := by
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, hcover, ?_⟩
  by_contra hnot
  have hind : d ≤ (commonNeighborConflict G).indepNum := by omega
  obtain ⟨H, hHdec, hHmin, hHfree⟩ :=
    c4FreeMinDegreeWitness_succ_of_conflict_indepNum
      G hmin.ge hfree hind
  exact hHfree (hnext H hHdec hHmin)

/-- A plateau core defeats the canonical delete-one/add-an-adjacent-pair
surgery at every center.  Thus it has no repair set in the sense of
`Erdos85RepairSet`. -/
theorem C4PlateauCore.not_hasRepairSet {m d : ℕ} (hm : 4 ≤ m)
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin m) G ∧
      (∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
      ¬ HasRepairSet G d := by
  have hd : 1 ≤ d := by have := hcore.two_le_degree hm; omega
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, hcover, ?_⟩
  rintro ⟨x, R, hRcard, hRsafe, hinter, hcross⟩
  have hw := c4FreeMinDegreeWitness_delete_add_pair_of_repairSet
    G x (n := m - 1) (d := d) (by simp; omega) hd hmin.ge hfree R
      hRcard hRsafe hinter hcross
  have hw' : C4FreeMinDegreeWitness (m + 1) d := by
    convert hw using 1 <;> omega
  obtain ⟨H, hHdec, hHmin, hHfree⟩ := hw'
  exact hHfree (hnext H hHdec hHmin)

/-- Edge-minimal plateau cores have a strict majority of tight vertices.  In
addition to being a vertex cover, the degree-`d` layer is larger than the
entire above-minimum layer. -/
theorem C4PlateauCore.exists_tight_majority_core {m d : ℕ} (hm : 4 ≤ m)
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin m) G ∧
      (∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
      (aboveMinVertices G d).card < (tightVertices G d).card ∧
      (aboveMinVertices G d).card * (d + 1).choose 2 ≤
        (tightVertices G d).card.choose 2 := by
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hcover' : ∀ {u v : Fin m}, G.Adj u v →
      G.degree u = d ∨ G.degree v = d := by
    intro u v huv
    exact hcover huv
  have hmajor := card_aboveMin_lt_card_tight G (d := d) hmin
    (fun {u v} huv => hcover' (u := u) (v := v) huv)
  have hcherry := card_aboveMin_mul_choose_succ_le_choose_card_tight
    G (d := d) hfree (fun {u v} huv => hcover' (u := u) (v := v) huv)
  exact ⟨G, hdec, hmin, hfree, hcover', hmajor, hcherry⟩

/-- Moore localization: a plateau core of degree at least three cannot occur
before the second strict Moore layer. -/
theorem C4PlateauCore.second_strict_moore_lower {m d : ℕ}
    (hcore : C4PlateauCore m d) (hd : 3 ≤ d) :
    d * (d - 1) + 3 ≤ m := by
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  have hm : 0 < m := by
    by_contra hzero
    have hm0 : m = 0 := by omega
    subst m
    simp at hmin
    omega
  letI : Nonempty (Fin m) :=
    Fintype.card_pos_iff.mp (by simpa using hm)
  simpa using second_strict_moore_bound G hfree hd hmin.ge

/-- Below the next asymmetric Moore layer, every plateau core can be chosen
regular. -/
theorem C4PlateauCore.exists_regular_core {m d : ℕ}
    (hm : 4 ≤ m) (hcore : C4PlateauCore m d)
    (hsize : m < (d + 1) * (d - 1) + 1) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      ¬ containsC4 (Fin m) G ∧
      (∀ x, G.degree x = d) ∧
      ∀ (H : SimpleGraph (Fin (m + 1))) (_ : DecidableRel H.Adj),
        d ≤ H.minDegree → containsC4 (Fin (m + 1)) H := by
  have hd : 2 ≤ d := hcore.two_le_degree hm
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hfree, ?_, hnext⟩
  exact regular_of_minDegree_card_lt_nextMooreLayer
    G hfree hd hmin.ge (by simpa using hsize)

/-- Global core reformulation: Erdős 85 asks exactly whether edge-minimal
plateau cores eventually disappear. -/
theorem erdos85Question_iff_eventually_no_plateauCore :
    Erdos85Question ↔
      ∀ᶠ m in Filter.atTop, ¬ ∃ d, C4PlateauCore m d := by
  constructor
  · intro hmono
    filter_upwards [hmono, Filter.eventually_ge_atTop 4] with m hmstep hm
    intro hcore
    have hdrop := (minDegreeForC4_drop_iff_exists_plateauCore hm).2 hcore
    omega
  · intro hcore
    filter_upwards [hcore, Filter.eventually_ge_atTop 4] with m hnone hm
    by_contra hmono
    have hdrop : minDegreeForC4 (m + 1) < minDegreeForC4 m := by omega
    exact hnone ((minDegreeForC4_drop_iff_exists_plateauCore hm).1 hdrop)

/-- Canonical global core reformulation, with the degree fixed pointwise to
the threshold at the larger order. -/
theorem erdos85Question_iff_eventually_no_threshold_plateauCore :
    Erdos85Question ↔
      ∀ᶠ m in Filter.atTop,
        ¬ C4PlateauCore m (minDegreeForC4 (m + 1)) := by
  constructor
  · intro hmono
    filter_upwards [hmono, Filter.eventually_ge_atTop 4] with m hmstep hm
    intro hcore
    have hdrop :=
      (minDegreeForC4_drop_iff_threshold_plateauCore hm).2 hcore
    omega
  · intro hcore
    filter_upwards [hcore, Filter.eventually_ge_atTop 4] with m hnone hm
    by_contra hmono
    have hdrop : minDegreeForC4 (m + 1) < minDegreeForC4 m := by omega
    exact hnone
      ((minDegreeForC4_drop_iff_threshold_plateauCore hm).1 hdrop)

/-- The negation is equivalently the existence of arbitrarily large
canonical threshold cores. -/
theorem erdos85Negation_iff_arbitrarily_large_threshold_plateauCore :
    Erdos85Negation ↔
      ∀ N : ℕ, ∃ m ≥ N,
        C4PlateauCore m (minDegreeForC4 (m + 1)) := by
  constructor
  · intro hneg N
    obtain ⟨m, hmN, hdrop⟩ := hneg (max N 4)
    refine ⟨m, le_trans (Nat.le_max_left N 4) hmN, ?_⟩
    exact (minDegreeForC4_drop_iff_threshold_plateauCore
      (le_trans (Nat.le_max_right N 4) hmN)).1 hdrop
  · intro hcore N
    obtain ⟨m, hmN, hmcore⟩ := hcore (max N 4)
    refine ⟨m, le_trans (Nat.le_max_left N 4) hmN, ?_⟩
    exact (minDegreeForC4_drop_iff_threshold_plateauCore
      (le_trans (Nat.le_max_right N 4) hmN)).2 hmcore

/-- At the first possible order allowed by the parity-free strict Moore
bound, a plateau core cannot have odd degree. -/
theorem not_C4PlateauCore_secondOrder_of_odd {d : ℕ}
    (hd : 4 ≤ d) (hodd : Odd d) :
    ¬ C4PlateauCore (d * (d - 1) + 3) d := by
  rintro ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  apply hfree
  exact containsC4_of_odd_secondOrder G hd hodd hmin.ge (by simp)

end Erdos85
