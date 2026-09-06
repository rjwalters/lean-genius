import Proofs.Erdos85BinarySquareRegularParity

/-!
# The signed joint eigenvector with `μ = 1` on a size-two defect component

At order 64 (`q = 8`), let `c` be a size-two defect component (16 vertices)
carrying a `±1`-valued vector `v` (zero off `c`) which is an eigenvector of the
internal ambient 2-factor `H = A[c]` with eigenvalue `−2` and of the defect
graph `D` with eigenvalue `μ = 1`. Connected bipartite `H` supplies a
joint eigenline by commutation and negative-eigenline rigidity, but does
not force its defect eigenvalue to be `1`; that value is a separate
hypothesis here. For a
disconnected union of even cycles, commutation only preserves the whole
multi-dimensional `−2` eigenspace; producing a global `±1` joint eigenvector
is a separate hypothesis, exactly as reflected in the theorem statement.

Then `w := A v − (−2) v` is supported off `c` with values in `{−2, 0, 2}`, and
`A w = (q − 5 − μ) v + 2 w = 2 v + 2 w`.  Reading this at a vertex `u` with
`w u = 2` shows that `u` has at least two neighbours with `w = 2`; reading it at
a vertex `z` of `c` with `v z = 1` shows `z` has exactly one neighbour with
`w = 2`, and every `w = 2` vertex has both of its neighbours in `c` on the side
`v = 1`.  Hence `#{w = 2} = 8/2 = 4`, and the four vertices with `w = 2` span a
graph of minimum degree `≥ 2` on four vertices — which contains a `C₄`.

So `μ = 1` is impossible whenever the displayed signed joint eigenvector has
been produced. This kills the `μ = 1` subcase of the connected-internal
branch at `q = 8`, not its other joint eigenvalues or a general-`q` branch.
Disconnected even-cycle factors still require a production argument.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Double counting over adjacent ordered pairs between two finsets. -/
theorem sum_sum_filter_neighborFinset_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (f : V → V → ℤ) :
    ∑ x ∈ A, ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ B), f x y =
      ∑ y ∈ B, ∑ x ∈ (G.neighborFinset y).filter (fun x => x ∈ A), f x y := by
  calc
    ∑ x ∈ A, ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ B), f x y
        = ∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then f x y else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          have : (G.neighborFinset x).filter (fun y => y ∈ B) =
              B.filter (fun y => G.Adj x y) := by
            ext y
            simp only [Finset.mem_filter, mem_neighborFinset]
            exact and_comm
          rw [this, Finset.sum_filter]
    _ = ∑ y ∈ B, ∑ x ∈ A, if G.Adj x y then f x y else 0 := Finset.sum_comm
    _ = ∑ y ∈ B, ∑ x ∈ (G.neighborFinset y).filter (fun x => x ∈ A), f x y := by
          apply Finset.sum_congr rfl
          intro y _
          have : (G.neighborFinset y).filter (fun x => x ∈ A) =
              A.filter (fun x => G.Adj x y) := by
            ext x
            simp only [Finset.mem_filter, mem_neighborFinset]
            rw [G.adj_comm]
            exact and_comm
          rw [this, Finset.sum_filter]

/-- A `C₄`-free graph has no four-vertex set of minimum induced degree two. -/
theorem not_containsC4_no_four_set_min_degree_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : ¬ containsC4 V G)
    (S : Finset V) (hS : S.card = 4)
    (hdeg : ∀ u ∈ S, 2 ≤ ((G.neighborFinset u).filter (fun y => y ∈ S)).card) : False := by
  -- pick `u ∈ S` and two of its neighbours `a ≠ b` in `S`
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hS]; norm_num
  obtain ⟨u, hu⟩ := hSne
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (show 1 < ((G.neighborFinset u).filter (fun y => y ∈ S)).card by have := hdeg u hu; omega)
  rw [Finset.mem_filter, mem_neighborFinset] at ha hb
  have hua : G.Adj u a := ha.1
  have hub : G.Adj u b := hb.1
  have haS : a ∈ S := ha.2
  have hbS : b ∈ S := hb.2
  have hau : a ≠ u := (G.ne_of_adj hua).symm
  have hbu : b ≠ u := (G.ne_of_adj hub).symm
  -- the fourth vertex `d`
  have hcard3 : ({u, a, b} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hau.symm, hbu.symm⟩
  have hsub : ({u, a, b} : Finset V) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hdiff : (S \ {u, a, b}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hS, hcard3]
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hdiff
  have hdmem : d ∈ S \ {u, a, b} := by rw [hd]; exact Finset.mem_singleton_self d
  rw [Finset.mem_sdiff] at hdmem
  have hdS : d ∈ S := hdmem.1
  have hdu : d ≠ u := fun h => hdmem.2 (by simp [h])
  have hda : d ≠ a := fun h => hdmem.2 (by simp [h])
  have hdb : d ≠ b := fun h => hdmem.2 (by simp [h])
  -- `S = {u, a, b, d}`
  have hSeq : S = {u, a, b, d} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [hS]
      have : ({u, a, b, d} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_pair hdb.symm]
        · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
          exact ⟨hab, hda.symm⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
          exact ⟨hau.symm, hbu.symm, hdu.symm⟩
      rw [this]
  -- two common neighbours are impossible
  have hcommon : ∀ x y : V, x ≠ y → ∀ p q : V, p ≠ q →
      G.Adj x p → G.Adj y p → G.Adj x q → G.Adj y q → False := by
    intro x y hxy p q hpq hxp hyp hxq hyq
    have hle := common_le_one_of_not_containsC4 hfree x y hxy
    have h2 : 1 < (G.neighborFinset x ∩ G.neighborFinset y).card := by
      apply Finset.one_lt_card.mpr
      refine ⟨p, ?_, q, ?_, hpq⟩ <;> simp [mem_neighborFinset, *]
    omega
  -- neighbourhood of `d` inside `S`
  have hdegd := hdeg d hdS
  have hNd : (G.neighborFinset d).filter (fun y => y ∈ S) ⊆ {u, a, b} := by
    intro x hx
    rw [Finset.mem_filter, mem_neighborFinset] at hx
    rw [hSeq] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h.symm (G.ne_of_adj hx.1)
  by_cases hda' : G.Adj d a <;> by_cases hdb' : G.Adj d b
  · -- `a, b` are common neighbours of `u` and `d`
    exact hcommon u d hdu.symm a b hab hua hda' hub hdb'
  · -- `d ~ a`, `d ≁ b`: then `d ~ u`, `b ~ a`, and `b, d` are common nbrs of `u, a`
    have hdu' : G.Adj d u := by
      by_contra hne
      have : (G.neighborFinset d).filter (fun y => y ∈ S) ⊆ {a} := by
        intro x hx
        have hx' := hNd hx
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
        rcases hx' with rfl | rfl | rfl
        · exact absurd hx.1 hne
        · rfl
        · exact absurd hx.1 hdb'
      have := Finset.card_le_card this
      rw [Finset.card_singleton] at this
      omega
    have hba : G.Adj b a := by
      by_contra hne
      have hdegb := hdeg b hbS
      have : (G.neighborFinset b).filter (fun y => y ∈ S) ⊆ {u} := by
        intro x hx
        rw [Finset.mem_filter, mem_neighborFinset, hSeq] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl | rfl
        · rfl
        · exact absurd hx.1 hne
        · exact absurd hx.1 G.irrefl
        · exact absurd hx.1.symm hdb'
      have := Finset.card_le_card this
      rw [Finset.card_singleton] at this
      omega
    exact hcommon u a hau.symm b d hdb.symm hub hba.symm hdu'.symm hda'.symm
  · -- `d ≁ a`, `d ~ b`: symmetric
    have hdu' : G.Adj d u := by
      by_contra hne
      have : (G.neighborFinset d).filter (fun y => y ∈ S) ⊆ {b} := by
        intro x hx
        have hx' := hNd hx
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
        rcases hx' with rfl | rfl | rfl
        · exact absurd hx.1 hne
        · exact absurd hx.1 hda'
        · rfl
      have := Finset.card_le_card this
      rw [Finset.card_singleton] at this
      omega
    have hab' : G.Adj a b := by
      by_contra hne
      have hdega := hdeg a haS
      have : (G.neighborFinset a).filter (fun y => y ∈ S) ⊆ {u} := by
        intro x hx
        rw [Finset.mem_filter, mem_neighborFinset, hSeq] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl | rfl
        · rfl
        · exact absurd hx.1 G.irrefl
        · exact absurd hx.1 hne
        · exact absurd hx.1.symm hda'
      have := Finset.card_le_card this
      rw [Finset.card_singleton] at this
      omega
    exact hcommon u b hbu.symm a d hda.symm hua hab'.symm hdu'.symm hdb'.symm
  · -- `d` has at most one neighbour in `S`
    have : (G.neighborFinset d).filter (fun y => y ∈ S) ⊆ {u} := by
      intro x hx
      have hx' := hNd hx
      rw [Finset.mem_filter, mem_neighborFinset] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
      rcases hx' with rfl | rfl | rfl
      · rfl
      · exact absurd hx.1 hda'
      · exact absurd hx.1 hdb'
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this
    omega

/-- **`μ = 1` is impossible at order 64.**  See the module docstring. -/
theorem orderSixtyFour_sizeTwoPart_signedJointEigenvector_muOne_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (v : V → ℤ)
    (hv_out : ∀ x, x ∉ c.supp → v x = 0)
    (hv_in : ∀ x, x ∈ c.supp → v x = 1 ∨ v x = -1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), v y = -2 * v z)
    (hD : ∀ z ∈ c.supp, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, v y = v z) :
    False := by
  have hmem : ∀ x, x ∈ c.supp ↔ (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  -- defect degree `7`, component closure
  have hcensus : Fintype.card V = 8 * (8 - 1) + 3 + (8 - 3) := by rw [hcard]
  have hDdeg : ∀ y : V, (secondOrderDefectGraph G).degree y = 7 := by
    intro y
    have h := secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg hcensus y
    omega
  have hDin : ∀ x y, x ∈ c.supp → (secondOrderDefectGraph G).Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [hmem] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hDout : ∀ x y, x ∉ c.supp → (secondOrderDefectGraph G).Adj x y → y ∉ c.supp := by
    intro x y hx hxy hy
    exact hx (hDin y x hy hxy.symm)
  -- every vertex has exactly two ambient neighbours in `c`
  have htwo : ∀ x, ((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card = 2 := by
    intro x
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg hcard ((secondOrderDefectGraph G).connectedComponentMk x) c
      (x := x) ((ConnectedComponent.mem_supp_iff _ x).mpr rfl)
    rw [hc] at h
    change 8 * ((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card = 8 * 2 at h
    omega
  -- the finset of `c`
  set Sc : Finset V := Finset.univ.filter
    (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c) with hSc
  have hSc_mem : ∀ x, x ∈ Sc ↔ x ∈ c.supp := by
    intro x
    simp only [hSc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hmem x).symm
  have hSc_card : Sc.card = 16 := by
    have h1 : c.supp.ncard = c.supp.toFinset.card := Set.ncard_eq_toFinset_card' c.supp
    have h2 : c.supp.toFinset = Sc := by
      ext x
      rw [Set.mem_toFinset, hSc_mem]
    rw [h2] at h1
    omega
  have hfilt_eq : ∀ x, (G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) =
      (G.neighborFinset x).filter (fun y => y ∈ Sc) := by
    intro x
    apply Finset.filter_congr
    intro y _
    simp only [hSc, Finset.mem_filter, Finset.mem_univ, true_and]
  -- `Σ v = 0` (double count the internal 2-factor)
  have hsum_c : ∑ x ∈ Sc, v x = 0 := by
    have h1 : ∑ x ∈ Sc, ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ Sc), v y =
        ∑ y ∈ Sc, ∑ x ∈ (G.neighborFinset y).filter (fun x => x ∈ Sc), v y :=
      sum_sum_filter_neighborFinset_comm G Sc Sc (fun _ y => v y)
    have hl : ∑ x ∈ Sc, ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ Sc), v y =
        -2 * ∑ x ∈ Sc, v x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← hfilt_eq x]
      exact hH x ((hSc_mem x).mp hx)
    have hr : ∑ y ∈ Sc, ∑ x ∈ (G.neighborFinset y).filter (fun x => x ∈ Sc), v y =
        2 * ∑ y ∈ Sc, v y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_const, ← hfilt_eq y, htwo y, nsmul_eq_mul]
      push_cast; ring
    rw [hl, hr] at h1
    linarith
  have hsum_all : ∑ x, v x = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c)]
    have : ∑ x ∈ Finset.univ.filter
        (fun x => ¬ (secondOrderDefectGraph G).connectedComponentMk x = c), v x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hv_out x (fun h => (Finset.mem_filter.mp hx).2 ((hmem x).mp h))
    rw [this, add_zero]
    exact hsum_c
  -- `a := A v`
  set a : V → ℤ := fun x => ∑ y ∈ G.neighborFinset x, v y with ha
  have ha_split : ∀ x, a x = ∑ y ∈ (G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), v y := by
    intro x
    simp only [ha]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : (secondOrderDefectGraph G).connectedComponentMk y = c
    · simp [hy]
    · rw [if_neg hy, hv_out y (fun h => hy ((hmem y).mp h))]
  have ha_in : ∀ z, z ∈ c.supp → a z = -2 * v z := by
    intro z hz
    rw [ha_split z]
    exact hH z hz
  have ha_val : ∀ x, a x = -2 ∨ a x = 0 ∨ a x = 2 := by
    intro x
    rw [ha_split x]
    obtain ⟨u, u', huu', hset⟩ := Finset.card_eq_two.mp (htwo x)
    rw [hset, Finset.sum_pair huu']
    have hu : u ∈ c.supp := by
      have : u ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
        rw [hset]; simp
      exact (hmem u).mpr (Finset.mem_filter.mp this).2
    have hu' : u' ∈ c.supp := by
      have : u' ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
        rw [hset]; simp
      exact (hmem u').mpr (Finset.mem_filter.mp this).2
    rcases hv_in u hu with h1 | h1 <;> rcases hv_in u' hu' with h2 | h2 <;> simp [h1, h2]
  -- `D v = v` everywhere
  have hDv : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, v y = v x := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact hD x hx
    · rw [hv_out x hx]
      apply Finset.sum_eq_zero
      intro y hy
      exact hv_out y (hDout x y hx (((secondOrderDefectGraph G).mem_neighborFinset x y).mp hy))
  -- `A² v = 6 v`
  have hAA : ∀ x, ∑ y ∈ G.neighborFinset x, a y = 6 * v x := by
    intro x
    have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg (d := 8)
    have h1 : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ v) x = ∑ y ∈ G.neighborFinset x, a y := by
      rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have h2 : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ v) x =
        ((8 : ℕ) - 1 : ℤ) * v x + (∑ y, v y) -
          ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, v y := by
      rw [hsq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
      congr 2
      simp [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct]
    rw [← h1, h2, hsum_all, hDv x]
    push_cast; ring
  -- `w := a + 2 v`
  set w : V → ℤ := fun x => a x + 2 * v x with hw
  have hw_in : ∀ z, z ∈ c.supp → w z = 0 := by
    intro z hz
    simp only [hw]
    rw [ha_in z hz]; ring
  have hw_out : ∀ x, x ∉ c.supp → w x = a x := by
    intro x hx
    simp only [hw]
    rw [hv_out x hx]; ring
  have hw_val : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2 := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact Or.inr (Or.inl (hw_in x hx))
    · rw [hw_out x hx]; exact ha_val x
  have hAw : ∀ x, ∑ y ∈ G.neighborFinset x, w y = 2 * v x + 2 * w x := by
    intro x
    simp only [hw]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hAA x]
    have : ∑ y ∈ G.neighborFinset x, v y = a x := rfl
    rw [this]; ring
  -- the positive support
  set Sp : Finset V := Finset.univ.filter (fun u => w u = 2) with hSp
  have hSp_mem : ∀ u, u ∈ Sp ↔ w u = 2 := by
    intro u; simp only [hSp, Finset.mem_filter, Finset.mem_univ, true_and]
  -- (i) each `u ∈ Sp` has at least two neighbours in `Sp`
  have hmin : ∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter (fun y => y ∈ Sp)).card := by
    intro u hu
    have hwu : w u = 2 := (hSp_mem u).mp hu
    have hvu : v u = 0 := by
      by_contra hne
      have : u ∈ c.supp := by
        by_contra h; exact hne (hv_out u h)
      rw [hw_in u this] at hwu; norm_num at hwu
    have hsum := hAw u
    rw [hvu, hwu] at hsum
    have hle : ∑ y ∈ G.neighborFinset u, w y ≤
        ∑ y ∈ G.neighborFinset u, (if y ∈ Sp then (2 : ℤ) else 0) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ Sp
      · rw [if_pos hy, (hSp_mem y).mp hy]
      · rw [if_neg hy]
        have : w y ≠ 2 := fun h => hy ((hSp_mem y).mpr h)
        rcases hw_val y with h | h | h <;> rw [h] <;> norm_num
        exact absurd h this
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hsum] at hle
    have : (4 : ℤ) ≤ 2 * ((G.neighborFinset u).filter (fun y => y ∈ Sp)).card := by
      linarith
    omega
  -- (ii) `Sp` has exactly four elements
  set X : Finset V := Finset.univ.filter (fun z => v z = 1) with hX
  have hX_mem : ∀ z, z ∈ X ↔ v z = 1 := by
    intro z; simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and]
  have hX_sub : ∀ z, z ∈ X → z ∈ c.supp := by
    intro z hz
    by_contra h
    have := hv_out z h
    rw [(hX_mem z).mp hz] at this
    norm_num at this
  -- each `z ∈ X` has exactly one neighbour in `Sp`
  have hXdeg : ∀ z ∈ X, ((G.neighborFinset z).filter (fun y => y ∈ Sp)).card = 1 := by
    intro z hz
    have hvz : v z = 1 := (hX_mem z).mp hz
    have hzc : z ∈ c.supp := hX_sub z hz
    have hsum := hAw z
    rw [hvz, hw_in z hzc] at hsum
    -- no neighbour of `z` has `w = -2`
    have hno : ∀ y ∈ G.neighborFinset z, w y ≠ -2 := by
      intro y hy hneg
      have hyc : y ∉ c.supp := by
        intro h; rw [hw_in y h] at hneg; norm_num at hneg
      rw [hw_out y hyc, ha_split y] at hneg
      -- `z` is one of the two `c`-neighbours of `y`, with `v z = 1`
      have hzmem : z ∈ (G.neighborFinset y).filter
          (fun y' => (secondOrderDefectGraph G).connectedComponentMk y' = c) := by
        rw [Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset y z).mpr ((G.mem_neighborFinset z y).mp hy).symm,
          (hmem z).mp hzc⟩
      have hge : -1 ≤ ∑ y' ∈ (G.neighborFinset y).filter
          (fun y' => (secondOrderDefectGraph G).connectedComponentMk y' = c), v y' := by
        obtain ⟨p, p', hpp', hset⟩ := Finset.card_eq_two.mp (htwo y)
        rw [hset] at hzmem ⊢
        rw [Finset.sum_pair hpp']
        have hp : p ∈ c.supp := by
          have : p ∈ (G.neighborFinset y).filter
              (fun y' => (secondOrderDefectGraph G).connectedComponentMk y' = c) := by
            rw [hset]; simp
          exact (hmem p).mpr (Finset.mem_filter.mp this).2
        have hp' : p' ∈ c.supp := by
          have : p' ∈ (G.neighborFinset y).filter
              (fun y' => (secondOrderDefectGraph G).connectedComponentMk y' = c) := by
            rw [hset]; simp
          exact (hmem p').mpr (Finset.mem_filter.mp this).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
        rcases hzmem with rfl | rfl
        · rw [hvz]; rcases hv_in p' hp' with h | h <;> rw [h] <;> norm_num
        · rw [hvz]; rcases hv_in p hp with h | h <;> rw [h] <;> norm_num
      omega
    have hall : ∀ y ∈ G.neighborFinset z, w y = if y ∈ Sp then (2 : ℤ) else 0 := by
      intro y hy
      by_cases hyS : y ∈ Sp
      · rw [if_pos hyS]; exact (hSp_mem y).mp hyS
      · rw [if_neg hyS]
        have h2 : w y ≠ 2 := fun h => hyS ((hSp_mem y).mpr h)
        rcases hw_val y with h | h | h
        · exact absurd h (hno y hy)
        · exact h
        · exact absurd h h2
    rw [Finset.sum_congr rfl hall, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    omega
  -- each `u ∈ Sp` has exactly two neighbours in `X`
  have hSpdeg : ∀ u ∈ Sp, ((G.neighborFinset u).filter (fun y => y ∈ X)).card = 2 := by
    intro u hu
    have hwu : w u = 2 := (hSp_mem u).mp hu
    have huc : u ∉ c.supp := by
      intro h; rw [hw_in u h] at hwu; norm_num at hwu
    rw [hw_out u huc, ha_split u] at hwu
    -- both `c`-neighbours of `u` have `v = 1`
    have hboth : ∀ y ∈ (G.neighborFinset u).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), v y = 1 := by
      intro y hy
      have hnonneg : ∀ y' ∈ (G.neighborFinset u).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), 0 ≤ 1 - v y' := by
        intro y' hy'
        have := hv_in y' ((hmem y').mpr (Finset.mem_filter.mp hy').2)
        rcases this with h | h <;> rw [h] <;> norm_num
      have hsum0 : ∑ y' ∈ (G.neighborFinset u).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), (1 - v y') = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, htwo u, hwu]; simp
      have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 y hy
      linarith
    have heq : (G.neighborFinset u).filter (fun y => y ∈ X) =
        (G.neighborFinset u).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hmem y).mp (hX_sub y h2)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hX_mem y).mpr (hboth y (Finset.mem_filter.mpr ⟨h1, h2⟩))⟩
    rw [heq, htwo u]
  -- double count `X`–`Sp` edges: `|X| = 2 |Sp|`
  have hdc := sum_sum_filter_neighborFinset_comm G X Sp (fun _ _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hdc
  have hL : ∑ z ∈ X, (((G.neighborFinset z).filter (fun y => y ∈ Sp)).card : ℤ) = X.card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun z hz => by rw [hXdeg z hz]; simp)]
    simp
  have hR : ∑ u ∈ Sp, (((G.neighborFinset u).filter (fun y => y ∈ X)).card : ℤ) =
      2 * Sp.card := by
    rw [Finset.sum_congr rfl (g := fun _ => (2 : ℤ)) (fun u hu => by rw [hSpdeg u hu]; simp)]
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hL, hR] at hdc
  -- `|X| = 8`: `|X| + |Y| = 16` and `|X| − |Y| = Σ v = 0`
  have hXcard : X.card = 8 := by
    have hXsub : X ⊆ Sc := fun z hz => (hSc_mem z).mpr (hX_sub z hz)
    have hsplit : ∑ x ∈ Sc, v x = ∑ x ∈ Sc.filter (fun z => v z = 1), v x +
        ∑ x ∈ Sc.filter (fun z => ¬ v z = 1), v x :=
      (Finset.sum_filter_add_sum_filter_not Sc (fun z => v z = 1) v).symm
    have hXeq : Sc.filter (fun z => v z = 1) = X := by
      ext z
      simp only [Finset.mem_filter, hX, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨(hSc_mem z).mpr (hX_sub z ((hX_mem z).mpr h)), h⟩
    have h1 : ∑ x ∈ Sc.filter (fun z => v z = 1), v x = X.card := by
      rw [hXeq]
      rw [Finset.sum_congr rfl (fun z hz => (hX_mem z).mp hz)]
      simp
    have h2 : ∑ x ∈ Sc.filter (fun z => ¬ v z = 1), v x =
        -((Sc.filter (fun z => ¬ v z = 1)).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun z hz => by
        have hz' := Finset.mem_filter.mp hz
        rcases hv_in z ((hSc_mem z).mp hz'.1) with h | h
        · exact absurd h hz'.2
        · exact h)]
      simp
    have h3 := Finset.card_filter_add_card_filter_not (s := Sc) (fun z => v z = 1)
    rw [hXeq, hSc_card] at h3
    rw [hsplit, h1, h2] at hsum_c
    omega
  have hSpcard : Sp.card = 4 := by
    rw [hXcard] at hdc
    omega
  -- (iii) a four-vertex set of minimum induced degree two: `C₄`
  exact not_containsC4_no_four_set_min_degree_two G hfree Sp hSpcard hmin

end

end Erdos85
