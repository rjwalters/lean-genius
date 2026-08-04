import Proofs.Erdos85MinimalWitness
import Proofs.Erdos85Relabel

/-!
# The nonneighbor reduction for Erdős Problem 85

In a `C₄`-free graph, delete a vertex together with all of its neighbors.
Every surviving vertex loses at most one neighbor: two lost neighbors would be
two common neighbors of it and the deleted vertex.  This is the local reduction
used in the `C₄`-versus-star Ramsey literature.
-/

open SimpleGraph

namespace Erdos85

/-- The vertices outside the closed neighborhood of `x`. -/
def outsideClosedNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  Finset.univ.filter fun y => y ≠ x ∧ ¬ G.Adj y x

/-- A surviving vertex loses at most one degree when the closed neighborhood
of a vertex is deleted from a `C₄`-free graph. -/
theorem degree_le_induce_outsideClosedNeighborhood_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (y : outsideClosedNeighborhood G x) :
    G.degree y.1 ≤
      (G.induce (outsideClosedNeighborhood G x)).degree y + 1 := by
  classical
  letI : Fintype (outsideClosedNeighborhood G x) :=
    FinsetCoe.fintype (outsideClosedNeighborhood G x)
  let S := outsideClosedNeighborhood G x
  let N := G.neighborFinset y.1
  have hlost : N \ S ⊆
      G.neighborFinset y.1 ∩ G.neighborFinset x := by
    intro z hz
    have hzy : G.Adj y.1 z := (G.mem_neighborFinset y.1 z).mp
      (Finset.mem_sdiff.mp hz).1
    have hzS : z ∉ S := (Finset.mem_sdiff.mp hz).2
    have hzx : G.Adj z x := by
      have hzxne : z ≠ x := by
        intro h
        subst z
        have hy : ¬G.Adj y.1 x :=
          (Finset.mem_filter.mp y.2).2.2
        exact hy hzy
      have hnS : ¬(z ≠ x ∧ ¬G.Adj z x) := by
        simpa [S, outsideClosedNeighborhood] using hzS
      push Not at hnS
      exact hnS hzxne
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset y.1 z).mpr hzy,
        (G.mem_neighborFinset x z).mpr hzx.symm⟩
  have hlostCard : (N \ S).card ≤ 1 :=
    (Finset.card_le_card hlost).trans
      (common_le_one_of_not_containsC4 hfree y.1 x
        (Finset.mem_filter.mp y.2).2.1)
  have hkept : (N ∩ S).card =
      (G.induce (outsideClosedNeighborhood G x)).degree y := by
    rw [← (G.induce (outsideClosedNeighborhood G x)).card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun z hz =>
      (⟨z, (Finset.mem_inter.mp hz).2⟩ : outsideClosedNeighborhood G x))
    · intro z hz
      simpa [SimpleGraph.mem_neighborFinset] using
        (G.mem_neighborFinset y.1 z).mp (Finset.mem_inter.mp hz).1
    · intro a ha b hb hab
      exact congrArg Subtype.val hab
    · intro z hz
      refine ⟨z.1, ?_, rfl⟩
      · exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset y.1 z.1).mpr
              (by simpa [SimpleGraph.mem_neighborFinset] using hz), z.2⟩
  have hpart := Finset.card_inter_add_card_sdiff N S
  rw [G.card_neighborFinset_eq_degree] at hpart
  rw [← hkept]
  omega

/-- The induced graph outside a closed neighborhood is still `C₄`-free. -/
theorem not_containsC4_induce_outsideClosedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    ¬ containsC4 (outsideClosedNeighborhood G x)
      (G.induce (outsideClosedNeighborhood G x)) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  refine ⟨fun i => (f i).1, fun i j hij => ?_, fun i j hij => ?_⟩
  · exact hf (Subtype.ext hij)
  · exact hadj i j hij

/-- If `G` has minimum degree at least `d + 1`, deleting a closed neighborhood
leaves minimum degree at least `d`. -/
theorem le_minDegree_induce_outsideClosedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) {d : ℕ}
    [Nonempty (outsideClosedNeighborhood G x)]
    (hmin : d + 1 ≤ G.minDegree) :
    d ≤ (G.induce (outsideClosedNeighborhood G x)).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro y
  have hdeg := hmin.trans (G.minDegree_le_degree y.1)
  have hloss := degree_le_induce_outsideClosedNeighborhood_add_one G hfree x y
  omega

/-- Exact number of vertices outside the closed neighborhood of `x`. -/
theorem card_outsideClosedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (outsideClosedNeighborhood G x).card =
      Fintype.card V - G.degree x - 1 := by
  classical
  have heq : outsideClosedNeighborhood G x =
      Finset.univ \ insert x (G.neighborFinset x) := by
    ext y
    simp [outsideClosedNeighborhood, G.adj_comm]
  rw [heq, Finset.card_sdiff]
  have hx : x ∉ G.neighborFinset x := by simp
  rw [Finset.inter_univ, Finset.card_insert_of_notMem hx,
    G.card_neighborFinset_eq_degree,
    Finset.card_univ]
  omega

/-- The nonneighbor reduction as a witness theorem.  A `C₄`-free graph of
minimum degree at least `d + 1` yields a witness of degree `d` on the vertices
outside any nonempty closed-neighborhood complement. -/
theorem c4FreeMinDegreeWitness_of_outsideClosedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) {d : ℕ}
    (hmin : d + 1 ≤ G.minDegree)
    (hpos : 1 ≤ Fintype.card V - G.degree x - 1) :
    C4FreeMinDegreeWitness (Fintype.card V - G.degree x - 1) d := by
  let S := outsideClosedNeighborhood G x
  have hScard : S.card = Fintype.card V - G.degree x - 1 :=
    card_outsideClosedNeighborhood G x
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty S := hSne.to_subtype
  apply c4FreeMinDegreeWitness_of_card_eq (G.induce (↑S : Set V))
  · simpa [Fintype.card_coe] using hScard
  · exact le_minDegree_induce_outsideClosedNeighborhood G hfree x hmin
  · exact not_containsC4_induce_outsideClosedNeighborhood G hfree x

/-- **Recursive top-witness reduction.**  From a tight top witness on `n`
vertices, deletion of the closed neighborhood of a minimum-degree vertex gives
a `C₄`-free witness one degree lower on the indicated smaller order. -/
theorem exists_top_nonneighbor_reduction {n : ℕ} (hn : 4 ≤ n) :
    C4FreeMinDegreeWitness
      (n - (minDegreeForC4 n - 1) - 1)
      (minDegreeForC4 n - 2) := by
  obtain ⟨G, hdec, x, hdegree, hx, hfree⟩ := exists_top_tight_vertex hn
  letI : DecidableRel G.Adj := hdec
  have htwo : 2 ≤ minDegreeForC4 n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact two_le_minDegreeForC4 (by omega)
  have hupper := minDegreeForC4_le_sub_two hn
  have hmin : (minDegreeForC4 n - 2) + 1 ≤ G.minDegree := by omega
  have hpos : 1 ≤ n - G.degree x - 1 := by omega
  have hpos' : 1 ≤ Fintype.card (Fin n) - G.degree x - 1 := by
    simpa using hpos
  simpa [hx] using
    c4FreeMinDegreeWitness_of_outsideClosedNeighborhood G hfree x hmin hpos'

/-- Whenever the reduced order is at least four, the recursive witness gives
the corresponding strict lower bound on its threshold. -/
theorem top_nonneighbor_reduction_lt {n : ℕ} (hn : 4 ≤ n)
    (hreduced : 4 ≤ n - (minDegreeForC4 n - 1) - 1) :
    minDegreeForC4 n - 2 <
      minDegreeForC4 (n - (minDegreeForC4 n - 1) - 1) :=
  (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hreduced).1
    (exists_top_nonneighbor_reduction hn)

/-- The order in the top-witness reduction simplifies to `n - f(n)`. -/
theorem top_nonneighbor_reduced_order_eq {n : ℕ} (hn : 4 ≤ n) :
    n - (minDegreeForC4 n - 1) - 1 = n - minDegreeForC4 n := by
  have hlower : 1 ≤ minDegreeForC4 n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have htwo := two_le_minDegreeForC4 (n := m) (by omega)
    omega
  have hupper := minDegreeForC4_le_sub_two hn
  omega

/-- Clean form of the recursive witness reduction: a top witness at `n`
produces degree `f(n)-2` at order `n-f(n)`. -/
theorem exists_top_nonneighbor_reduction_sub_threshold {n : ℕ} (hn : 4 ≤ n) :
    C4FreeMinDegreeWitness (n - minDegreeForC4 n)
      (minDegreeForC4 n - 2) := by
  rw [← top_nonneighbor_reduced_order_eq hn]
  exact exists_top_nonneighbor_reduction hn

/-- Recursive threshold inequality in its clean numerical form. -/
theorem top_nonneighbor_reduction_sub_threshold_lt {n : ℕ} (hn : 4 ≤ n)
    (hreduced : 4 ≤ n - minDegreeForC4 n) :
    minDegreeForC4 n - 2 < minDegreeForC4 (n - minDegreeForC4 n) :=
  (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hreduced).1
    (exists_top_nonneighbor_reduction_sub_threshold hn)

/-- One normalized reduction step for an arbitrary witness. -/
theorem c4FreeMinDegreeWitness_nonneighbor_step {n d : ℕ} (hn : 4 ≤ n)
    (hw : C4FreeMinDegreeWitness n (d + 1)) :
    C4FreeMinDegreeWitness (n - (d + 1) - 1) d := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨G, hdec, hdegree, hfree⟩ :=
    (c4FreeMinDegreeWitness_iff_exists_exact (by omega) (by omega)).1 hw
  letI : DecidableRel G.Adj := hdec
  obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
  have hthreshold : d + 1 < minDegreeForC4 n :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).1 hw
  have hupper := minDegreeForC4_le_sub_two hn
  have hpos : 1 ≤ Fintype.card (Fin n) - G.degree x - 1 := by
    simp only [Fintype.card_fin]
    rw [← hx, hdegree]
    omega
  simpa [← hx, hdegree] using
    c4FreeMinDegreeWitness_of_outsideClosedNeighborhood G hfree x
      (d := d) (by omega) hpos

/-- Orders produced by repeatedly normalizing a witness and deleting the
closed neighborhood of a minimum-degree vertex. -/
def iteratedNonneighborOrder (n d : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => iteratedNonneighborOrder n d k - (d - k) - 1

/-- Total number of vertices removed by the first `k` normalized
closed-neighborhood deletions. -/
def iteratedNonneighborRemoval (d k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (d - i + 1)

/-- The recursive order is the original order minus the accumulated closed
neighborhood sizes. -/
theorem iteratedNonneighborOrder_eq_sub_removal (n d k : ℕ) :
    iteratedNonneighborOrder n d k = n - iteratedNonneighborRemoval d k := by
  induction k with
  | zero => simp [iteratedNonneighborOrder, iteratedNonneighborRemoval]
  | succ k ih =>
      rw [iteratedNonneighborOrder, ih]
      simp only [iteratedNonneighborRemoval, Finset.sum_range_succ]
      omega

/-- A witness of certified degree at least three necessarily has at least four
vertices. -/
theorem four_le_order_of_c4FreeMinDegreeWitness {n d : ℕ} (hthree : 3 ≤ d)
    (hw : C4FreeMinDegreeWitness n d) : 4 ≤ n := by
  by_contra hn
  have hnle : n ≤ 3 := by omega
  rcases hw with ⟨G, hdec, hmin, _⟩
  letI : DecidableRel G.Adj := hdec
  by_cases hn0 : n = 0
  · subst n
    simp at hmin
    omega
  · have hnpos : 1 ≤ n := by omega
    let v : Fin n := ⟨0, hnpos⟩
    have hdeg := G.degree_lt_card_verts v
    have hmd := G.minDegree_le_degree v
    simp only [Fintype.card_fin] at hdeg
    omega

/-- The checked values `f(4),…,f(9) = 2,3,3,3,3,3` imply that a
degree-three witness needs at least ten vertices. -/
theorem ten_le_order_of_c4FreeMinDegreeWitness_three {n : ℕ}
    (hw : C4FreeMinDegreeWitness n 3) : 10 ≤ n := by
  have hfour : 4 ≤ n := four_le_order_of_c4FreeMinDegreeWitness (by omega) hw
  have hlt : 3 < minDegreeForC4 n :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hfour).1 hw
  by_contra hten
  have hnine : n ≤ 9 := by omega
  interval_cases n <;>
    simp [minDegreeForC4_four, minDegreeForC4_five,
      minDegreeForC4_six, minDegreeForC4_seven,
      minDegreeForC4_eight, minDegreeForC4_nine] at hlt

/-- Iterated nonneighbor reduction.  As long as every intermediate order is at
least four, `k` reductions lower the certified degree from `d` to `d-k` and
produce a witness on `iteratedNonneighborOrder n d k` vertices. -/
theorem c4FreeMinDegreeWitness_iterated_nonneighbor
    {n d k : ℕ} (hw : C4FreeMinDegreeWitness n d)
    (hk : k ≤ d)
    (horders : ∀ i, i < k → 4 ≤ iteratedNonneighborOrder n d i) :
    C4FreeMinDegreeWitness (iteratedNonneighborOrder n d k) (d - k) := by
  induction k with
  | zero => simpa [iteratedNonneighborOrder] using hw
  | succ k ih =>
      have hklt : k < d := by omega
      have hprev : C4FreeMinDegreeWitness
          (iteratedNonneighborOrder n d k) (d - k) :=
        ih (by omega) (fun i hi => horders i (by omega))
      have hdegree : d - k = (d - (k + 1)) + 1 := by omega
      have hprev' : C4FreeMinDegreeWitness
          (iteratedNonneighborOrder n d k) ((d - (k + 1)) + 1) := by
        rwa [← hdegree]
      have hstep := c4FreeMinDegreeWitness_nonneighbor_step
        (horders k (by omega)) hprev'
      rw [← hdegree] at hstep
      simpa [iteratedNonneighborOrder] using hstep

/-- Every admissible iterate gives a strict lower bound for the threshold at
the reduced order. -/
theorem iterated_nonneighbor_lt_minDegreeForC4
    {n d k : ℕ} (hw : C4FreeMinDegreeWitness n d)
    (hk : k ≤ d)
    (horders : ∀ i, i < k → 4 ≤ iteratedNonneighborOrder n d i)
    (hfinal : 4 ≤ iteratedNonneighborOrder n d k) :
    d - k < minDegreeForC4 (iteratedNonneighborOrder n d k) :=
  (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hfinal).1
    (c4FreeMinDegreeWitness_iterated_nonneighbor hw hk horders)

/-- Up to degree two, the intermediate-order hypotheses in the iterated
reduction are automatic: the current certified degree is at least three, so
the current graph has at least four vertices. -/
theorem c4FreeMinDegreeWitness_iterated_nonneighbor_auto
    {n d k : ℕ} (hw : C4FreeMinDegreeWitness n d) (hk : k + 2 ≤ d) :
    C4FreeMinDegreeWitness (iteratedNonneighborOrder n d k) (d - k) := by
  induction k with
  | zero => simpa [iteratedNonneighborOrder] using hw
  | succ k ih =>
      have hprev := ih (by omega)
      have hthree : 3 ≤ d - k := by omega
      have horder := four_le_order_of_c4FreeMinDegreeWitness hthree hprev
      have hdegree : d - k = (d - (k + 1)) + 1 := by omega
      have hprev' : C4FreeMinDegreeWitness
          (iteratedNonneighborOrder n d k) ((d - (k + 1)) + 1) := by
        rwa [← hdegree]
      have hstep := c4FreeMinDegreeWitness_nonneighbor_step horder hprev'
      rw [← hdegree] at hstep
      simpa [iteratedNonneighborOrder] using hstep

/-- Automatic recursive threshold constraints for every iterate that leaves
certified degree at least three. -/
theorem iterated_nonneighbor_auto_lt_minDegreeForC4
    {n d k : ℕ} (hw : C4FreeMinDegreeWitness n d) (hk : k + 3 ≤ d) :
    d - k < minDegreeForC4 (iteratedNonneighborOrder n d k) := by
  have hw' := c4FreeMinDegreeWitness_iterated_nonneighbor_auto
    (n := n) (d := d) (k := k) hw (by omega)
  have hthree : 3 ≤ d - k := by omega
  exact (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4
    (four_le_order_of_c4FreeMinDegreeWitness hthree hw')).1 hw'

/-- Iterating all the way down to degree three must leave at least ten
vertices.  Equivalently, the original order pays for every deleted closed
neighborhood and for a final degree-three core of order at least ten. -/
theorem iterated_nonneighbor_degree_three_core_bound
    {n d : ℕ} (hthree : 3 ≤ d) (hw : C4FreeMinDegreeWitness n d) :
    iteratedNonneighborRemoval d (d - 3) + 10 ≤ n := by
  have hk : (d - 3) + 3 ≤ d := by omega
  have hiter := c4FreeMinDegreeWitness_iterated_nonneighbor_auto
    (n := n) (d := d) (k := d - 3) hw (by omega)
  have hdegree : d - (d - 3) = 3 := by omega
  have hcore : C4FreeMinDegreeWitness
      (iteratedNonneighborOrder n d (d - 3)) 3 := by
    rwa [hdegree] at hiter
  have hten := ten_le_order_of_c4FreeMinDegreeWitness_three hcore
  rw [iteratedNonneighborOrder_eq_sub_removal] at hten
  omega

/-- A `C₄`-free graph of minimum degree at least four has at least fifteen
vertices.  The bound is sharp (the 15-vertex polarity witness realizes it). -/
theorem fifteen_le_order_of_c4FreeMinDegreeWitness_four {n : ℕ}
    (hw : C4FreeMinDegreeWitness n 4) : 15 ≤ n := by
  have h := iterated_nonneighbor_degree_three_core_bound (n := n) (d := 4)
    (by omega) hw
  norm_num [iteratedNonneighborRemoval] at h ⊢
  exact h

/-- A `C₄`-free graph of minimum degree at least five has at least twenty-one
vertices.  This is also sharp, as witnessed by the order-21 construction. -/
theorem twentyone_le_order_of_c4FreeMinDegreeWitness_five {n : ℕ}
    (hw : C4FreeMinDegreeWitness n 5) : 21 ≤ n := by
  have h := iterated_nonneighbor_degree_three_core_bound (n := n) (d := 5)
    (by omega) hw
  norm_num [iteratedNonneighborRemoval] at h ⊢
  exact h

/-- A uniform consequence of the reduction: a `C₄`-free minimum-degree-`d`
witness, for `d ≥ 3`, has at least `C(d+2,2)` vertices.  This is sharp for
`d = 3,4,5` in the present development. -/
theorem choose_degree_add_two_le_order_of_c4FreeMinDegreeWitness
    {n d : ℕ} (hthree : 3 ≤ d) (hw : C4FreeMinDegreeWitness n d) :
    (d + 2).choose 2 ≤ n := by
  induction d using Nat.strong_induction_on generalizing n with
  | h d ih =>
      by_cases hd : d = 3
      · subst d
        norm_num
        exact ten_le_order_of_c4FreeMinDegreeWitness_three hw
      · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        have hethree : 3 ≤ e := by omega
        have hfour : 4 ≤ n :=
          four_le_order_of_c4FreeMinDegreeWitness (by omega) hw
        have hstep : C4FreeMinDegreeWitness (n - (e + 1) - 1) e :=
          c4FreeMinDegreeWitness_nonneighbor_step hfour hw
        have hbound : (e + 2).choose 2 ≤ n - (e + 1) - 1 :=
          ih e (by omega) hethree hstep
        have hen : e + 2 ≤ n := by
          have hthreshold : e + 1 < minDegreeForC4 n :=
            (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hfour).1 hw
          have hupper := minDegreeForC4_le_sub_two hfour
          omega
        have hadd : (e + 2) + (e + 2).choose 2 ≤ n := by omega
        have hchoose : ((e + 2) + 1).choose 2 =
            (e + 2) + (e + 2).choose 2 := by
          rw [Nat.choose_succ_succ]
          simp
        have heq : e + 1 + 2 = (e + 2) + 1 := by omega
        rw [heq, hchoose]
        exact hadd

/-- Contrapositive threshold form of the uniform order bound. -/
theorem minDegreeForC4_le_of_lt_choose_degree_add_two
    {n d : ℕ} (hn : 4 ≤ n) (hthree : 3 ≤ d)
    (hsmall : n < (d + 2).choose 2) :
    minDegreeForC4 n ≤ d := by
  by_contra hnot
  have hlt : d < minDegreeForC4 n := by omega
  have hw : C4FreeMinDegreeWitness n d :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).2 hlt
  have horder :=
    choose_degree_add_two_le_order_of_c4FreeMinDegreeWitness hthree hw
  omega

/-- The classical common-neighbor count, expressed as a necessary order bound
for a witness. -/
theorem mul_pred_lt_order_of_c4FreeMinDegreeWitness
    {n d : ℕ} (hthree : 3 ≤ d) (hw : C4FreeMinDegreeWitness n d) :
    d * (d - 1) < n := by
  have hfour : 4 ≤ n := four_le_order_of_c4FreeMinDegreeWitness hthree hw
  have hthreshold : d < minDegreeForC4 n :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hfour).1 hw
  by_contra hnot
  have hupper := minDegreeForC4_le_of_le_mul_pred (by omega)
    (Nat.le_of_not_gt hnot)
  omega

/-- Combined surgery-and-counting lower bound.  The triangular reduction bound
is stronger in the first sharp cases; the classical quadratic count dominates
from degree six onward. -/
theorem max_choose_add_two_mul_pred_succ_le_order_of_witness
    {n d : ℕ} (hthree : 3 ≤ d) (hw : C4FreeMinDegreeWitness n d) :
    max ((d + 2).choose 2) (d * (d - 1) + 1) ≤ n := by
  rw [max_le_iff]
  refine ⟨choose_degree_add_two_le_order_of_c4FreeMinDegreeWitness hthree hw, ?_⟩
  have hcount := mul_pred_lt_order_of_c4FreeMinDegreeWitness hthree hw
  omega

/-- In a `C₄`-free graph of minimum degree at least three, no vertex is
universal. -/
theorem degree_add_two_le_order_of_not_containsC4
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree) (hfree : ¬ containsC4 (Fin n) G) (x : Fin n) :
    G.degree x + 2 ≤ n := by
  have hxdeg : 3 ≤ G.degree x := hmin.trans (G.minDegree_le_degree x)
  have hxlt := G.degree_lt_card_verts x
  simp only [Fintype.card_fin] at hxlt
  by_contra hnot
  have hxeq : G.degree x = n - 1 := by omega
  have hsub : G.neighborFinset x ⊆ Finset.univ.erase x := by
    intro z hz
    exact Finset.mem_erase.mpr
      ⟨(G.ne_of_adj ((G.mem_neighborFinset x z).mp hz)).symm,
        Finset.mem_univ z⟩
  have hcard : (Finset.univ.erase x).card ≤ (G.neighborFinset x).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin, G.card_neighborFinset_eq_degree, hxeq]
  have hxall : G.neighborFinset x = Finset.univ.erase x :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hxpos : 0 < (G.neighborFinset x).card := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨y, hyx⟩ := Finset.card_pos.mp hxpos
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hyx
  have hxyMem : x ∈ G.neighborFinset y :=
    (G.mem_neighborFinset y x).mpr hxy.symm
  have hydeg : 3 ≤ G.degree y := hmin.trans (G.minDegree_le_degree y)
  have herase : 1 < ((G.neighborFinset y).erase x).card := by
    rw [Finset.card_erase_of_mem hxyMem, G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp herase
  have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp (Finset.mem_erase.mp hz).2
  have hyw : G.Adj y w := (G.mem_neighborFinset y w).mp (Finset.mem_erase.mp hw).2
  have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
  have hwx : w ≠ x := (Finset.mem_erase.mp hw).1
  have hxz : G.Adj x z := by
    apply (G.mem_neighborFinset x z).mp
    rw [hxall]
    exact Finset.mem_erase.mpr ⟨hzx, Finset.mem_univ z⟩
  have hxw : G.Adj x w := by
    apply (G.mem_neighborFinset x w).mp
    rw [hxall]
    exact Finset.mem_erase.mpr ⟨hwx, Finset.mem_univ w⟩
  exact hfree (containsC4_of_rim (a := y) (b := z) (c := x) (d := w)
    hyz hxz.symm hxw hyw.symm
    (G.ne_of_adj hxy).symm hzw
    (G.ne_of_adj hyz).symm hzx (G.ne_of_adj hyw).symm hwx)

/-- Deleting the closed neighborhood of any vertex and applying the triangular
bound to the reduced witness gives a vertex-sensitive order inequality. -/
theorem degree_add_one_add_choose_le_order
    {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : 4 ≤ d) (hdegree : G.minDegree = d)
    (hfree : ¬ containsC4 (Fin n) G) (x : Fin n) :
    G.degree x + 1 + (d + 1).choose 2 ≤ n := by
  have hmin3 : 3 ≤ G.minDegree := by omega
  have hnonuniv := degree_add_two_le_order_of_not_containsC4 G hmin3 hfree x
  have hpos : 1 ≤ Fintype.card (Fin n) - G.degree x - 1 := by
    simp only [Fintype.card_fin]
    omega
  have hreduced := c4FreeMinDegreeWitness_of_outsideClosedNeighborhood
    G hfree x (d := d - 1) (by omega) hpos
  have hbound := choose_degree_add_two_le_order_of_c4FreeMinDegreeWitness
    (d := d - 1) (by omega) hreduced
  simp only [Fintype.card_fin] at hbound
  have hchooseArg : d - 1 + 2 = d + 1 := by omega
  rw [hchooseArg] at hbound
  omega

/-- A vertex strictly above the exact minimum forces one full vertex of slack
beyond the triangular order bound. -/
theorem choose_degree_add_two_add_one_le_order_of_high_vertex
    {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : 4 ≤ d) (hdegree : G.minDegree = d)
    (hfree : ¬ containsC4 (Fin n) G) {x : Fin n}
    (hxhigh : d < G.degree x) :
    (d + 2).choose 2 + 1 ≤ n := by
  have hvertex := degree_add_one_add_choose_le_order
    G hfour hdegree hfree x
  have hchoose : (d + 2).choose 2 = (d + 1) + (d + 1).choose 2 := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ]
    simp
  rw [hchoose]
  omega

/-- Equality in the triangular witness bound forces exact regularity. -/
theorem regular_of_card_eq_choose_degree_add_two
    {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : 4 ≤ d) (hdegree : G.minDegree = d)
    (hfree : ¬ containsC4 (Fin n) G)
    (hcard : n = (d + 2).choose 2) :
    ∀ x, G.degree x = d := by
  intro x
  have hxlow : d ≤ G.degree x := by
    rw [← hdegree]
    exact G.minDegree_le_degree x
  by_contra hxne
  have hxhigh : d < G.degree x := lt_of_le_of_ne hxlow (Ne.symm hxne)
  have hstrict := choose_degree_add_two_add_one_le_order_of_high_vertex
    G hfour hdegree hfree hxhigh
  omega

/-- At triangular equality, deleting the closed neighborhood of *any* vertex
lands exactly on the next triangular witness order. -/
theorem closedNeighborhood_witness_of_card_eq_choose_degree_add_two
    {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : 4 ≤ d) (hdegree : G.minDegree = d)
    (hfree : ¬ containsC4 (Fin n) G)
    (hcard : n = (d + 2).choose 2) (x : Fin n) :
    C4FreeMinDegreeWitness ((d + 1).choose 2) (d - 1) := by
  have hregular := regular_of_card_eq_choose_degree_add_two
    G hfour hdegree hfree hcard
  have hx := hregular x
  have hchoose : (d + 2).choose 2 = (d + 1) + (d + 1).choose 2 := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ]
    simp
  have horder : Fintype.card (Fin n) - G.degree x - 1 =
      (d + 1).choose 2 := by
    simp only [Fintype.card_fin]
    omega
  have hpos : 1 ≤ Fintype.card (Fin n) - G.degree x - 1 := by
    rw [horder]
    have : 0 < (d + 1).choose 2 := Nat.choose_pos (by omega)
    omega
  have hreduced := c4FreeMinDegreeWitness_of_outsideClosedNeighborhood
    G hfree x (d := d - 1) (by omega) hpos
  rwa [horder] at hreduced

/-- From degree six onward, the classical quadratic count strictly exceeds
the triangular reduction bound. -/
theorem choose_degree_add_two_lt_mul_pred_succ {d : ℕ} (hsix : 6 ≤ d) :
    (d + 2).choose 2 < d * (d - 1) + 1 := by
  rw [Nat.choose_two_right, Nat.div_lt_iff_lt_mul (by norm_num)]
  have hsub : d + 2 - 1 = d + 1 := by omega
  have hpred : d - 1 + 1 = d := by omega
  rw [hsub]
  nlinarith

/-- Consequently triangular equality can occur only in degrees at most five.
Together with the regularity theorem, the nontrivial equality cases are reduced
to the sharp degree-four and degree-five orders 15 and 21. -/
theorem degree_le_five_of_witness_card_eq_choose_degree_add_two
    {n d : ℕ} (hthree : 3 ≤ d) (hw : C4FreeMinDegreeWitness n d)
    (hcard : n = (d + 2).choose 2) : d ≤ 5 := by
  by_contra hnot
  have hsix : 6 ≤ d := by omega
  have hcombined := max_choose_add_two_mul_pred_succ_le_order_of_witness
    hthree hw
  have hcount : d * (d - 1) + 1 ≤ n :=
    (le_max_right _ _).trans hcombined
  have hstrict := choose_degree_add_two_lt_mul_pred_succ hsix
  omega

/-- Strongest combined vertex-sensitive form currently available: the graph
must accommodate the closed neighborhood of `x` and both lower bounds for the
degree-`d-1` witness that remains outside it. -/
theorem degree_add_one_add_max_reduced_bound_le_order
    {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : 4 ≤ d) (hdegree : G.minDegree = d)
    (hfree : ¬ containsC4 (Fin n) G) (x : Fin n) :
    G.degree x + 1 +
      max ((d + 1).choose 2) ((d - 1) * (d - 2) + 1) ≤ n := by
  have hmin3 : 3 ≤ G.minDegree := by omega
  have hnonuniv := degree_add_two_le_order_of_not_containsC4 G hmin3 hfree x
  have hpos : 1 ≤ Fintype.card (Fin n) - G.degree x - 1 := by
    simp only [Fintype.card_fin]
    omega
  have hreduced := c4FreeMinDegreeWitness_of_outsideClosedNeighborhood
    G hfree x (d := d - 1) (by omega) hpos
  have hbound := max_choose_add_two_mul_pred_succ_le_order_of_witness
    (d := d - 1) (by omega) hreduced
  simp only [Fintype.card_fin] at hbound
  have hchooseArg : d - 1 + 2 = d + 1 := by omega
  have hpredArg : d - 1 - 1 = d - 2 := by omega
  rw [hchooseArg, hpredArg] at hbound
  omega

/-- Equivalent explicit upper bound on every vertex degree. -/
theorem degree_le_order_sub_max_reduced_bound_sub_one
    {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : 4 ≤ d) (hdegree : G.minDegree = d)
    (hfree : ¬ containsC4 (Fin n) G) (x : Fin n) :
    G.degree x ≤ n -
      max ((d + 1).choose 2) ((d - 1) * (d - 2) + 1) - 1 := by
  have h := degree_add_one_add_max_reduced_bound_le_order
    G hfour hdegree hfree x
  omega

end Erdos85
