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

end Erdos85
