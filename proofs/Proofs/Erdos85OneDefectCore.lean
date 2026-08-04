import Proofs.Erdos85DeletePair
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# One-defect cores for Erdős Problem 85

Deleting the prospective new vertex turns every one-vertex extension into a
`C₄`-free graph together with a selector.  Conversely, attaching a vertex to
such a selector reconstructs the extension.  This module records that normal
form exactly; importantly, the core need not be a subgraph of any previously
chosen extremal witness.
-/

namespace Erdos85

open SimpleGraph

/-- A graph on `n` old vertices which becomes a minimum-degree-`d`, `C₄`-free
graph after one vertex is attached.  The two degree requirements expose the
single allowed defect: old vertices may use their edge to the new vertex,
while the new vertex needs at least `d` old neighbours. -/
def OneDefectCore (n d : ℕ) : Prop :=
  ∃ (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj) (S : Finset (Fin n)),
    ¬ containsC4 (Fin n) H ∧
    CommonNeighborIndependent H S ∧
    d ≤ S.card ∧
    ∀ v, d ≤ (attachVertex H S).degree (some v)

/-- The intrinsic selector-cover formulation of a one-defect core. -/
def IntrinsicOneDefectCore (n d : ℕ) : Prop :=
  ∃ (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj)
      (S : Finset (Fin n)),
    ¬ containsC4 (Fin n) H ∧
    CommonNeighborIndependent H S ∧
    d ≤ S.card ∧
    (∀ v, d - 1 ≤ H.degree v) ∧
    ∀ v, H.degree v = d - 1 → v ∈ S

theorem degree_deleteIncidenceSet_of_ne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hy : y ≠ x) :
    (G.deleteIncidenceSet x).degree y =
      G.degree y - if G.Adj y x then 1 else 0 := by
  rw [degree, degree]
  have hfin : (G.deleteIncidenceSet x).neighborFinset y =
      (G.neighborFinset y).erase x := by
    ext z
    simp [SimpleGraph.deleteIncidenceSet_adj, hy, and_comm]
  rw [hfin]
  by_cases hyx : G.Adj y x
  · rw [if_pos hyx, Finset.card_erase_of_mem
      ((G.mem_neighborFinset y x).2 hyx)]
  · rw [if_neg hyx, Nat.sub_zero, Finset.erase_eq_of_notMem]
    exact fun h => hyx ((G.mem_neighborFinset y x).1 h)

theorem commonNeighborIndependent_neighborFinset_deleteIncidenceSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hfree : ¬ containsC4 V G) :
    CommonNeighborIndependent (G.deleteIncidenceSet x) (G.neighborFinset x) := by
  intro a ha b hb hab
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro z hz
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at hz
  have haz : G.Adj a z := (SimpleGraph.deleteIncidenceSet_adj.mp hz.1).1
  have hbz : G.Adj b z := (SimpleGraph.deleteIncidenceSet_adj.mp hz.2).1
  have hzx : z ≠ x := (SimpleGraph.deleteIncidenceSet_adj.mp hz.1).2.2
  rw [SimpleGraph.mem_neighborFinset] at ha hb
  exact hfree (containsC4_of_rim (a := a) (b := z) (c := b) (d := x)
    haz hbz.symm hb.symm ha hab hzx
    (G.ne_of_adj haz).symm (G.ne_of_adj hbz.symm)
    (G.ne_of_adj ha) (G.ne_of_adj hb))

/-- Star deletion produces the required large safe selector and repairs every
possible deficient vertex except the now-isolated center. -/
theorem exists_starDeleted_almostIntrinsic {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {d : ℕ}
    (hd : 1 ≤ d) (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G) :
    let H := G.deleteIncidenceSet x
    let S := G.neighborFinset x
    ¬ containsC4 V H ∧
      CommonNeighborIndependent H S ∧
      d ≤ S.card ∧
      H.degree x = 0 ∧
      (∀ y, y ≠ x → d - 1 ≤ H.degree y) ∧
      ∀ y, y ≠ x → H.degree y = d - 1 → y ∈ S := by
  dsimp
  refine ⟨fun h => hfree (containsC4_mono (G.deleteIncidenceSet_le x) h),
    commonNeighborIndependent_neighborFinset_deleteIncidenceSet G x hfree,
    ?_, ?_, ?_, ?_⟩
  · simpa [SimpleGraph.card_neighborFinset_eq_degree] using
      hmin.trans (G.minDegree_le_degree x)
  · rw [degree]
    have hfin : (G.deleteIncidenceSet x).neighborFinset x = ∅ := by
      ext y
      simp [SimpleGraph.deleteIncidenceSet_adj]
    rw [hfin]
    simp
  · intro y hy
    rw [degree_deleteIncidenceSet_of_ne G x y hy]
    have hydeg := hmin.trans (G.minDegree_le_degree y)
    split <;> omega
  · intro y hy hydeg
    rw [degree_deleteIncidenceSet_of_ne G x y hy] at hydeg
    have hymin := hmin.trans (G.minDegree_le_degree y)
    by_contra hyS
    rw [SimpleGraph.mem_neighborFinset] at hyS
    have hyS' : ¬ G.Adj y x := fun h => hyS h.symm
    rw [if_neg hyS', Nat.sub_zero] at hydeg
    omega

/-- **Intrinsic normal form for a one-defect core.**  When `d` is positive,
the core has minimum degree at least `d - 1`, and every vertex at that lower
degree must be selected for repair.  Thus the remaining extension problem is
precisely to find a large safe selector covering all deficient vertices. -/
theorem oneDefectCore_iff_intrinsic {n d : ℕ} (hd : 1 ≤ d) :
    OneDefectCore n d ↔ IntrinsicOneDefectCore n d := by
  constructor
  · rintro ⟨H, hdec, S, hfree, hsafe, hcard, hold⟩
    letI : DecidableRel H.Adj := hdec
    refine ⟨H, hdec, S, hfree, hsafe, hcard, ?_, ?_⟩
    · intro v
      have hv := hold v
      rw [attachVertex_degree_some_eq] at hv
      split at hv <;> omega
    · intro v hvdeg
      by_contra hvS
      have hv := hold v
      rw [attachVertex_degree_some_eq, if_neg hvS, hvdeg] at hv
      omega
  · rintro ⟨H, hdec, S, hfree, hsafe, hcard, hlow, htight⟩
    letI : DecidableRel H.Adj := hdec
    refine ⟨H, hdec, S, hfree, hsafe, hcard, ?_⟩
    intro v
    rw [attachVertex_degree_some_eq]
    by_cases hvS : v ∈ S
    · rw [if_pos hvS]
      have hv := hlow v
      omega
    · rw [if_neg hvS, Nat.add_zero]
      have hne : H.degree v ≠ d - 1 := fun h => hvS (htight v h)
      have hlt : d - 1 < H.degree v := lt_of_le_of_ne (hlow v) (Ne.symm hne)
      omega

/-- Split a graph on `Option V` into its old-old part. -/
def oldPart {V : Type*} (K : SimpleGraph (Option V)) : SimpleGraph V :=
  SimpleGraph.comap some K

/-- The old vertices adjacent to `none`. -/
def newNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph (Option V)) [DecidableRel K.Adj] : Finset V :=
  Finset.univ.filter fun v => K.Adj (some v) none

instance oldPartDecidableRel {V : Type*} (K : SimpleGraph (Option V))
    [DecidableRel K.Adj] : DecidableRel (oldPart K).Adj :=
  fun x y => inferInstanceAs (Decidable (K.Adj (some x) (some y)))

/-- Splitting at `none` and reattaching it recovers the original graph. -/
theorem attachVertex_oldPart_newNeighborhood {V : Type*} [Fintype V]
    [DecidableEq V] (K : SimpleGraph (Option V)) [DecidableRel K.Adj] :
    attachVertex (oldPart K) (newNeighborhood K) = K := by
  ext x y
  rcases x with _ | x <;> rcases y with _ | y
  · simp [attachVertex, K.loopless]
  · simp [attachVertex, newNeighborhood, adj_comm]
  · simp [attachVertex, newNeighborhood, adj_comm]
  · rfl

/-- The new vertex has exactly the selector as its neighbourhood. -/
theorem attachVertex_degree_none_eq_card {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    (attachVertex H S).degree none = S.card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (attachVertex H S).neighborFinset none =
      S.map ⟨some, Option.some_injective (α := V)⟩ := by
    ext x
    rcases x with _ | x <;> simp
  rw [hfin, Finset.card_map]

/-- The exact normal form: a witness on `n+1` vertices is the attachment of
one vertex to a one-defect core on `n` vertices. -/
theorem c4FreeMinDegreeWitness_succ_iff_oneDefectCore {n d : ℕ} :
    C4FreeMinDegreeWitness (n + 1) d ↔ OneDefectCore n d := by
  classical
  constructor
  · rintro ⟨G, hdec, hdeg, hfree⟩
    letI : DecidableRel G.Adj := hdec
    let K : SimpleGraph (Option (Fin n)) :=
      SimpleGraph.comap (finSuccEquiv n).symm G
    letI : DecidableRel K.Adj := Classical.decRel _
    let e : K ≃g G := SimpleGraph.Iso.comap (finSuccEquiv n).symm G
    let H := oldPart K
    let S := newNeighborhood K
    have hKG : ¬ containsC4 (Option (Fin n)) K := by
      rintro ⟨f, hinj, hadj⟩
      exact hfree ⟨fun i => (finSuccEquiv n).symm (f i),
        (finSuccEquiv n).symm.injective.comp hinj,
        fun i j hij => hadj i j hij⟩
    have hsplit : attachVertex H S = K :=
      attachVertex_oldPart_newNeighborhood K
    let eSplit : attachVertex H S ≃g K := {
      toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro a b
        simpa only [Equiv.refl_apply, hsplit] }
    have hdegree (u : Option (Fin n)) :
        (attachVertex H S).degree u = K.degree u := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext v
      simp only [SimpleGraph.mem_neighborFinset]
      exact eSplit.map_rel_iff.symm
    refine ⟨H, inferInstance, S, ?_, ?_, ?_, ?_⟩
    · intro hC4
      rcases hC4 with ⟨f, hinj, hadj⟩
      exact hKG ⟨fun i => some (f i),
        (Option.some_injective (α := Fin n)).comp hinj,
        fun i j hij => hadj i j hij⟩
    · exact ((attachVertex_not_containsC4_iff).1 (hsplit ▸ hKG)).2
    · have hnone : d ≤ (attachVertex H S).degree none := by
        rw [hdegree]
        exact (hdeg.trans (G.minDegree_le_degree (e none))).trans_eq
          (e.degree_eq none)
      simpa [attachVertex_degree_none_eq_card] using hnone
    · intro v
      rw [hdegree]
      exact (hdeg.trans (G.minDegree_le_degree (e (some v)))).trans_eq
        (e.degree_eq (some v))
  · rintro ⟨H, hdec, S, hfree, hsafe, hcard, hold⟩
    letI : DecidableRel H.Adj := hdec
    refine ⟨attachFin H S, inferInstance, ?_, ?_⟩
    · apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro u
      refine le_trans ?_ (attachFin_degree_ge H S u)
      rcases h : finSuccEquiv n u with _ | v
      · exact hcard.trans (card_le_attachVertex_degree_none H S)
      · exact hold v
    · apply attachFin_not_containsC4 H S
      exact (attachVertex_not_containsC4_iff).2 ⟨hfree, hsafe⟩

/-- **Exact top-level reduction of Erdős 85.** At every order where the
threshold/witness duality applies, monotonicity is equivalent to the existence
of a single one-defect core at the largest degree below the threshold. -/
theorem minDegreeForC4_le_succ_iff_top_oneDefectCore {n : ℕ} (hn : 4 ≤ n) :
    minDegreeForC4 n ≤ minDegreeForC4 (n + 1) ↔
      OneDefectCore n (minDegreeForC4 n - 1) := by
  classical
  have hzero : C4FreeMinDegreeWitness n 0 := by
    refine ⟨⊥, Classical.decRel _, Nat.zero_le _, ?_⟩
    rintro ⟨f, hf, hadj⟩
    simpa using hadj 0 1 (by decide)
  have hpos : 0 < minDegreeForC4 n :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).1 hzero
  constructor
  · intro hmono
    apply c4FreeMinDegreeWitness_succ_iff_oneDefectCore.mp
    apply (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).2
    omega
  · intro hcore
    have hw := c4FreeMinDegreeWitness_succ_iff_oneDefectCore.mpr hcore
    have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).1 hw
    omega

/-- **Intrinsic top-level reduction of Erdős 85.**  Once the threshold is at
least two, one-step monotonicity says exactly that there is a `C₄`-free core
of minimum degree `f(n)-2` whose deficient vertices can all be covered by a
safe selector of size `f(n)-1`. -/
theorem minDegreeForC4_le_succ_iff_intrinsicOneDefectCore {n : ℕ}
    (hn : 4 ≤ n) (hthreshold : 2 ≤ minDegreeForC4 n) :
    minDegreeForC4 n ≤ minDegreeForC4 (n + 1) ↔
      IntrinsicOneDefectCore n (minDegreeForC4 n - 1) := by
  rw [minDegreeForC4_le_succ_iff_top_oneDefectCore hn,
    oneDefectCore_iff_intrinsic]
  omega

end Erdos85
