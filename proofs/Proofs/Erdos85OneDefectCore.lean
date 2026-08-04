import Proofs.Erdos85DeletePair

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

/-- **Intrinsic normal form for a one-defect core.**  When `d` is positive,
the core has minimum degree at least `d - 1`, and every vertex at that lower
degree must be selected for repair.  Thus the remaining extension problem is
precisely to find a large safe selector covering all deficient vertices. -/
theorem oneDefectCore_iff_intrinsic {n d : ℕ} (hd : 1 ≤ d) :
    OneDefectCore n d ↔
      ∃ (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj)
          (S : Finset (Fin n)),
        ¬ containsC4 (Fin n) H ∧
        CommonNeighborIndependent H S ∧
        d ≤ S.card ∧
        (∀ v, d - 1 ≤ H.degree v) ∧
        ∀ v, H.degree v = d - 1 → v ∈ S := by
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

end Erdos85
