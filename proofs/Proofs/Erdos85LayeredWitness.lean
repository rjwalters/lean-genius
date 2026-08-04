import Proofs.Erdos85MinimalWitness

/-!
# Layered top witnesses for Erdős Problem 85
-/

open SimpleGraph

namespace Erdos85

theorem card_tightVertices_add_card_aboveMinVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdegree : G.minDegree = d) :
    (tightVertices G d).card + (aboveMinVertices G d).card =
      Fintype.card V := by
  have hdisjoint : Disjoint (tightVertices G d) (aboveMinVertices G d) := by
    rw [Finset.disjoint_left]
    intro v hvT hvU
    have hvEq : G.degree v = d := by simpa [tightVertices] using hvT
    have hvLt : d < G.degree v := by simpa [aboveMinVertices] using hvU
    omega
  have hunion : tightVertices G d ∪ aboveMinVertices G d = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hv : d ≤ G.degree v := by
      rw [← hdegree]
      exact G.minDegree_le_degree v
    simp only [tightVertices, aboveMinVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  rw [← Finset.card_union_of_disjoint hdisjoint, hunion,
    Finset.card_univ]

/-- Edge-cover normalization gives a direct incidence inequality: every
above-minimum vertex has at least `d+1` neighbors, all in the tight layer,
while each tight vertex has exactly `d` incident edges in total. -/
theorem card_aboveMin_mul_succ_le_card_tight_mul_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hcover : ∀ ⦃u v⦄, G.Adj u v →
      G.degree u = d ∨ G.degree v = d) :
    (aboveMinVertices G d).card * (d + 1) ≤
      (tightVertices G d).card * d := by
  classical
  let U := aboveMinVertices G d
  let T := tightVertices G d
  let L : Finset (Σ _u : V, V) :=
    U.sigma fun u => G.neighborFinset u
  let R : Finset (Σ _v : V, V) :=
    T.sigma fun v => G.neighborFinset v
  have hLR : L.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn
      (fun p : Σ _u : V, V => (⟨p.2, p.1⟩ : Σ _v : V, V))
    · intro p hp
      change p ∈ L at hp
      change (⟨p.2, p.1⟩ : Σ _v : V, V) ∈ R
      dsimp [L, R] at hp ⊢
      rw [Finset.mem_sigma] at hp ⊢
      have hpAdj : G.Adj p.1 p.2 :=
        (G.mem_neighborFinset p.1 p.2).mp hp.2
      have hpHigh : d < G.degree p.1 := by
        simpa [U, aboveMinVertices] using hp.1
      have hpTight : G.degree p.2 = d := by
        rcases hcover hpAdj with h | h
        · omega
        · exact h
      exact ⟨by simpa [T, tightVertices] using hpTight,
        (G.mem_neighborFinset p.2 p.1).mpr hpAdj.symm⟩
    · intro p hp q hq hpq
      rcases p with ⟨u, v⟩
      rcases q with ⟨u', v'⟩
      have hv : v = v' := congrArg Sigma.fst hpq
      have hu : u = u' := congrArg Sigma.snd hpq
      subst v'
      subst u'
      rfl
  have hLcard : L.card = ∑ u ∈ U, G.degree u := by
    dsimp [L]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro u _
    exact G.card_neighborFinset_eq_degree u
  have hRcard : R.card = T.card * d := by
    dsimp [R]
    rw [Finset.card_sigma]
    calc
      (∑ v ∈ T, (G.neighborFinset v).card) = ∑ _v ∈ T, d := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [G.card_neighborFinset_eq_degree]
        simpa [T, tightVertices] using hv
      _ = T.card * d := by simp
  have hLlower : U.card * (d + 1) ≤ ∑ u ∈ U, G.degree u := by
    calc
      U.card * (d + 1) = ∑ _u ∈ U, (d + 1) := by simp
      _ ≤ ∑ u ∈ U, G.degree u := by
        apply Finset.sum_le_sum
        intro u hu
        have : d < G.degree u := by
          simpa [U, aboveMinVertices] using hu
        omega
  change U.card * (d + 1) ≤ T.card * d
  rw [hLcard, hRcard] at hLR
  exact hLlower.trans hLR

/-- In every nonempty edge-covered exact-minimum-degree graph, the tight
layer strictly outnumbers the above-minimum independent layer. -/
theorem card_aboveMin_lt_card_tight
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdegree : G.minDegree = d)
    (hcover : ∀ ⦃u v⦄, G.Adj u v →
      G.degree u = d ∨ G.degree v = d) :
    (aboveMinVertices G d).card < (tightVertices G d).card := by
  let U := (aboveMinVertices G d).card
  let T := (tightVertices G d).card
  have hpart : T + U = Fintype.card V := by
    exact card_tightVertices_add_card_aboveMinVertices G hdegree
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have hinc := card_aboveMin_mul_succ_le_card_tight_mul_degree G hcover
  by_contra hnot
  have hTU : T ≤ U := Nat.le_of_not_gt hnot
  have hUpos : 0 < U := by
    by_contra hzero
    have : U = 0 := Nat.eq_zero_of_not_pos hzero
    omega
  have hright : T * d ≤ U * d := Nat.mul_le_mul_right d hTU
  have hstrict : U * d < U * (d + 1) := by
    exact (Nat.mul_lt_mul_left hUpos).mpr (Nat.lt_succ_self d)
  exact (not_lt_of_ge (hinc.trans hright)) hstrict

/-- More than half of the vertices in a normalized witness are tight. -/
theorem two_mul_card_aboveMin_lt_card
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdegree : G.minDegree = d)
    (hcover : ∀ ⦃u v⦄, G.Adj u v →
      G.degree u = d ∨ G.degree v = d) :
    2 * (aboveMinVertices G d).card < Fintype.card V := by
  have hpart := card_tightVertices_add_card_aboveMinVertices G hdegree
  have hlt := card_aboveMin_lt_card_tight G hdegree hcover
  omega

/-- Every size below half the order can be realized by a deletion set made
entirely of tight vertices in the normalized witness. -/
theorem exists_tight_deletion_set_of_two_mul_lt_card
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ}
    (hdegree : G.minDegree = d)
    (hcover : ∀ ⦃u v⦄, G.Adj u v →
      G.degree u = d ∨ G.degree v = d)
    (hk : 2 * k < Fintype.card V) :
    ∃ D : Finset V, D.card = k ∧ ∀ x ∈ D, G.degree x = d := by
  have hpart := card_tightVertices_add_card_aboveMinVertices G hdegree
  have hlt := card_aboveMin_lt_card_tight G hdegree hcover
  have hkT : k ≤ (tightVertices G d).card := by omega
  obtain ⟨D, hsub, hDcard⟩ := Finset.exists_subset_card_eq hkT
  refine ⟨D, hDcard, ?_⟩
  intro x hx
  have hxT := hsub hx
  simpa [tightVertices] using hxT

/-- **Layered threshold normal form.** At every order n at least four, a top
C4-free witness may be chosen with tight vertices covering every edge. Its
high-degree vertices form an independent layer whose large neighborhoods pack
linearly into the tight layer. -/
theorem exists_top_layered_witness {n : ℕ} (hn : 4 ≤ n) :
    let d := minDegreeForC4 n - 1
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin n) G ∧
      (∀ ⦃u v⦄, G.Adj u v →
        G.degree u = d ∨ G.degree v = d) ∧
      (tightVertices G d).card + (aboveMinVertices G d).card = n ∧
      (aboveMinVertices G d).card * (d + 1).choose 2 ≤
        (tightVertices G d).card.choose 2 := by
  dsimp
  obtain ⟨G, hdec, hdegree, hfree, hcover⟩ :=
    exists_top_edgeCovered_exact_minDegree hn
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hdegree, hfree, hcover, ?_, ?_⟩
  · simpa using card_tightVertices_add_card_aboveMinVertices G hdegree
  · exact card_aboveMin_mul_choose_succ_le_choose_card_tight
      G hfree hcover

end Erdos85
