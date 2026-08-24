import Proofs.Erdos85ClosedNeighborhoodCutLocalEdges
import Proofs.Erdos85IncidenceEnergyModThreeResidue

/-!
# Strict closed-neighborhood energy from triangle incidence

For an arbitrary finite simple graph, an edge in the induced neighborhood at
`x` is the same thing as a triangle containing `x`.  Double-counting these
rooted triangles shows that the sum of all local edge counts is three times
the number of triangles, without any `C₄`-free hypothesis.  Combining this
with the exact regular closed-star cut identity supplies the mod-three excess
residue and hence the strict cubic energy bounds.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem localEdges_eq_cliques_containing
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (x : V) :
    (D.induce (D.neighborSet x)).edgeFinset.card =
      ((D.cliqueFinset 3).filter (x ∈ ·)).card := by
  classical
  let f : Sym2 {z : V // z ∈ D.neighborSet x} → Finset V :=
    fun e => insert x (e.map Subtype.val).toFinset
  apply Finset.card_bij (fun e _ => f e)
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · induction e using Sym2.inductionOn with
      | _ u v =>
          simp only [f, Sym2.map_mk, Sym2.toFinset_mk_eq]
          rw [SimpleGraph.is3Clique_iff]
          refine ⟨x, u.1, v.1, ?_, ?_, ?_, rfl⟩
          · exact (D.mem_neighborSet x u.1).mp u.2
          · exact (D.mem_neighborSet x v.1).mp v.2
          · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    · simp [f]
  · intro e₁ he₁ e₂ he₂ h
    induction e₁ using Sym2.inductionOn with
    | _ u₁ v₁ =>
      induction e₂ using Sym2.inductionOn with
      | _ u₂ v₂ =>
        simp only [f, Sym2.map_mk, Sym2.toFinset_mk_eq] at h
        have hxu₁ : x ≠ u₁.1 := ((D.mem_neighborSet x u₁.1).mp u₁.2).ne
        have hxv₁ : x ≠ v₁.1 := ((D.mem_neighborSet x v₁.1).mp v₁.2).ne
        have hxu₂ : x ≠ u₂.1 := ((D.mem_neighborSet x u₂.1).mp u₂.2).ne
        have hxv₂ : x ≠ v₂.1 := ((D.mem_neighborSet x v₂.1).mp v₂.2).ne
        have hpairs : ({u₁.1, v₁.1} : Finset V) = {u₂.1, v₂.1} := by
          simpa [hxu₁, hxv₁, hxu₂, hxv₂] using
            congrArg (fun s : Finset V => s.erase x) h
        have hadj₁ : D.Adj u₁.1 v₁.1 := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            SimpleGraph.induce_adj] using he₁
        have hadj₂ : D.Adj u₂.1 v₂.1 := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            SimpleGraph.induce_adj] using he₂
        have hne₁ : u₁.1 ≠ v₁.1 := hadj₁.ne
        have hne₂ : u₂.1 ≠ v₂.1 := hadj₂.ne
        apply Sym2.eq_iff.mpr
        simp only [Subtype.ext_iff]
        simp only [Finset.ext_iff] at hpairs
        have hu := (hpairs u₁.1).mp (by simp)
        have hv := (hpairs v₁.1).mp (by simp)
        grind
  · intro s hs
    simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hs
    obtain ⟨hsclique, hxs⟩ := hs
    rw [SimpleGraph.is3Clique_iff] at hsclique
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hsclique
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
    rcases hxs with hxa | hxb | hxc
    · subst a
      let u : {z : V // z ∈ D.neighborSet x} := ⟨b, hab⟩
      let v : {z : V // z ∈ D.neighborSet x} := ⟨c, hac⟩
      refine ⟨s(u, v), ?_, ?_⟩
      · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.induce_adj] using hbc
      · dsimp [f, u, v]
        rw [Sym2.toFinset_mk_eq]
    · subst b
      let u : {z : V // z ∈ D.neighborSet x} := ⟨a, (D.adj_comm a x).mp hab⟩
      let v : {z : V // z ∈ D.neighborSet x} := ⟨c, hbc⟩
      refine ⟨s(u, v), ?_, ?_⟩
      · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.induce_adj] using hac
      · dsimp [f, u, v]
        rw [Sym2.toFinset_mk_eq]
        ext z
        simp [or_left_comm]
    · subst c
      let u : {z : V // z ∈ D.neighborSet x} := ⟨a, (D.adj_comm a x).mp hac⟩
      let v : {z : V // z ∈ D.neighborSet x} := ⟨b, (D.adj_comm b x).mp hbc⟩
      refine ⟨s(u, v), ?_, ?_⟩
      · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.induce_adj] using hab
      · dsimp [f, u, v]
        rw [Sym2.toFinset_mk_eq]
        ext z
        simp [or_left_comm, or_comm]

theorem sum_localEdges_eq_three_mul_cliques
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] :
    (∑ x : V, (D.induce (D.neighborSet x)).edgeFinset.card) =
      3 * (D.cliqueFinset 3).card := by
  simp_rw [localEdges_eq_cliques_containing D]
  calc
    (∑ x : V, ((D.cliqueFinset 3).filter (x ∈ ·)).card) =
        ∑ x : V, ∑ s ∈ D.cliqueFinset 3, if x ∈ s then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          simp
    _ = ∑ s ∈ D.cliqueFinset 3, ∑ x : V, if x ∈ s then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s ∈ D.cliqueFinset 3, s.card := by
          apply Finset.sum_congr rfl
          intro s _
          simp
    _ = 3 * (D.cliqueFinset 3).card := by
          rw [Nat.mul_comm]
          apply Finset.sum_const_nat
          intro s hs
          exact (SimpleGraph.mem_cliqueFinset_iff.mp hs).card_eq

theorem closedNeighborhood_residue_arith (q E C : ℕ) (hq : 1 ≤ q)
    (h : q * q * q + 2 * E + 2 * (q - 1) * (q * q) + 2 * (3 * C) =
      q * q * (q * (q - 1))) : Nat.ModEq 3 E q := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have hz := congrArg (fun n : ℕ => (n : ZMod 3)) h
  push_cast [Nat.cast_sub hq] at hz
  ring_nf at hz
  have hthree : (3 : ZMod 3) = 0 := by decide
  have hsix : (6 : ZMod 3) = 0 := by decide
  simp only [hthree, hsix, mul_zero, add_zero] at hz
  have hq3 : (q : ZMod 3) ^ 3 = (q : ZMod 3) := by
    exact ZMod.pow_card _
  have hq4 : (q : ZMod 3) ^ 4 = (q : ZMod 3) ^ 2 := by
    calc
      (q : ZMod 3) ^ 4 = (q : ZMod 3) * (q : ZMod 3) ^ 3 := by ring
      _ = (q : ZMod 3) * (q : ZMod 3) := by rw [hq3]
      _ = (q : ZMod 3) ^ 2 := by ring
  rw [hq3, hq4] at hz
  linear_combination 2 * hz - ((E : ZMod 3) + q - 2 * q ^ 2) * hthree

theorem closedNeighborhood_excess_modEq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (q : ℕ) (hq : 1 ≤ q) (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, D.degree x = q - 1) (e : V → ℕ)
    (hcut : ∀ x, finsetGraphCutSize D (insert x (D.neighborFinset x)) =
      q + 2 * e x) :
    Nat.ModEq 3 (∑ x, e x) q := by
  let t : V → ℕ := fun x =>
    (D.induce (D.neighborSet x)).edgeFinset.card
  have hsum :
      (∑ x : V, (finsetGraphCutSize D (insert x (D.neighborFinset x)) +
        (2 * (q - 1) + 2 * t x))) =
      ∑ x : V, ((q - 1) + 1) * (q - 1) := by
    apply Finset.sum_congr rfl
    intro x _
    exact closedNeighborhood_cut_add_two_mul_degree_add_two_mul_localEdges
      D hreg x
  have ht : (∑ x : V, t x) = 3 * (D.cliqueFinset 3).card := by
    exact sum_localEdges_eq_three_mul_cliques D
  have hglobal :
      q * q * q + 2 * (∑ x, e x) +
          2 * (q - 1) * (q * q) +
          2 * (3 * (D.cliqueFinset 3).card) =
        q * q * (q * (q - 1)) := by
    simp_rw [hcut] at hsum
    simp only [Finset.sum_add_distrib, Finset.sum_const] at hsum
    simp_rw [← Finset.mul_sum] at hsum
    simp [hcard] at hsum
    rw [ht] at hsum
    rw [Nat.sub_add_cancel hq] at hsum
    ring_nf at hsum ⊢
    exact hsum
  exact closedNeighborhood_residue_arith q (∑ x, e x)
    (D.cliqueFinset 3).card hq hglobal

/-- In residue class one, the triangle-incidence residue makes the total
closed-star cut energy exceed `q³` by at least two. -/
theorem cube_add_two_le_sum_closedNeighborhood_cut_of_mod_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (q : ℕ) (hq : 1 ≤ q) (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, D.degree x = q - 1) (e : V → ℕ)
    (hcut : ∀ x, finsetGraphCutSize D (insert x (D.neighborFinset x)) =
      q + 2 * e x)
    (hqmod : q % 3 = 1) :
    q * q * q + 2 ≤
      ∑ x : V, finsetGraphCutSize D (insert x (D.neighborFinset x)) := by
  apply cube_add_two_le_sum_of_pointwise_excess_mod_one q
    (fun x => finsetGraphCutSize D (insert x (D.neighborFinset x))) e
    hcard hcut
  · exact closedNeighborhood_excess_modEq_three D q hq hcard hreg e hcut
  · exact hqmod

/-- In residue class two, the triangle-incidence residue makes the total
closed-star cut energy exceed `q³` by at least four. -/
theorem cube_add_four_le_sum_closedNeighborhood_cut_of_mod_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (q : ℕ) (hq : 1 ≤ q) (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, D.degree x = q - 1) (e : V → ℕ)
    (hcut : ∀ x, finsetGraphCutSize D (insert x (D.neighborFinset x)) =
      q + 2 * e x)
    (hqmod : q % 3 = 2) :
    q * q * q + 4 ≤
      ∑ x : V, finsetGraphCutSize D (insert x (D.neighborFinset x)) := by
  apply cube_add_four_le_sum_of_pointwise_excess_mod_two q
    (fun x => finsetGraphCutSize D (insert x (D.neighborFinset x))) e
    hcard hcut
  · exact closedNeighborhood_excess_modEq_three D q hq hcard hreg e hcut
  · exact hqmod

end
end Erdos85

#print axioms Erdos85.localEdges_eq_cliques_containing
#print axioms Erdos85.sum_localEdges_eq_three_mul_cliques
#print axioms Erdos85.closedNeighborhood_excess_modEq_three
#print axioms Erdos85.cube_add_two_le_sum_closedNeighborhood_cut_of_mod_one
#print axioms Erdos85.cube_add_four_le_sum_closedNeighborhood_cut_of_mod_two
