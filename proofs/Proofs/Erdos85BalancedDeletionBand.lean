import Proofs.Erdos85ControlledDeletion

/-!
# Balanced vertex deletion bands

A single large deletion set whose incidence is uniformly bounded produces a
whole interval of `C₄`-free minimum-degree witnesses: delete any smaller
subset.  This is the deterministic interface needed by the probabilistic
balanced-deletion route for polarity graphs.
-/

open SimpleGraph

namespace Erdos85

/-- Every vertex, including vertices of `D`, has at most `r` neighbors in
`D`.  Quantifying over all vertices is what makes the property hereditary
under replacing `D` by an arbitrary subset. -/
def UniformDeletionLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (r : ℕ) : Prop :=
  ∀ v : V, (G.neighborFinset v ∩ D).card ≤ r

theorem UniformDeletionLoss.mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D E : Finset V} {r : ℕ}
    (hD : UniformDeletionLoss G D r) (hED : E ⊆ D) :
    UniformDeletionLoss G E r := by
  intro v
  have hinter : G.neighborFinset v ∩ E ⊆ G.neighborFinset v ∩ D := by
    intro x hx
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨hx.1, hED hx.2⟩
  exact (Finset.card_le_card hinter).trans (hD v)

/-- A uniformly controlled deletion set of size `L` supplies witnesses after
deleting any `k ≤ L` of its vertices. -/
theorem c4FreeMinDegreeWitness_uniformDeletionBand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) {N q d L : ℕ}
    (hcard : Fintype.card V = N) (hDcard : D.card = L)
    (hfree : ¬ containsC4 V G) (hmin : q ≤ G.minDegree)
    (hdq : d ≤ q) (hloss : UniformDeletionLoss G D (q - d))
    {k : ℕ} (hk : k ≤ L) (hremain : 1 ≤ N - k) :
    C4FreeMinDegreeWitness (N - k) d := by
  obtain ⟨E, hED, hEcard⟩ :=
    Finset.exists_subset_card_eq (hDcard ▸ hk)
  have hlossE : ∀ v : {v : V // v ∉ E},
      (G.neighborFinset v ∩ E).card ≤ q - d := by
    intro v
    exact (hloss.mono hED) v
  have hw := c4FreeMinDegreeWitness_delete_vertex_set
    G E hcard hEcard hremain hmin hfree hlossE
  simpa [Nat.sub_sub_self hdq] using hw

/-- Interval-indexed form: a uniform deletion set gives every retained order
between `N-L` and `N`. -/
theorem c4FreeMinDegreeWitness_of_mem_uniformDeletionBand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) {N q d L n : ℕ}
    (hcard : Fintype.card V = N) (hDcard : D.card = L)
    (hfree : ¬ containsC4 V G) (hmin : q ≤ G.minDegree)
    (hdq : d ≤ q) (hloss : UniformDeletionLoss G D (q - d))
    (hnlow : N - L ≤ n) (hnhigh : n ≤ N) (hnpos : 1 ≤ n) :
    C4FreeMinDegreeWitness n d := by
  have hk : N - n ≤ L := by omega
  have heq : N - (N - n) = n := by omega
  rw [← heq]
  exact c4FreeMinDegreeWitness_uniformDeletionBand
    G D hcard hDcard hfree hmin hdq hloss hk (by omega)

end Erdos85
