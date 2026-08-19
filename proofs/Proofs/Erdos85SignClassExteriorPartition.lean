import Proofs.Erdos85SizeTwoEigenlineGridInstantiation

/-!
# The sign-class exterior partition

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3 (shape-independent layer,
dual to the owner tiling law).

The same-sign census (`sameSign_common_mem_supp`) says no same-sign pair
of a size-two eigenline component has an exterior common neighbour.
Dually packaged: the exterior neighbourhoods of one sign class are
pairwise disjoint (`sameSign_exterior_disjoint`), and every exterior
vertex owns exactly one internal neighbour of each sign
(`exteriorOwner_pair_opposite_sign`, `exteriorOwner_one_per_sign`) —
so every owner pair is automatically an opposite-sign pair, in every
stratum of the node, with no shape hypothesis.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (antipodalGraph G).Adj]
variable [DecidableRel (triangleFreeEdgeGraph G).Adj]
variable [Fintype (secondOrderDefectGraph G).ConnectedComponent]
variable [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]

/-- **Sign-class exterior disjointness.**  Two distinct same-sign internal
vertices have disjoint exterior neighbourhoods. -/
theorem sameSign_exterior_disjoint (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    {z z' : V} (hz : z ∈ c.supp) (hz' : z' ∈ c.supp)
    (hne : z' ≠ z) (hsign : s z' = s z) :
    Disjoint ((G.neighborFinset z).filter (fun y => y ∉ c.supp))
      ((G.neighborFinset z').filter (fun y => y ∉ c.supp)) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu hu'
  exact hu.2 (sameSign_common_mem_supp G hfree hq hreg hcard c hc s hs_in
    hs_out hsum hA_in hDs hz hz' hne hsign hu.1.symm hu'.1.symm)

/-- **Owner pairs are opposite-sign.**  The two internal neighbours of an
exterior vertex carry opposite signs. -/
theorem exteriorOwner_pair_opposite_sign (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    {u : V} (hu : u ∉ c.supp)
    {z z' : V}
    (hz : z ∈ componentNeighborFinset G (secondOrderDefectGraph G) c u)
    (hz' : z' ∈ componentNeighborFinset G (secondOrderDefectGraph G) c u)
    (hne : z' ≠ z) :
    s z' = -(s z) := by
  rw [componentNeighborFinset, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset] at hz hz'
  have hzc : z ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c z).mpr hz.2
  have hzc' : z' ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c z').mpr hz'.2
  by_contra hopp
  have hsign : s z' = s z := by
    rcases hs_in z hzc with h | h <;> rcases hs_in z' hzc' with h' | h' <;>
      rw [h, h'] <;> rw [h, h'] at hopp <;> first | rfl | norm_num at hopp
  exact hu (sameSign_common_mem_supp G hfree hq hreg hcard c hc s hs_in
    hs_out hsum hA_in hDs hzc hzc' hne hsign hz.1 hz'.1)

/-- **One internal neighbour per sign.**  An exterior vertex has exactly
one internal neighbour of each sign. -/
theorem exteriorOwner_one_per_sign (hfree : ¬ containsC4 V G)
    {q : ℕ} (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    {u : V} (hu : u ∉ c.supp) :
    ((componentNeighborFinset G (secondOrderDefectGraph G) c u).filter
      (fun y => s y = 1)).card = 1 ∧
    ((componentNeighborFinset G (secondOrderDefectGraph G) c u).filter
      (fun y => s y = -1)).card = 1 := by
  have hucomp : (secondOrderDefectGraph G).connectedComponentMk u ≠ c := by
    intro h
    exact hu ((SimpleGraph.ConnectedComponent.mem_supp_iff c u).mpr h)
  have hpair :
      (componentNeighborFinset G (secondOrderDefectGraph G) c u).card = 2 := by
    have hmem : u ∈ ((secondOrderDefectGraph G).connectedComponentMk u).supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ u).mpr rfl
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (by omega) hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk u) c hmem
    rw [hc] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hpair
  have hamem : a ∈ componentNeighborFinset G (secondOrderDefectGraph G) c u := by
    rw [hset]
    exact Finset.mem_insert_self a {b}
  have hbmem : b ∈ componentNeighborFinset G (secondOrderDefectGraph G) c u := by
    rw [hset]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hopp : s b = -(s a) :=
    exteriorOwner_pair_opposite_sign G hfree hq hreg hcard c hc s hs_in
      hs_out hsum hA_in hDs hu hamem hbmem (Ne.symm hab)
  have hac : a ∈ c.supp := by
    rw [componentNeighborFinset, Finset.mem_filter] at hamem
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c a).mpr hamem.2
  have hfilter : ∀ t : ℤ,
      ((componentNeighborFinset G (secondOrderDefectGraph G) c u).filter
        (fun y => s y = t)) = ({a, b} : Finset V).filter (fun y => s y = t) := by
    intro t
    rw [hset]
  rcases hs_in a hac with hsa | hsa
  · -- `s a = -1`, `s b = 1`
    have hsb : s b = 1 := by rw [hopp, hsa]; norm_num
    constructor
    · rw [hfilter 1]
      have : (({a, b} : Finset V).filter (fun y => s y = 1)) = {b} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h | h, hy⟩
          · subst h; rw [hsa] at hy; norm_num at hy
          · exact h
        · intro h
          subst h
          exact ⟨Or.inr rfl, hsb⟩
      rw [this, Finset.card_singleton]
    · rw [hfilter (-1)]
      have : (({a, b} : Finset V).filter (fun y => s y = -1)) = {a} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h | h, hy⟩
          · exact h
          · subst h; rw [hsb] at hy; norm_num at hy
        · intro h
          subst h
          exact ⟨Or.inl rfl, hsa⟩
      rw [this, Finset.card_singleton]
  · -- `s a = 1`, `s b = -1`
    have hsb : s b = -1 := by rw [hopp, hsa]
    constructor
    · rw [hfilter 1]
      have : (({a, b} : Finset V).filter (fun y => s y = 1)) = {a} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h | h, hy⟩
          · exact h
          · subst h; rw [hsb] at hy; norm_num at hy
        · intro h
          subst h
          exact ⟨Or.inl rfl, hsa⟩
      rw [this, Finset.card_singleton]
    · rw [hfilter (-1)]
      have : (({a, b} : Finset V).filter (fun y => s y = -1)) = {b} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h | h, hy⟩
          · subst h; rw [hsa] at hy; norm_num at hy
          · exact h
        · intro h
          subst h
          exact ⟨Or.inr rfl, hsb⟩
      rw [this, Finset.card_singleton]

end

end Erdos85

#print axioms Erdos85.sameSign_exterior_disjoint
#print axioms Erdos85.exteriorOwner_pair_opposite_sign
#print axioms Erdos85.exteriorOwner_one_per_sign
