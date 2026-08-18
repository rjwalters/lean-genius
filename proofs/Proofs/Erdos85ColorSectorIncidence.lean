import Proofs.Erdos85CycleCoverColorRigidity

/-!
# Incidence identities forced by the triangle-free color sector

The color-rigidity theorems make the triangle-free defect components an
independent diagonal-two sector of the component quotient.  This file records
the exact consequences of the quotient square equation abstractly: every
off-diagonal square entry between two such components factors entirely
through the complementary (antipodal-colored) sector.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- The components whose chosen cyclic rim consists of edges of `G`.  By the
local monochromaticity theorem, this is exactly the triangle-free-colored
sector; phrasing it through a mixed cycle labeling makes the quotient
interfaces immediately usable. -/
def triangleFreeCycleSector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V) :
    Finset (secondOrderDefectGraph G).ConnectedComponent :=
  Finset.univ.filter fun c ↦ ∀ x, G.Adj (u c x) (u c (x + 1))

@[simp] theorem mem_triangleFreeCycleSector_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    c ∈ triangleFreeCycleSector G u ↔
      ∀ x, G.Adj (u c x) (u c (x + 1)) := by
  simp [triangleFreeCycleSector]

/-- The graph triangle-free cycle sector is diagonal-two. -/
theorem triangleFreeCycleSector_diagonalQuotient_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    {c : (secondOrderDefectGraph G).ConnectedComponent}
    (hc : c ∈ triangleFreeCycleSector G u) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 := by
  exact triangleFreeCycleComponent_diagonalQuotient_eq_two G hfree hd heven
    hmin hcard (hr c) c (u c) (hu c) (huRange c) (huD c)
    ((mem_triangleFreeCycleSector_iff G u c).mp hc)

/-- Distinct graph triangle-free cycle components have zero quotient entry. -/
theorem triangleFreeCycleSector_offDiagonalQuotient_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hc : c ∈ triangleFreeCycleSector G u)
    (he : e ∈ triangleFreeCycleSector G u) (hce : c ≠ e) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0 := by
  exact componentQuotient_eq_zero_of_both_triangleFree_cycles G hfree hd
    heven hmin hcard (hr c) (hr e) c e hce (u c) (u e) (hu c) (hu e)
    (huRange c) (huRange e) (huD c) (huD e)
    ((mem_triangleFreeCycleSector_iff G u c).mp hc)
    ((mem_triangleFreeCycleSector_iff G u e).mp he)

/-- If a sector `S` has diagonal two and no off-diagonal entries, then the
off-diagonal square entry between two distinct vertices of `S` factors
entirely through its complement. -/
theorem sum_complementary_products_eq_of_independent_diagonal_two_sector
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (a : ℕ) (S : Finset C)
    (hsq : ∀ c e, (Q * Q) c e =
      a * (if c = e then 1 else 0) + size e)
    (hoff : ∀ c ∈ S, ∀ e ∈ S, c ≠ e → Q c e = 0)
    {c e : C} (hc : c ∈ S) (he : e ∈ S) (hce : c ≠ e) :
    ∑ j ∈ Finset.univ.filter (fun j : C ↦ j ∉ S), Q c j * Q j e =
      size e := by
  have hinternal : ∑ j ∈ S, Q c j * Q j e = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjc : j = c
    · subst j
      rw [hoff c hc e he hce]
      simp
    · rw [hoff c hc j hj (fun h ↦ hjc h.symm)]
      simp
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : C ↦ j ∈ S) (fun j ↦ Q c j * Q j e)
  have htotal : ∑ j, Q c j * Q j e = size e := by
    have hs := hsq c e
    simp only [Matrix.mul_apply, if_neg hce, mul_zero, zero_add] at hs
    exact hs
  have hinside :
      ∑ j ∈ Finset.univ.filter (fun j : C ↦ j ∈ S), Q c j * Q j e = 0 := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using hinternal
  rw [hinside, zero_add] at hsplit
  rw [← htotal, hsplit]

/-- The diagonal square entry of a diagonal-two independent sector leaves
exactly `a + size c - 4` two-step mass through the complementary sector. -/
theorem sum_complementary_products_self_of_independent_diagonal_two_sector
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (a : ℕ) (S : Finset C)
    (hsq : ∀ c e, (Q * Q) c e =
      a * (if c = e then 1 else 0) + size e)
    (hdiag : ∀ c ∈ S, Q c c = 2)
    (hoff : ∀ c ∈ S, ∀ e ∈ S, c ≠ e → Q c e = 0)
    {c : C} (hc : c ∈ S) :
    (∑ j ∈ Finset.univ.filter (fun j : C ↦ j ∉ S), Q c j * Q j c) + 4 =
      a + size c := by
  have hinternal : ∑ j ∈ S, Q c j * Q j c = 4 := by
    rw [Finset.sum_eq_single c]
    · simp [hdiag c hc]
    · intro j hj hjc
      rw [hoff c hc j hj (fun h ↦ hjc h.symm)]
      simp
    · exact fun h ↦ (h hc).elim
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : C ↦ j ∈ S) (fun j ↦ Q c j * Q j c)
  have htotal : ∑ j, Q c j * Q j c = a + size c := by
    have hs := hsq c c
    simp only [Matrix.mul_apply, if_pos, mul_one] at hs
    exact hs
  have hinside :
      ∑ j ∈ Finset.univ.filter (fun j : C ↦ j ∈ S), Q c j * Q j c = 4 := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using hinternal
  rw [hinside] at hsplit
  rw [← htotal]
  omega

/-- In a constant-row-sum quotient, a diagonal-two independent sector sends
exactly the remaining `d - 2` units of every row into its complement. -/
theorem sum_complementary_row_eq_of_independent_diagonal_two_sector
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (d : ℕ) (S : Finset C)
    (hrow : ∀ c, ∑ e, Q c e = d)
    (hdiag : ∀ c ∈ S, Q c c = 2)
    (hoff : ∀ c ∈ S, ∀ e ∈ S, c ≠ e → Q c e = 0)
    {c : C} (hc : c ∈ S) :
    (∑ e ∈ Finset.univ.filter (fun e : C ↦ e ∉ S), Q c e) + 2 = d := by
  have hinternal : ∑ e ∈ S, Q c e = 2 := by
    rw [Finset.sum_eq_single c]
    · exact hdiag c hc
    · intro e he hec
      exact hoff c hc e he (fun h ↦ hec h.symm)
    · exact fun h ↦ (h hc).elim
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e : C ↦ e ∈ S) (fun e ↦ Q c e)
  have hinside : ∑ e ∈ Finset.univ.filter (fun e : C ↦ e ∈ S), Q c e = 2 := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using hinternal
  rw [hinside] at hsplit
  rw [← hrow c]
  omega

end

end Erdos85
