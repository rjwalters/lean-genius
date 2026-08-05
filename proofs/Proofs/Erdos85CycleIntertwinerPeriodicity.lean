import Proofs.Erdos85SecondOrderColorTrace
import Mathlib.GroupTheory.OrderOfElement

/-!
# Periodicity of cycle intertwiners

The full commutation relation with a disjoint union of cycles contains more
information than the equitable quotient.  The elementary engine is that a
finite cyclic integer sequence with vanishing second difference is constant.
This file develops that engine before applying it to rectangular blocks that
intertwine two cycle adjacency matrices.
-/

namespace Erdos85

/-- The symmetric one-step translation operator in direction `a`. -/
def cycleCosineOp {α : Type*} [AddCommGroup α]
    (a : α) (f : α → ℤ) (x : α) : ℤ :=
  f (x - a) + f (x + a)

/-- The integral Chebyshev recurrence for symmetric translation.  Its `k`th
value is translation by `k • a` plus translation by `-(k • a)`. -/
def cycleCosineIter {α : Type*} [AddCommGroup α] (a : α) :
    ℕ → (α → ℤ) → (α → ℤ)
  | 0, f => 2 • f
  | 1, f => cycleCosineOp a f
  | k + 2, f => cycleCosineOp a (cycleCosineIter a (k + 1) f) -
      cycleCosineIter a k f

theorem cycleCosineIter_apply
    {α : Type*} [AddCommGroup α]
    (a : α) (k : ℕ) (f : α → ℤ) (x : α) :
    cycleCosineIter a k f x = f (x - k • a) + f (x + k • a) := by
  induction k using Nat.twoStepInduction generalizing x with
  | zero => simp [cycleCosineIter]; ring
  | one => simp [cycleCosineIter, cycleCosineOp]
  | more k hk hk1 =>
      rw [cycleCosineIter]
      simp only [Pi.sub_apply, cycleCosineOp]
      rw [hk1 (x - a), hk1 (x + a), hk x]
      have hm₁ : x - a - (k + 1) • a = x - (k + 2) • a := by
        simp only [add_nsmul, one_nsmul, two_nsmul]
        abel
      have hm₂ : x + a - (k + 1) • a = x - k • a := by
        simp only [add_nsmul, one_nsmul]
        abel
      have hp₁ : x - a + (k + 1) • a = x + k • a := by
        simp only [add_nsmul, one_nsmul]
        abel
      have hp₂ : x + a + (k + 1) • a = x + (k + 2) • a := by
        simp only [add_nsmul, one_nsmul, two_nsmul]
        abel
      rw [hm₁, hm₂, hp₁, hp₂]
      ring

/-- Intertwining the one-step symmetric translations intertwines every term
of their integral Chebyshev recurrence. -/
theorem LinearMap.map_cycleCosineIter
    {α β : Type*} [AddCommGroup α] [AddCommGroup β]
    (L : (β → ℤ) →ₗ[ℤ] (α → ℤ)) (a : α) (b : β)
    (h : ∀ f, L (cycleCosineOp b f) = cycleCosineOp a (L f))
    (k : ℕ) (f : β → ℤ) :
    L (cycleCosineIter b k f) = cycleCosineIter a k (L f) := by
  induction k using Nat.twoStepInduction with
  | zero =>
      change L ((2 : ℤ) • f) = (2 : ℤ) • L f
      exact L.map_smul (2 : ℤ) f
  | one =>
      exact h f
  | more k hk hk1 =>
      rw [cycleCosineIter, cycleCosineIter, L.map_sub,
        h (cycleCosineIter b (k + 1) f), hk, hk1]

/-- An integer-valued function on a finite additive group whose second
difference in direction `a` vanishes is constant along translation by `a`.
The torsion-freeness of `ℤ` is essential. -/
theorem eq_add_of_add_secondDifference_eq_two_mul
    {α : Type*} [AddCommGroup α] [Finite α]
    (f : α → ℤ) (a x : α)
    (h : ∀ y, f (y - a) + f (y + a) = 2 * f y) :
    f (x + a) = f x := by
  let n := addOrderOf a
  have hn : 0 < n := addOrderOf_pos a
  have hstep : ∀ y, f (y + a) - f y = f y - f (y - a) := by
    intro y
    have hy := h y
    omega
  have hlinear : ∀ k : ℕ,
      f (x + (k • a)) = f x + (k : ℤ) * (f (x + a) - f x) := by
    apply Nat.twoStepInduction
    · simp
    · simp
    · intro k hk hk1
      have hs := hstep (x + (k + 1) • a)
      have hminus : x + (k + 1) • a - a = x + k • a := by
        simp only [add_nsmul, one_nsmul]
        abel
      have hplus : x + (k + 1) • a + a = x + (k + 2) • a := by
        simp only [add_nsmul, one_nsmul, two_nsmul]
        abel
      rw [hminus, hplus, hk, hk1] at hs
      push_cast at hs ⊢
      ring_nf at hs ⊢
      omega
  have hperiod : n • a = 0 := addOrderOf_nsmul_eq_zero a
  have hnlin := hlinear n
  rw [hperiod, add_zero] at hnlin
  have hzero : (f (x + a) - f x) = 0 := by
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    nlinarith
  omega

/-- Translation invariance in one direction extends to every integral
multiple of that direction. -/
theorem eq_add_zsmul_of_eq_add
    {α : Type*} [AddCommGroup α] (f : α → ℤ) (a : α)
    (h : ∀ x, f (x + a) = f x) (z : ℤ) (x : α) :
    f (x + z • a) = f x := by
  have hback : ∀ y, f (y - a) = f y := by
    intro y
    have hy := h (y - a)
    simpa only [sub_add_cancel] using hy.symm
  induction z using Int.induction_on generalizing x with
  | zero => simp
  | succ z ih =>
      have heq : x + ((z : ℤ) + 1) • a =
          (x + (z : ℤ) • a) + a := by
        rw [add_zsmul, one_zsmul]
        abel
      rw [heq, h, ih]
  | pred z ih =>
      have heq : x + (-(z : ℤ) - 1) • a =
          (x - a) + (-(z : ℤ)) • a := by
        rw [sub_zsmul, one_zsmul]
        abel
      rw [heq, ih, hback]

/-- A linear map intertwining two cycle translations has output periodic in
the source direction by the additive order of the target step. -/
theorem LinearMap.cycleIntertwiner_periodic
    {α β : Type*} [AddCommGroup α] [Finite α]
    [AddCommGroup β] [Finite β]
    (L : (β → ℤ) →ₗ[ℤ] (α → ℤ)) (a : α) (b : β)
    (h : ∀ f, L (cycleCosineOp b f) = cycleCosineOp a (L f))
    (f : β → ℤ) (x : α) :
    (L f) (x + addOrderOf b • a) = (L f) x := by
  let n := addOrderOf b
  have hnb : n • b = 0 := addOrderOf_nsmul_eq_zero b
  have hinter := Erdos85.LinearMap.map_cycleCosineIter L a b h n f
  have htarget : cycleCosineIter b n f = (2 : ℤ) • f := by
    funext z
    rw [cycleCosineIter_apply, hnb, sub_zero, add_zero]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsecond : ∀ y : α,
      (L f) (y - n • a) + (L f) (y + n • a) = 2 * (L f) y := by
    intro y
    have hy := congrFun hinter y
    rw [htarget, L.map_smul, cycleCosineIter_apply] at hy
    simpa only [Pi.smul_apply, smul_eq_mul] using hy.symm
  exact eq_add_of_add_secondDifference_eq_two_mul
    (L f) (n • a) x hsecond

/-- Rectangular-matrix form: an integer block intertwining the symmetric
cycle translations has rows periodic by the target cycle order. -/
theorem Matrix.row_periodic_of_cycleCosine_intertwine
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]
    [Fintype β] [DecidableEq β] [AddCommGroup β]
    (B : Matrix α β ℤ) (a : α) (b : β)
    (h : ∀ f, B.mulVec (cycleCosineOp b f) =
      cycleCosineOp a (B.mulVec f))
    (x : α) (j : β) :
    B (x + addOrderOf b • a) j = B x j := by
  let e : β → ℤ := Pi.single j 1
  have hp := Erdos85.LinearMap.cycleIntertwiner_periodic
    B.mulVecLin a b h e x
  simpa [e, Matrix.mulVec, dotProduct_single_one] using hp

/-- Entrywise form of cycle-block commutation implies the functional
intertwining identity used above.  The only extra step is reindexing the two
finite target sums by cyclic translation. -/
theorem Matrix.mulVec_cycleCosineOp_eq_of_entry_intertwine
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]
    [Fintype β] [DecidableEq β] [AddCommGroup β]
    (B : Matrix α β ℤ) (a : α) (b : β)
    (h : ∀ x y,
      B (x - a) y + B (x + a) y = B x (y + b) + B x (y - b))
    (f : β → ℤ) :
    B.mulVec (cycleCosineOp b f) = cycleCosineOp a (B.mulVec f) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, cycleCosineOp]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  let ep : β ≃ β :=
    { toFun := fun y => y + b
      invFun := fun y => y - b
      left_inv := fun y => add_sub_cancel_right y b
      right_inv := fun y => sub_add_cancel y b }
  let em : β ≃ β :=
    { toFun := fun y => y - b
      invFun := fun y => y + b
      left_inv := fun y => sub_add_cancel y b
      right_inv := fun y => add_sub_cancel_right y b }
  rw [← Equiv.sum_comp ep
      (fun y => B x y * f (y - b)),
    ← Equiv.sum_comp em
      (fun y => B x y * f (y + b))]
  have hep : ∀ y, ep y = y + b := fun _ => rfl
  have hem : ∀ y, em y = y - b := fun _ => rfl
  simp_rw [hep, hem, add_sub_cancel_right, sub_add_cancel]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← add_mul, ← add_mul, h]

/-- Direct entrywise version of row periodicity, tailored to rectangular
blocks cut out of a commuting pair of graph adjacency matrices. -/
theorem Matrix.row_periodic_of_entry_cycleIntertwine
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]
    [Fintype β] [DecidableEq β] [AddCommGroup β]
    (B : Matrix α β ℤ) (a : α) (b : β)
    (h : ∀ x y,
      B (x - a) y + B (x + a) y = B x (y + b) + B x (y - b))
    (x : α) (j : β) :
    B (x + addOrderOf b • a) j = B x j := by
  apply Matrix.row_periodic_of_cycleCosine_intertwine B a b
  exact Matrix.mulVec_cycleCosineOp_eq_of_entry_intertwine B a b h

/-- The same row periodicity for every integral multiple of the target
cycle order. -/
theorem Matrix.row_periodic_zsmul_of_cycleCosine_intertwine
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]
    [Fintype β] [DecidableEq β] [AddCommGroup β]
    (B : Matrix α β ℤ) (a : α) (b : β)
    (h : ∀ f, B.mulVec (cycleCosineOp b f) =
      cycleCosineOp a (B.mulVec f))
    (z : ℤ) (x : α) (j : β) :
    B (x + z • (addOrderOf b • a)) j = B x j := by
  apply eq_add_zsmul_of_eq_add (fun y => B y j) (addOrderOf b • a)
  intro y
  exact Erdos85.Matrix.row_periodic_of_cycleCosine_intertwine B a b h y j

/-- Graph form of the rectangular-block theorem: translating the source by
the target cycle order preserves every adjacency entry in that target block. -/
theorem adj_iff_add_targetOrder_of_entry_cycleIntertwine
    {V α β : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α] [AddCommGroup α]
    [Fintype β] [DecidableEq β] [AddCommGroup β]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : α → V) (v : β → V) (a : α) (b : β)
    (h : ∀ x y,
      G.adjMatrix ℤ (u (x - a)) (v y) +
          G.adjMatrix ℤ (u (x + a)) (v y) =
        G.adjMatrix ℤ (u x) (v (y + b)) +
          G.adjMatrix ℤ (u x) (v (y - b)))
    (x : α) (j : β) :
    G.Adj (u (x + addOrderOf b • a)) (v j) ↔ G.Adj (u x) (v j) := by
  let B : Matrix α β ℤ := fun i k => G.adjMatrix ℤ (u i) (v k)
  have hp := Matrix.row_periodic_of_entry_cycleIntertwine B a b h x j
  change G.adjMatrix ℤ (u (x + addOrderOf b • a)) (v j) =
    G.adjMatrix ℤ (u x) (v j) at hp
  constructor <;> intro hadj
  · by_contra hn
    simp [SimpleGraph.adjMatrix_apply, hadj, hn] at hp
  · by_contra hn
    simp [SimpleGraph.adjMatrix_apply, hadj, hn] at hp

/-- If two distinct source vertices have identical adjacency on a target
set, every selected target neighbor is common, so `C₄`-freeness bounds their
number by one. -/
theorem card_filter_adj_le_one_of_periodic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x x' : V) (S : Finset V)
    (hne : x' ≠ x)
    (hperiod : ∀ y ∈ S, G.Adj x' y ↔ G.Adj x y) :
    (S.filter fun y => G.Adj x y).card ≤ 1 := by
  have hsub : (S.filter fun y => G.Adj x y) ⊆
      G.neighborFinset x ∩ G.neighborFinset x' := by
    intro y hy
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hxy : G.Adj x y := (Finset.mem_filter.mp hy).2
    have hx'y : G.Adj x' y := (hperiod y hyS).mpr hxy
    simp [SimpleGraph.mem_neighborFinset, hxy, hx'y, G.adj_comm]
  exact (Finset.card_le_card hsub).trans
    (common_le_one_of_not_containsC4 hfree x x' hne.symm)

end Erdos85
