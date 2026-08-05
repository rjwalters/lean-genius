import Proofs.Erdos85CycleCoverGraph

/-!
# Pair-mass quantization for oriented cyclic covers

A globally oriented selector between two labeled cycles has a simple but
useful consequence: for a fixed target displacement, either every translated
pair has the same selected source vertex, or none does.  Double-counting over
the source vertices therefore makes the corresponding anchor-pair mass either
zero or the full target-cycle length.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- For a globally orientation-preserving or orientation-reversing cycle map,
the assertion that a displacement fixes the selected source vertex is
independent of the target base point. -/
theorem cycleCoverMap_eq_translate_iff_zero
    {r n : ℕ} [NeZero r] [NeZero n]
    (f : ZMod n → ZMod r)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (δ t : ZMod n) :
    f (t + δ) = f t ↔ f δ = f 0 := by
  have hstep : ∀ y : ZMod n,
      (f ((y + 1) + δ) = f (y + 1) ↔ f (y + δ) = f y) := by
    intro y
    rcases horient with hforward | hreverse
    · rw [show (y + 1) + δ = (y + δ) + 1 by ring,
        hforward (y + δ), hforward y]
      constructor
      · exact add_right_cancel
      · intro h
        rw [h]
    · rw [show (y + 1) + δ = (y + δ) + 1 by ring,
        hreverse (y + δ), hreverse y]
      constructor
      · intro h
        have h' := congrArg (fun z : ZMod r ↦ z + 1) h
        simpa using h'
      · intro h
        rw [h]
  have hind : ∀ k : ℕ,
      (f (((k : ℕ) : ZMod n) + δ) = f ((k : ℕ) : ZMod n) ↔
        f δ = f 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.cast_succ, hstep]
        exact ih
  rw [← ZMod.natCast_zmod_val t]
  exact hind t.val

/-- **Cyclic-cover pair-mass quantization.**  Suppose adjacency from the
`r`-cycle labeled by `u` to the `n`-cycle labeled by `v` is the graph of a
globally oriented selector `f`.  For every displacement `δ`, the sum of
anchor-pair multiplicities over the whole source cycle is either zero or the
full target length `n`.

The Boolean condition is deliberately stated intrinsically as `f δ = f 0`;
when the cover degree is made explicit this is the usual divisibility
condition on `δ`.
-/
theorem sum_anchorPairMultiplicity_of_cycleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    {r n : ℕ} [NeZero r] [NeZero n]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ZMod r → V) (v : ZMod n → V)
    (f : ZMod n → ZMod r)
    (hadj : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (δ : ZMod n) :
    ∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ =
      if f δ = f 0 then n else 0 := by
  classical
  have hpair : ∀ x : ZMod r,
      anchorPairMultiplicity G (u x) v δ =
        (Finset.univ.filter fun t : ZMod n ↦
          x = f t ∧ x = f (t + δ)).card := by
    intro x
    rw [anchorPairMultiplicity]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_mixedAnchorSupport_iff, hadj]
  calc
    ∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ =
        ∑ t : ZMod n, ∑ x : ZMod r,
          if x = f t ∧ x = f (t + δ) then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [hpair x, Finset.card_filter]
    _ = ∑ t : ZMod n, if f (t + δ) = f t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : f (t + δ) = f t
      · simp [ht]
      · have ht' : f t ≠ f (t + δ) := fun h ↦ ht h.symm
        simp [ht, ht']
    _ = ∑ _t : ZMod n, if f δ = f 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [cycleCoverMap_eq_translate_iff_zero f horient δ t]
    _ = if f δ = f 0 then n else 0 := by
      split_ifs <;> simp [Finset.card_univ, ZMod.card]

/-- Set-valued form of pair-mass quantization, convenient for downstream
parity and partition arguments. -/
theorem sum_anchorPairMultiplicity_of_cycleCover_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {r n : ℕ} [NeZero r] [NeZero n]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ZMod r → V) (v : ZMod n → V)
    (f : ZMod n → ZMod r)
    (hadj : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (δ : ZMod n) :
    (∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ) ∈ ({0, n} : Set ℕ) := by
  rw [sum_anchorPairMultiplicity_of_cycleCover G u v f hadj horient δ]
  by_cases h : f δ = f 0 <;> simp [h]

/-- Boundary-graph wrapper: a quotient entry `Q(e,c)=1` directly quantizes
the contribution of the entire `c`-component to pair multiplicities on the
`e`-component.  This is the form used by the mixed-cycle parity assembly. -/
theorem sum_anchorPairMultiplicity_mem_of_componentQuotient_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (hone : componentQuotientMatrix G (secondOrderDefectGraph G) e c = 1)
    (δ : ZMod n) :
    (∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ) ∈ ({0, n} : Set ℕ) := by
  obtain ⟨f, hadj, horient⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one G hfree hd heven hmin
      hcard hr hn c e u v huinj hvinj huRange hvRange huD hvD hone
  exact sum_anchorPairMultiplicity_of_cycleCover_mem G u v f hadj horient δ

end

end Erdos85
