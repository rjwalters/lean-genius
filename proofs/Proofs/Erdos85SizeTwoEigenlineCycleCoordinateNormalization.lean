import Proofs.Erdos85OrderSixtyFourTenSixComponentLabeling

/-!
# Cycle coordinates aligned with an alternating eigenline

The cyclic grid model needs more than an abstract statement that a connected
two-regular component is a cycle: its coordinates must also agree with the
alternating sign carried by the size-two eigenline.  The result below is
uniform in `q`.  It chooses `C_{2q}` coordinates preserving adjacency and
proves that the sign in those coordinates is exactly the parity character.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Consecutive non-wrapping coordinates are adjacent in a cycle graph. -/
private theorem cycleGraph_adj_castSucc_succ
    {n : Nat} (i : Fin n) :
    (cycleGraph (n + 1)).Adj i.castSucc i.succ := by
  change (cycleGraph (n + 1)).Adj
    ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩
  rw [cycleGraph_adj']
  right
  simp [Fin.sub_val_of_le]

/-- Casting the modulus along an equality preserves cyclic adjacency. -/
private theorem cycleGraph_adj_finCongr
    {m n : Nat} (h : m = n) (i j : Fin m) :
    (cycleGraph m).Adj i j ↔
      (cycleGraph n).Adj (finCongr h i) (finCongr h j) := by
  subst n
  rfl

/-- A cycle coordinate equivalence transports an edge-flipping sign to the
parity character.  This is the phase-alignment part of cycle normalization. -/
theorem componentCycleEquiv_sign_eq_parity
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (n : Nat)
    (c : H.ConnectedComponent)
    (e : Fin (n + 1) ≃ c.supp)
    (he : ∀ i j, (cycleGraph (n + 1)).Adj i j ↔
      H.Adj (e i).1 (e j).1)
    (s : V → ℤ)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    ∀ i : Fin (n + 1),
      s (e i).1 = (-1 : ℤ) ^ i.val * s (e 0).1 := by
  intro i
  induction i using Fin.induction with
  | zero => simp
  | succ k ih =>
      have hadjCycle :
          (cycleGraph (n + 1)).Adj k.castSucc k.succ := by
        exact cycleGraph_adj_castSucc_succ k
      have hf := hflip ((he k.castSucc k.succ).mp hadjCycle)
      calc
        s (e k.succ).1 = -s (e k.castSucc).1 := by omega
        _ = (-1 : ℤ) ^ k.succ.val * s (e 0).1 := by
          rw [ih]
          simp [pow_succ]

/-- A connected component of order `2q` in a finite two-regular graph admits
standard `C_{2q}` coordinates simultaneously preserving adjacency and
normalizing every edge-flipping signed eigenline to parity. -/
theorem exists_componentCycleEquiv_sign_normalized
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (q : Nat) (hq : 1 ≤ q)
    (c : H.ConnectedComponent) (hc : c.supp.ncard = 2 * q)
    (s : V → ℤ)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    ∃ e : Fin (2 * q) ≃ c.supp,
      (∀ i j, (cycleGraph (2 * q)).Adj i j ↔
        H.Adj (e i).1 (e j).1) ∧
      ∀ i : Fin (2 * q),
        s (e i).1 = (-1 : ℤ) ^ i.val *
          s (e ⟨0, by omega⟩).1 := by
  have hn : 2 * q = (2 * q - 1) + 1 := by omega
  have hc' : c.supp.ncard = (2 * q - 1) + 1 := hc.trans hn
  obtain ⟨e', he'⟩ :=
    exists_componentCycleEquiv H hdeg c ((2 * q - 1) + 1) hc'
  let e : Fin (2 * q) ≃ c.supp := (finCongr hn).trans e'
  have he : ∀ i j, (cycleGraph (2 * q)).Adj i j ↔
      H.Adj (e i).1 (e j).1 := by
    intro i j
    simpa [e] using (cycleGraph_adj_finCongr hn i j).trans
      (he' (finCongr hn i) (finCongr hn j))
  refine ⟨e, he, ?_⟩
  intro i
  simpa [e] using componentCycleEquiv_sign_eq_parity H (2 * q - 1)
    c e' he' s hflip (finCongr hn i)

end

end Erdos85

#print axioms Erdos85.exists_componentCycleEquiv_sign_normalized
