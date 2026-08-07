import Proofs.Erdos85Problem

/-!
# A common-neighbor pigeonhole principle

In a `C₄`-free graph, if a fixed vertex `x` and a target vertex `yᵢ` share a
selected common neighbor `zᵢ`, then distinct selected common neighbors must
have distinct targets.  This elementary injection is the counting core of
the uniform clean high-root branch obstruction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Selected distinct common neighbors of a fixed vertex inject into any
finset containing their opposite endpoints. -/
theorem card_le_of_commonNeighbor_selectors
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (I : Finset ι) (T : Finset V) (x : V)
    (z y : ι → V)
    (hz_inj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → z i ≠ z j)
    (hy_mem : ∀ i ∈ I, y i ∈ T)
    (hxy : ∀ i ∈ I, x ≠ y i)
    (hzx : ∀ i ∈ I, G.Adj (z i) x)
    (hzy : ∀ i ∈ I, G.Adj (z i) (y i)) :
    I.card ≤ T.card := by
  let target : {i // i ∈ I} → {v // v ∈ T} := fun i =>
    ⟨y i.1, hy_mem i.1 i.2⟩
  have htarget_injective : Function.Injective target := by
    intro i j hij
    apply Subtype.ext
    by_contra hijIndex
    have hyij : y i.1 = y j.1 := congrArg Subtype.val hij
    have hzneq : z i.1 ≠ z j.1 :=
      hz_inj i.1 i.2 j.1 j.2 hijIndex
    apply hfree
    apply containsC4_of_two_common
      (hxy i.1 i.2) hzneq (hzx i.1 i.2) (hzy i.1 i.2)
        (hzx j.1 j.2)
    simpa [hyij] using hzy j.1 j.2
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective target htarget_injective

/-- Contradiction form of `card_le_of_commonNeighbor_selectors`. -/
theorem false_of_commonNeighbor_selectors_card_lt
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (I : Finset ι) (T : Finset V) (x : V)
    (z y : ι → V)
    (hz_inj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → z i ≠ z j)
    (hy_mem : ∀ i ∈ I, y i ∈ T)
    (hxy : ∀ i ∈ I, x ≠ y i)
    (hzx : ∀ i ∈ I, G.Adj (z i) x)
    (hzy : ∀ i ∈ I, G.Adj (z i) (y i))
    (hcard : T.card < I.card) : False := by
  have := card_le_of_commonNeighbor_selectors
    G hfree I T x z y hz_inj hy_mem hxy hzx hzy
  omega

end

end Erdos85
