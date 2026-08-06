import Proofs.Erdos85MixedAdmissibleFiberParity
import Proofs.Erdos85FrequencyPairMixedTransport

/-!
# Assembly interface for mixed projected-anchor parity

This file separates the final parity arithmetic from the geometric proof
that off-diagonal complement classes occur evenly.  The latter is supplied
by the equal-block and quotient-cut cancellation layers.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Pointwise partitions `L+R=A`, together with even total `R`, transfer the
parity of the total `A` to the total `L`. -/
theorem odd_sum_left_iff_of_partition_of_even_right
    {C : Type*} [DecidableEq C] (S : Finset C)
    (L R A : C → ℕ) (hpart : ∀ c ∈ S, L c + R c = A c)
    (hR : Even (∑ c ∈ S, R c)) :
    Odd (∑ c ∈ S, L c) ↔ Odd (∑ c ∈ S, A c) := by
  have hsum : (∑ c ∈ S, L c) + (∑ c ∈ S, R c) =
      ∑ c ∈ S, A c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    exact hpart c hc
  obtain ⟨r, hr⟩ := hR
  constructor <;> intro hodd
  · obtain ⟨k, hk⟩ := hodd
    refine ⟨k + r, ?_⟩
    omega
  · obtain ⟨k, hk⟩ := hodd
    refine ⟨k - r, ?_⟩
    have hrk : r ≤ k := by omega
    omega

/-- Convert the valuation form of reduction modulo `p` to `castHom`. -/
theorem zmod_castHom_eq_val_cast
    {m p : ℕ} [NeZero m] [NeZero p] (hpm : p ∣ m) (x : ZMod m) :
    ZMod.castHom hpm (ZMod p) x = ((x.val : ℕ) : ZMod p) := by
  calc
    ZMod.castHom hpm (ZMod p) x =
        ZMod.castHom hpm (ZMod p) ((x.val : ℕ) : ZMod m) :=
      congrArg _ (ZMod.natCast_zmod_val x).symm
    _ = ((x.val : ℕ) : ZMod p) := map_natCast _ _

/-- **Conditional mixed projected-anchor parity.** Once the aggregate
off-diagonal complement fiber is even, the nonexceptional projected diagonal
anchor count is odd exactly when the number of `p`-divisible components is
odd. -/
theorem odd_mixedProjectedAnchor_iff_odd_componentCount_of_complement_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (s : ZMod p) (hs0 : 2 * s ≠ 0) (hs1 : 2 * s ≠ 1)
    (hsm1 : 2 * s ≠ -1)
    (hcompEven : Even (∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ c.supp.ncard),
      ((admissibleDifferences c.supp.ncard).filter (fun w ↦
        ((w.val : ℕ) : ZMod p) = 2 * s ∧
          w ∉ orderedDifferenceSet
            (mixedAnchorSupport G (u c 0) (u c)))).card)) :
    Odd (mixedProjectedAnchor G u p s) ↔
      Odd (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard)).card := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let ℓ : C → ℕ := fun c ↦ c.supp.ncard
  let S : Finset C := Finset.univ.filter (fun c ↦ p ∣ ℓ c)
  let L : C → ℕ := fun c ↦
    ((mixedAnchorSupport G (u c 0) (u c)).filter (fun h ↦
      ((h.val : ℕ) : ZMod p) = s)).card
  let R : C → ℕ := fun c ↦
    ((admissibleDifferences (ℓ c)).filter (fun w ↦
      ((w.val : ℕ) : ZMod p) = 2 * s ∧
        w ∉ orderedDifferenceSet
          (mixedAnchorSupport G (u c 0) (u c)))).card
  let A : C → ℕ := fun c ↦
    ((admissibleDifferences (ℓ c)).filter (fun w ↦
      ((w.val : ℕ) : ZMod p) = 2 * s)).card
  have hpart : ∀ c ∈ S, L c + R c = A c := by
    intro c hc
    have hpc : p ∣ ℓ c := by simpa [S] using hc
    have hf := diag_fiber_add_complement_eq_admissible_fiber G hfree hd
      heven hmin hcard (hℓ3 c) (hodd c hpc) hpc
        (hp.odd_of_ne_two (by omega)) c (hu c) (huRange c) (huD c) s
    simpa only [L, R, A, ℓ, zmod_castHom_eq_val_cast hpc] using hf
  have htransfer := odd_sum_left_iff_of_partition_of_even_right
    S L R A hpart (by simpa [S, R, ℓ] using hcompEven)
  have hA := odd_sum_admissibleFibers_iff_odd_componentCount ℓ hp hp7
    hℓ3 hodd (2 * s) hs0 hs1 hsm1
  have hL : mixedProjectedAnchor G u p s = ∑ c ∈ S, L c := by
    unfold mixedProjectedAnchor
    apply Finset.sum_congr
    · rfl
    · intro c hc
      apply congrArg Finset.card
      rw [mixedAnchorSupport_eq_graphCycleBlockZeroSupport]
  rw [hL, htransfer]
  simpa [S, A, ℓ] using hA

end

end Erdos85
