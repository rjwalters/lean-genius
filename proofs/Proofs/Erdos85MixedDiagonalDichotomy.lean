import Proofs.Erdos85MixedSectorMassQuotient
import Proofs.Erdos85DifferencePacking

/-!
# Diagonal quotient dichotomy on odd components and the sector-mass gap

Every odd defect component has an even diagonal quotient entry (handshake
against an odd order) that is at most two (odd-cycle self-block packing).
Hence `Q(c,c) ∈ {0, 2}` on odd components — per component, with no
equal-length or minimality hypotheses.

Consequences for the `p`-divisible sector under `hodd`:

* the sector anchor mass is `2m` where `m` counts the sector components
  with a present diagonal;
* combined with the nonsquare uniformity theorem
  (`prime_dvd_pDivisibleAnchorMass_of_nonsquare`), `p ∣ m`, so the mass
  is either `0` or at least `2p` — the **sector-mass gap**;
* for an all-odd family the complementary diagonal trace is even, so the
  full-trace identity `mass + complement = d` refines to an explicit
  even decomposition.

This answers the quotient-restriction question of the discharge program:
outside the sector the diagonal entries of odd components are likewise
confined to `{0, 2}`.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Odd components have even diagonal quotient entries: handshake gives
`ℓc · Q(c,c)` even, and `ℓc` is odd. -/
theorem oddComponent_diagonalQuotient_even
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hodd : Odd c.supp.ncard) :
    Even (componentQuotientMatrix G (secondOrderDefectGraph G) c c) := by
  have hprod := secondOrder_componentQuotientMatrix_diagonal_mul_even
    G hfree hd heven hmin hcard c
  exact (Nat.even_mul.mp hprod).resolve_left
    (Nat.not_even_iff_odd.mpr hodd)

/-- **Diagonal dichotomy.**  On an odd component carrying a cycle
labeling, the diagonal quotient entry is zero or two. -/
theorem oddComponent_diagonalQuotient_eq_zero_or_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (hu : Function.Injective u)
    (huRange : Set.range u = c.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 ∨
      componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 := by
  have hlen : c.supp.ncard = r := by
    rw [← huRange, Set.ncard_range_of_injective hu,
      Nat.card_eq_fintype_card, ZMod.card]
  have heq := oddComponent_diagonalQuotient_even G hfree hd heven hmin
    hcard c (hlen ▸ hrOdd)
  have hle := secondOrder_equalOddCycleComponent_diagonal_le_two
    G hfree hd heven hmin hcard hr3 hrOdd c u hu huRange huD
  rcases heq with ⟨k, hk⟩
  interval_cases h : componentQuotientMatrix G
    (secondOrderDefectGraph G) c c
  · exact Or.inl rfl
  · omega
  · exact Or.inr rfl

/-- **The sector-mass gap.**  Under `hodd`, the `p`-divisible sector
anchor mass is even; if moreover the nonsquare uniformity gives
`p ∣ mass`, the mass is zero or at least `2p`. -/
theorem pDivisibleAnchorMass_eq_zero_or_ge_two_mul
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hpOdd : Odd p)
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
    (hdvdMass : p ∣ pDivisibleAnchorMass G u p) :
    pDivisibleAnchorMass G u p = 0 ∨
      2 * p ≤ pDivisibleAnchorMass G u p := by
  classical
  set S := Finset.univ.filter (fun c :
    (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ c.supp.ncard)
    with hS
  have hbridge := pDivisibleAnchorMass_eq_sum_diagonalQuotient
    G hfree hd heven hmin hcard u hu huRange (p := p)
  set m := (S.filter fun c ↦ componentQuotientMatrix G
    (secondOrderDefectGraph G) c c = 2).card with hm
  have hmass2 : pDivisibleAnchorMass G u p = 2 * m := by
    rw [hbridge, hm]
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hc2 : p ∣ c.supp.ncard := (Finset.mem_filter.mp hc).2
    rcases oddComponent_diagonalQuotient_eq_zero_or_two G hfree hd heven
      hmin hcard (hℓ3 c) (hodd c hc2) c (u c) (hu c) (huRange c)
      (huD c) with h0 | h2
    · rw [h0]
      simp
    · rw [h2]
      simp
  have hpm : p ∣ m := by
    rcases hdvdMass with ⟨t, ht⟩
    rw [hmass2] at ht
    have hcop : Nat.Coprime p 2 :=
      Nat.coprime_two_right.mpr hpOdd
    exact hcop.dvd_of_dvd_mul_left ⟨t, by omega⟩
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · left
    rw [hmass2, h0, mul_zero]
  · right
    have hpm' : p ≤ m := Nat.le_of_dvd hpos hpm
    rw [hmass2]
    omega

end

end Erdos85
