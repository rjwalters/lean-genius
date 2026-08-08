import Proofs.Erdos85SquareMinimumLeakage
import Proofs.Erdos85EqualCycleResidual
import Proofs.Erdos85DifferencePacking
import Proofs.Erdos85FrequencyPairMixedTransport
import Proofs.Erdos85BoundaryQuotientExcess

/-!
# Unconditional closure of the unit minimum layer

The leakage dichotomy leaves two configurations for a coefficient-one
minimum layer in the exact-square boundary: at most one unit component, or
all components of order exactly `p`.

Both die without any parity input.  A lone unit component collapses the
equal-size excess identity to its bare diagonal, demanding
`Q(c,c)·(Q(c,c)−1) = p − 3 ≥ 4`, while the odd-cycle diagonal bound caps
the left side at two.  The all-equal branch is the equal-cycle boundary,
which forces `d ∈ {4, 12}` — impossible for `d = s² + 3` with `s ≥ 7`.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **A lone unit minimum component is impossible.**  If the minimum defect
component has order `p ≥ 7` odd and no other component shares its order,
the equal-size excess identity forces the diagonal quotient entry to carry
`p − 3 ≥ 4`, contradicting the odd-cycle diagonal bound of two. -/
theorem false_of_secondOrder_lone_unit_minimum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp7 : 7 ≤ p) (hpOdd : Odd p)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc₀size : c₀.supp.ncard = p)
    (hlone : (Finset.univ.filter
      (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        c.supp.ncard = c₀.supp.ncard)).card ≤ 1) : False := by
  classical
  set Q := componentQuotientMatrix G (secondOrderDefectGraph G) with hQ
  have hexcess := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hmin hcard c₀ hc₀min
  have hself : c₀ ∈ Finset.univ.filter
      (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        c.supp.ncard = c₀.supp.ncard) := by
    simp
  have hunique : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c₀ → e.supp.ncard ≠ c₀.supp.ncard := by
    intro e hne heq
    have he : e ∈ Finset.univ.filter
        (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
          c.supp.ncard = c₀.supp.ncard) := by
      simp [heq]
    have h2 : 1 < (Finset.univ.filter
        (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
          c.supp.ncard = c₀.supp.ncard)).card :=
      Finset.one_lt_card.mpr ⟨c₀, hself, e, he, Ne.symm hne⟩
    omega
  have hsum : (∑ e, if e.supp.ncard = c₀.supp.ncard then
      (Q c₀ e : ℤ) * ((Q c₀ e : ℤ) - 1) else 0) =
        (Q c₀ c₀ : ℤ) * ((Q c₀ c₀ : ℤ) - 1) := by
    rw [Finset.sum_eq_single c₀
      (fun b _ hb => by rw [if_neg (hunique b hb)])
      (fun h => absurd (Finset.mem_univ c₀) h)]
    rw [if_pos rfl]
  obtain ⟨u, hu, huRange, huD, hthree⟩ :=
    exists_mixed_cycle_labeling G hfree hd heven hmin hcard
  letI : NeZero c₀.supp.ncard := ⟨by have := hthree c₀; omega⟩
  have hOdd : Odd c₀.supp.ncard := by
    rw [hc₀size]
    exact hpOdd
  have hdiag := secondOrder_equalOddCycleComponent_diagonal_le_two
    G hfree hd heven hmin hcard (hthree c₀) hOdd c₀ (u c₀) (hu c₀)
      (huRange c₀) (huD c₀)
  have hQle : (Q c₀ c₀ : ℤ) ≤ 2 := by
    rw [hQ]
    exact_mod_cast hdiag
  have hQnonneg : (0 : ℤ) ≤ (Q c₀ c₀ : ℤ) := by positivity
  rw [hsum] at hexcess
  have hbound : (c₀.supp.ncard : ℤ) - 3 ≤ 2 := by
    nlinarith [hexcess, hQle, hQnonneg]
  rw [hc₀size] at hbound
  have hp7' : (7 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp7
  linarith

/-- **The square unit minimum layer is impossible, unconditionally.**  The
leakage dichotomy leaves a lone unit (dead by the diagonal collapse of the
equal-size excess) or an all-equal boundary (dead because equal cycles
force `d ∈ {4, 12}`, incompatible with `d = s² + 3`, `s ≥ 7`).  No parity
or convolution input is used. -/
theorem false_of_secondOrder_square_unit_minimum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s)
    (hNEq : N = d - s) (hs7 : 7 ≤ s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc₀unit : c₀.supp.ncard / p = 1) : False := by
  classical
  have hc₀size : c₀.supp.ncard = p := by
    calc
      c₀.supp.ncard = p * (c₀.supp.ncard / p) :=
        (Nat.mul_div_cancel' (hall c₀)).symm
      _ = p := by rw [hc₀unit, mul_one]
  have hp7 : 7 ≤ p := by
    rw [hpEq, hdEq]
    nlinarith [hs7]
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  rcases secondOrder_square_unitLayer_card_le_one_or_all_equal
      G hfree hd heven hmin hcard hp hboundary hdEq hpEq hNEq hs7 hall
        c₀ hc₀min hc₀unit with hlone | hallEq
  · exact false_of_secondOrder_lone_unit_minimum G hfree hd heven hmin
      hcard hp7 hpOdd c₀ hc₀min hc₀size hlone
  · rcases equalCycle_degree_eq_four_or_twelve G hfree hd heven hmin
        hcard hallEq with h4 | h12
    · rw [hdEq] at h4
      nlinarith [hs7]
    · rw [hdEq] at h12
      nlinarith [hs7]

end

end Erdos85
