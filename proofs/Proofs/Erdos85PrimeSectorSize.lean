import Proofs.Erdos85MixedDiagonalDichotomy
import Proofs.Erdos85ZeroDiagonalSectorExpansion

/-!
# Size bounds for prime-divisible defect sectors

The components whose orders are divisible by `p` consume at least `p`
vertices apiece.  On an odd labeled sector, every diagonal quotient entry is
at most two.  Consequently, positive sector mass in the quantized branch
forces `p ^ 2 ≤ |V|`.  At the exact second-order boundary this rules out the
positive-mass branch whenever `d ≤ p`.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A `p`-divisible component sector occupies at least `p` vertices for each
of its components.  This is purely the connected-component partition. -/
theorem prime_mul_pDivisible_component_card_le_card
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    {p : ℕ} (hp : 0 < p) :
    p * (Finset.univ.filter (fun c : D.ConnectedComponent ↦
      p ∣ c.supp.ncard)).card ≤ Fintype.card V := by
  classical
  let S := Finset.univ.filter (fun c : D.ConnectedComponent ↦
    p ∣ c.supp.ncard)
  have hparts : (∑ c : D.ConnectedComponent, c.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ c : D.ConnectedComponent, c.supp.ncard) =
          ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
  calc
    p * (Finset.univ.filter (fun c : D.ConnectedComponent ↦
        p ∣ c.supp.ncard)).card = ∑ c ∈ S, p := by
      simp [S, Nat.mul_comm]
    _ ≤ ∑ c ∈ S, c.supp.ncard := by
      apply Finset.sum_le_sum
      intro c hc
      exact Nat.le_of_dvd c.nonempty_supp.ncard_pos
        (Finset.mem_filter.mp hc).2
    _ ≤ ∑ c : D.ConnectedComponent, c.supp.ncard := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [S]) (by simp)
    _ = Fintype.card V := hparts

/-- On an odd labeled `p`-sector, its anchor mass is bounded above by twice
the number of selected components. -/
theorem pDivisibleAnchorMass_le_two_mul_component_card
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
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard) :
    pDivisibleAnchorMass G u p ≤
      2 * (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard)).card := by
  classical
  rw [pDivisibleAnchorMass_eq_sum_diagonalQuotient
    G hfree hd heven hmin hcard u hu huRange]
  calc
    (∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) c c) ≤
        ∑ _c ∈ Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard), 2 := by
      apply Finset.sum_le_sum
      intro c hc
      have hpc : p ∣ c.supp.ncard := (Finset.mem_filter.mp hc).2
      rcases oddComponent_diagonalQuotient_eq_zero_or_two
        G hfree hd heven hmin hcard (hℓ3 c) (hodd c hpc)
        c (u c) (hu c) (huRange c) (huD c) with h0 | h2
      · omega
      · omega
    _ = 2 * (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard)).card := by simp [Nat.mul_comm]

/-- The positive quantized mass branch forces the square-size obstruction
`p² ≤ |V|`. -/
theorem prime_sq_le_card_of_two_mul_le_pDivisibleAnchorMass
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
    (hp : 0 < p)
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
    (hmass : 2 * p ≤ pDivisibleAnchorMass G u p) :
    p * p ≤ Fintype.card V := by
  let S := Finset.univ.filter (fun c :
    (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ c.supp.ncard)
  have hmassUpper := pDivisibleAnchorMass_le_two_mul_component_card
    G hfree hd heven hmin hcard u hu huRange huD hℓ3 hodd
  have hpS : p ≤ S.card := by
    dsimp [S]
    omega
  have hsize := prime_mul_pDivisible_component_card_le_card
    (secondOrderDefectGraph G) hp
  calc
    p * p ≤ p * S.card := Nat.mul_le_mul_left p hpS
    _ ≤ Fintype.card V := by simpa [S] using hsize

/-- At the exact boundary, a prime at least the degree cannot lie in the
positive mass branch. -/
theorem pDivisibleAnchorMass_lt_two_mul_of_degree_le_prime
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
    (hdp : d ≤ p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard) :
    pDivisibleAnchorMass G u p < 2 * p := by
  by_contra hnot
  have hmass : 2 * p ≤ pDivisibleAnchorMass G u p := by omega
  have hp : 0 < p := by omega
  have hsquare := prime_sq_le_card_of_two_mul_le_pDivisibleAnchorMass
    G hfree hd heven hmin hcard hp u hu huRange huD hℓ3 hodd hmass
  rw [hcard] at hsquare
  have hdd : d * d ≤ p * p := Nat.mul_le_mul hdp hdp
  have hboundary : d * (d - 1) + 3 < d * d := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  omega

/-- Combining the sector-mass gap with the boundary size squeeze: if `p`
divides the mass and `d ≤ p`, then the selected-sector mass vanishes. -/
theorem pDivisibleAnchorMass_eq_zero_of_dvd_of_degree_le_prime
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
    (hpOdd : Odd p) (hdp : d ≤ p)
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
    pDivisibleAnchorMass G u p = 0 := by
  rcases pDivisibleAnchorMass_eq_zero_or_ge_two_mul
    G hfree hd heven hmin hcard hpOdd u hu huRange huD hℓ3 hodd
      hdvdMass with hzero | hlarge
  · exact hzero
  · have hsmall := pDivisibleAnchorMass_lt_two_mul_of_degree_le_prime
      G hfree hd heven hmin hcard hdp u hu huRange huD hℓ3 hodd
    omega

/-- A zero-mass even sector containing a globally minimum component of order
at least four occupies at least `4p` vertices. -/
theorem four_mul_prime_le_card_of_zero_even_minimum_sector
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
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hc4 : 4 ≤ c.supp.ncard) (hpc : p ∣ c.supp.ncard)
    (hsectorEven : Even ((Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card))
    (hmassZero : pDivisibleAnchorMass G u p = 0) :
    4 * p ≤ Fintype.card V := by
  classical
  let S := Finset.univ.filter (fun x :
    (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ x.supp.ncard)
  have hbridge := pDivisibleAnchorMass_eq_sum_diagonalQuotient
    G hfree hd heven hmin hcard u hu huRange (p := p)
  have hsumZero : (∑ x ∈ S, componentQuotientMatrix G
      (secondOrderDefectGraph G) x x) = 0 := by
    rw [← hbridge]
    exact hmassZero
  have hdiag : ∀ x : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ x.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) x x = 0 := by
    intro x hpx
    exact (Finset.sum_eq_zero_iff_of_nonneg (by simp)).mp hsumZero x
      (by simp [S, hpx])
  have hfour :=
    four_le_pDivisible_filter_card_of_even_zeroDiagonal_minimum_order_four
      G hfree hd heven hmin hcard c hcmin hc4 hpc hdiag hsectorEven
  have hsize := prime_mul_pDivisible_component_card_le_card
    (secondOrderDefectGraph G) (by
      exact Nat.pos_of_dvd_of_pos hpc c.nonempty_supp.ncard_pos)
  have hmul : 4 * p ≤ p * S.card := by
    rw [mul_comm 4 p]
    exact Nat.mul_le_mul_left p hfour
  exact hmul.trans (by simpa [S] using hsize)

/-- **Large nonresidue-sector terminal, in arithmetic interface form.**
If `p ≥ d`, divisibility quantizes the mass to zero; even zero-sector
geometry then forces `4p ≤ |V|`.  Therefore a prime larger than one quarter
of the boundary order cannot divide the global minimum component order. -/
theorem false_of_large_even_minimum_sector_mass_divisibility
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
    (hpOdd : Odd p) (hdp : d ≤ p)
    (hlarge : Fintype.card V < 4 * p)
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
    (hdvdMass : p ∣ pDivisibleAnchorMass G u p)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hc4 : 4 ≤ c.supp.ncard) (hpc : p ∣ c.supp.ncard)
    (hsectorEven : Even ((Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card)) : False := by
  have hzero := pDivisibleAnchorMass_eq_zero_of_dvd_of_degree_le_prime
    G hfree hd heven hmin hcard hpOdd hdp u hu huRange huD hℓ3 hodd
      hdvdMass
  have hfour := four_mul_prime_le_card_of_zero_even_minimum_sector
    G hfree hd heven hmin hcard u hu huRange c hcmin hc4 hpc
      hsectorEven hzero
  omega

end

end Erdos85
