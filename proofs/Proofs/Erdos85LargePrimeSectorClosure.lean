import Proofs.Erdos85BoundaryQuotientIrreducibleClean

/-!
# Closure of component-order sectors at primes above the degree

Detailed balance and the constant quotient row sum imply a sharp fact: if
`p > d`, a positive quotient edge cannot cross between a component whose
order is divisible by `p` and one whose order is not.  Irreducibility then
makes every nonempty `p`-sector global.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- At a prime larger than the quotient row sum, a `p`-divisible component
has no quotient edge to a non-`p`-divisible component. -/
theorem componentQuotient_eq_zero_of_largePrime_dvd_not_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hdp : d < p)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc : p ∣ c.supp.ncard) (hpe : ¬ p ∣ e.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 0 := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hrow := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard e
  have hle : Q e c ≤ d := by
    rw [← hrow]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c)
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  have hpRight : p ∣ e.supp.ncard * Q e c := by
    rw [← hbal]
    exact dvd_mul_of_dvd_left hpc _
  have hpQec : p ∣ Q e c :=
    (hp.dvd_mul.mp hpRight).resolve_left hpe
  have hQec : Q e c = 0 := by
    rcases hpQec with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · simp [hk, hk0]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have : p ≤ Q e c := by rw [hk]; exact Nat.le_mul_of_pos_right p hkpos
      omega
  have hcpos : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
  have hQce : Q c e = 0 := by
    change componentQuotientMatrix G (secondOrderDefectGraph G) e c = 0 at hQec
    rw [hQec, mul_zero] at hbal
    change componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0
    exact (Nat.mul_eq_zero.mp hbal).resolve_left (Nat.ne_of_gt hcpos)
  exact ⟨hQce, hQec⟩

/-- A nonempty component-order sector for a prime above the degree contains
every defect component. -/
theorem all_component_orders_dvd_of_largePrime_dvd_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hdp : d < p)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc : p ∣ c.supp.ncard) :
    ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ e.supp.ncard := by
  letI : Nonempty V :=
    ⟨componentRepresentative (secondOrderDefectGraph G) c⟩
  intro e
  have hwalk := secondOrder_componentQuotientMatrix_irreducible_clean
    G hfree hd heven hmin hcard c e
  induction hwalk with
  | refl => exact hpc
  | @tail a b hab hpos ih =>
      by_contra hpb
      have hz := componentQuotient_eq_zero_of_largePrime_dvd_not_dvd
        G hfree hd heven hmin hcard hp hdp a b ih hpb
      omega

/-- Consequently, a prime above the degree which divides one defect-cycle
order must divide the total number of vertices. -/
theorem largePrime_dvd_card_of_dvd_component_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hdp : d < p)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc : p ∣ c.supp.ncard) : p ∣ Fintype.card V := by
  let D := secondOrderDefectGraph G
  have hall := all_component_orders_dvd_of_largePrime_dvd_one
    G hfree hd heven hmin hcard hp hdp c hpc
  have hpSum : p ∣ ∑ e : D.ConnectedComponent, e.supp.ncard := by
    apply Finset.dvd_sum
    intro e he
    exact hall e
  have hparts : (∑ e : D.ConnectedComponent, e.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ e : D.ConnectedComponent, e.supp.ncard) =
          ∑ e : D.ConnectedComponent, Fintype.card e.supp := by
        apply Finset.sum_congr rfl
        intro e he
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq e.supp).symm
      _ = Fintype.card (Σ e : D.ConnectedComponent, e.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
  rwa [hparts] at hpSum

/-- **Large-prime residue theorem.**  If a prime above the degree divides a
defect-cycle order at the exact boundary, then `d-3` is a square modulo that
prime.  Indeed sector closure gives `p ∣ d²-d+3`, hence `d-3 ≡ d²`. -/
theorem isSquare_d_sub_three_mod_largePrime_of_dvd_component_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hdp : d < p)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc : p ∣ c.supp.ncard) :
    IsSquare ((d - 3 : ℕ) : ZMod p) := by
  have hpCard := largePrime_dvd_card_of_dvd_component_order
    G hfree hd heven hmin hcard hp hdp c hpc
  have hpN : p ∣ d * (d - 1) + 3 := by simpa [hcard] using hpCard
  have hzero : ((d * (d - 1) + 3 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpN
  have hcastSub : ((d - 3 : ℕ) : ZMod p) = (d : ZMod p) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ d)]
    norm_num
  refine ⟨(d : ZMod p), ?_⟩
  rw [hcastSub]
  push_cast at hzero
  have hdsub : (d : ZMod p) * ((d : ZMod p) - 1) + 3 = 0 := by
    simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hzero
  linear_combination -hdsub

/-- Equivalently, a nonresidue prime above the degree divides no defect-cycle
order. -/
theorem not_dvd_component_order_of_largePrime_nonresidue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hdp : d < p)
    (hnr : ¬ IsSquare ((d - 3 : ℕ) : ZMod p))
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ¬ p ∣ c.supp.ncard := by
  intro hpc
  exact hnr (isSquare_d_sub_three_mod_largePrime_of_dvd_component_order
    G hfree hd heven hmin hcard hp hdp c hpc)

end

end Erdos85
