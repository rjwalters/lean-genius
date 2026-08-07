import Proofs.Erdos85SquareMinimumDenseBlock
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A three-quarter squeeze for the minimum square layer

For a minimum defect component in the exact square family, split its quotient
row into equal-order and strictly larger components.  If `L` is the row mass
going to larger components and `M` is the number of minimum-order components,
then the minimum-layer excess identity and Cauchy--Schwarz give

`a * (d - L)^2 ≤ (N - a*L) * (p*a + s^2 - L)`.

A positive edge to a larger component has quotient multiplicity equal to the
integer ratio of the component orders, hence `L ≥ 2`.  In the exact family
`d=s^2+3`, `p=d+s`, `N=d-s`, this is impossible when `4a ≥ 3s` and `s ≥ 7`.
Thus a minimum coefficient in the top quarter of its possible range forces
the minimum-order layer to be closed under quotient support.
-/

namespace Erdos85

noncomputable section

/-- Arithmetic core of the three-quarter minimum-layer squeeze. -/
theorem false_of_square_minimum_layer_cauchy
    (s a L : ℚ) (hs : 7 ≤ s) (ha : 0 < a)
    (haLarge : 3 * s ≤ 4 * a) (hL : 2 ≤ L)
    (hineq :
      a * (s * s + 3 - L) ^ 2 ≤
        (s * s - s + 3 - a * L) *
          ((s * s + s + 3) * a + s * s - L)) : False := by
  have hs0 : 0 < s := by linarith
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have hPC : 0 < 9 * s ^ 4 - 3 * s ^ 3 + 43 * s ^ 2 - 88 * s + 48 := by
    have hprod : 0 ≤ (s - 7) *
        (9 * s ^ 3 + 60 * s ^ 2 + 463 * s + 3153) := by positivity
    nlinarith
  have hPF : 0 < s ^ 4 + 11 * s ^ 3 + 19 * s ^ 2 - 88 * s + 48 := by
    have hprod : 0 ≤ (s - 7) *
        (s ^ 3 + 18 * s ^ 2 + 145 * s + 927) := by positivity
    nlinarith
  let C : ℚ :=
    -a ^ 2 * (s ^ 2 + s + 3) + a * s ^ 2 + 6 * a - s ^ 2 + s - 3
  let F : ℚ :=
    -2 * a ^ 2 * (s ^ 2 + s + 3) + a * s ^ 2 + 12 * a +
      s ^ 4 - s ^ 3 + s ^ 2 + 2 * s - 6
  have hRC : 0 <
      4 * a * s ^ 2 + 4 * a * s + 12 * a +
        3 * s ^ 3 - s ^ 2 + 9 * s - 24 := by
    have hcore : 0 < 3 * s ^ 3 - s ^ 2 + 9 * s - 24 := by
      nlinarith [mul_nonneg hs2 (by linarith : 0 ≤ 3 * s - 1)]
    have has2 : 0 ≤ a * s ^ 2 := mul_nonneg ha.le hs2
    have has : 0 ≤ a * s := mul_nonneg ha.le hs0.le
    nlinarith
  have hRF : 0 <
      4 * a * s ^ 2 + 4 * a * s + 12 * a +
        3 * s ^ 3 + s ^ 2 + 9 * s - 24 := by
    nlinarith [hRC, hs2]
  have hprodC : (-4 * a + 3 * s) *
      (4 * a * s ^ 2 + 4 * a * s + 12 * a +
        3 * s ^ 3 - s ^ 2 + 9 * s - 24) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hRC.le
  have hprodF : (-4 * a + 3 * s) *
      (4 * a * s ^ 2 + 4 * a * s + 12 * a +
        3 * s ^ 3 + s ^ 2 + 9 * s - 24) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hRF.le
  have hC : C < 0 := by
    dsimp only [C]
    nlinarith
  have hF : F < 0 := by
    dsimp only [F]
    nlinarith
  have htail : (L - 2) * C ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hC.le
  dsimp only [C, F] at htail hF
  nlinarith

/-- Abstract minimum-layer form.  The weights are the normalized component
orders, and `Q` is the quotient row out of a minimum-weight state.  Exact
mass, row, and excess identities plus the integral ratio-two gap exclude a
larger neighbor once the minimum weight is at least `3s/4`. -/
theorem no_large_neighbor_of_square_minimum_layer
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℚ) (Q : I → I → ℚ) (i : I) (s a : ℚ)
    (hs : 7 ≤ s) (ha : 0 < a)
    (hmin : ∀ j, a ≤ w j)
    (hwNonneg : ∀ j, 0 ≤ w j) (hQNonneg : ∀ j, 0 ≤ Q i j)
    (hweight : ∑ j, w j = s * s - s + 3)
    (hrow : ∑ j, Q i j = s * s + 3)
    (hexcess :
      ∑ j ∈ Finset.univ.filter (fun j ↦ w j = a),
          Q i j * (Q i j - 1) = (s * s + s + 3) * a - 3)
    (hlargeMass : ∀ j, a < w j → 0 < Q i j → a * Q i j = w j)
    (hlargeTwo : ∀ j, a < w j → 0 < Q i j → 2 ≤ Q i j)
    (haLarge : 3 * s ≤ 4 * a) :
    ¬ ∃ j, a < w j ∧ 0 < Q i j := by
  intro hexists
  let E : Finset I := Finset.univ.filter (fun j ↦ w j = a)
  let Lset : Finset I := Finset.univ.filter (fun j ↦ w j ≠ a)
  let S : ℚ := ∑ j ∈ E, Q i j
  let L : ℚ := ∑ j ∈ Lset, Q i j
  let T : ℚ := ∑ j ∈ E, (Q i j) ^ 2
  let M : ℚ := E.card
  have hsplitQ : S + L = s * s + 3 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : I ↦ w j = a) (fun j ↦ Q i j)
    change S + L = _
    rw [hsplit]
    exact hrow
  have hT : T = (s * s + s + 3) * a - 3 + S := by
    have he := hexcess
    change ∑ j ∈ E, Q i j * (Q i j - 1) = _ at he
    change T = _
    rw [← he]
    dsimp only [T, S]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hTNonneg : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hCS : S ^ 2 ≤ M * T := by
    simpa only [S, M, T, Nat.cast_ofNat] using
      (sq_sum_le_card_mul_sum_sq (s := E) (f := fun j ↦ Q i j))
  have hmass : a * M + a * L ≤ s * s - s + 3 := by
    have heqMass : a * M + a * L =
        (∑ j ∈ E, w j) + ∑ j ∈ Lset, a * Q i j := by
      dsimp only [M, L]
      rw [Finset.mul_sum]
      have hE : a * (E.card : ℚ) = ∑ j ∈ E, w j := by
        calc
          a * (E.card : ℚ) = ∑ _j ∈ E, a := by simp [mul_comm]
          _ = ∑ j ∈ E, w j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact (Finset.mem_filter.mp hj).2.symm
      rw [hE]
    rw [heqMass]
    calc
      (∑ j ∈ E, w j) + ∑ j ∈ Lset, a * Q i j ≤
          (∑ j ∈ E, w j) + ∑ j ∈ Lset, w j := by
            gcongr with j hj
            by_cases hq : Q i j = 0
            · rw [hq, mul_zero]
              exact hwNonneg j
            · have hjne : w j ≠ a := (Finset.mem_filter.mp hj).2
              have hjlt : a < w j := lt_of_le_of_ne (hmin j) (Ne.symm hjne)
              exact (hlargeMass j hjlt (lt_of_le_of_ne (hQNonneg j)
                (Ne.symm hq))).le
      _ = ∑ j, w j := by
        rw [Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j : I ↦ w j = a) (fun j ↦ w j)]
      _ = s * s - s + 3 := hweight
  obtain ⟨j, hjLarge, hjQ⟩ := hexists
  have hjMem : j ∈ Lset := by
    simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_of_gt hjLarge
  have hqLeL : Q i j ≤ L := by
    dsimp only [L]
    exact Finset.single_le_sum (fun k _ ↦ hQNonneg k) hjMem
  have hL : 2 ≤ L := le_trans (hlargeTwo j hjLarge hjQ) hqLeL
  have haM : a * M ≤ s * s - s + 3 - a * L := by linarith
  have hmul : a * S ^ 2 ≤
      (s * s - s + 3 - a * L) * T := by
    calc
      a * S ^ 2 ≤ a * (M * T) :=
        mul_le_mul_of_nonneg_left hCS ha.le
      _ = (a * M) * T := by ring
      _ ≤ (s * s - s + 3 - a * L) * T :=
        mul_le_mul_of_nonneg_right haM hTNonneg
  have hineq :
      a * (s * s + 3 - L) ^ 2 ≤
        (s * s - s + 3 - a * L) *
          ((s * s + s + 3) * a + s * s - L) := by
    have hS : s * s + 3 - L = S := by linarith
    have hT' : (s * s + s + 3) * a + s * s - L = T := by
      rw [hT]
      linarith
    rw [hS, hT']
    exact hmul
  exact false_of_square_minimum_layer_cauchy s a L hs ha haLarge hL hineq

open SimpleGraph

/-- **Graph-facing three-quarter squeeze.**  In the exact square family, a
minimum component whose normalized order is at least `3s/4` has no quotient
edge to a strictly larger component. -/
theorem secondOrder_square_minimum_no_larger_neighbor_of_threeQuarter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hminDegree : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s) (hNEq : N = d - s)
    (hall : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ e.supp.ncard)
    (hs7 : 7 ≤ s)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (haLarge : 3 * s ≤ 4 * (c.supp.ncard / p)) :
    ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard < e.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0 := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let w : C → ℚ := fun e ↦ (e.supp.ncard / p : ℕ)
  let a : ℚ := (c.supp.ncard / p : ℕ)
  have hpPos : 0 < p := hp.pos
  have hcoeffSum : ∑ e : C, e.supp.ncard / p = N := by
    have hsumSizes : (∑ e : C, e.supp.ncard) = N * p := by
      rw [sum_connectedComponent_supp_ncard (secondOrderDefectGraph G), hcard]
      exact hboundary
    have hmul : p * (∑ e : C, e.supp.ncard / p) = p * N := by
      calc
        p * (∑ e : C, e.supp.ncard / p) =
            ∑ e : C, p * (e.supp.ncard / p) := by rw [Finset.mul_sum]
        _ = ∑ e : C, e.supp.ncard := by
          apply Finset.sum_congr rfl
          intro e he
          exact Nat.mul_div_cancel' (hall e)
        _ = N * p := hsumSizes
        _ = p * N := Nat.mul_comm N p
    exact Nat.eq_of_mul_eq_mul_left hpPos hmul
  have haPosNat : 0 < c.supp.ncard / p := by
    exact Nat.div_pos (Nat.le_of_dvd c.nonempty_supp.ncard_pos (hall c)) hpPos
  have haPos : 0 < a := by
    dsimp only [a]
    exact_mod_cast haPosNat
  have hwMin : ∀ e : C, a ≤ w e := by
    intro e
    have hcSize : c.supp.ncard = p * (c.supp.ncard / p) :=
      (Nat.mul_div_cancel' (hall c)).symm
    have heSize : e.supp.ncard = p * (e.supp.ncard / p) :=
      (Nat.mul_div_cancel' (hall e)).symm
    have hle := hcmin e
    rw [hcSize, heSize] at hle
    have hdiv : c.supp.ncard / p ≤ e.supp.ncard / p :=
      Nat.le_of_mul_le_mul_left hle hpPos
    dsimp only [a, w]
    exact_mod_cast hdiv
  have hwNonneg : ∀ e : C, 0 ≤ w e := by intro e; positivity
  have hQNonneg : ∀ e : C, 0 ≤ (Q c e : ℚ) := by intro e; positivity
  have hweight : ∑ e : C, w e = (s : ℚ) * s - s + 3 := by
    have hcast : (∑ e : C, w e) = (N : ℚ) := by
      dsimp only [w]
      exact_mod_cast hcoeffSum
    rw [hcast, hNEq]
    have hsd : s ≤ d := by rw [hdEq]; nlinarith
    rw [Nat.cast_sub hsd, hdEq]
    push_cast
    ring
  have hrow : ∑ e : C, (Q c e : ℚ) = (s : ℚ) * s + 3 := by
    have hrowNat := sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hminDegree hcard c
    have hrowRat : (∑ e : C, (Q c e : ℚ)) = (d : ℚ) := by
      exact_mod_cast hrowNat
    rw [hrowRat, hdEq]
    push_cast
    ring
  have hexcessZ := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hminDegree hcard c hcmin
  have hcSize : c.supp.ncard = p * (c.supp.ncard / p) :=
    (Nat.mul_div_cancel' (hall c)).symm
  have hexcess :
      ∑ e ∈ Finset.univ.filter (fun e : C ↦ w e = a),
          (Q c e : ℚ) * ((Q c e : ℚ) - 1) =
        ((s : ℚ) * s + s + 3) * a - 3 := by
    have hfilter : Finset.univ.filter (fun e : C ↦ w e = a) =
        Finset.univ.filter (fun e : C ↦ e.supp.ncard = c.supp.ncard) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, w, a]
      have heSize : e.supp.ncard = p * (e.supp.ncard / p) :=
        (Nat.mul_div_cancel' (hall e)).symm
      constructor
      · intro h
        have hnat : e.supp.ncard / p = c.supp.ncard / p := by
          exact_mod_cast h
        rw [heSize, hcSize, hnat]
      · intro h
        have hdiv := congrArg (fun n : ℕ ↦ n / p) h
        simpa using hdiv
    rw [hfilter]
    have hz := congrArg (fun z : ℤ ↦ (z : ℚ)) hexcessZ
    simp only [Int.cast_sum, Int.cast_sub, Int.cast_natCast,
      Int.cast_ofNat] at hz
    have hcRat : (c.supp.ncard : ℚ) = (p : ℚ) * a := by
      dsimp only [a]
      exact_mod_cast hcSize
    rw [hcRat] at hz
    have hpRat : (p : ℚ) = (s : ℚ) * s + s + 3 := by
      rw [hpEq, hdEq]
      push_cast
      ring
    rw [hpRat] at hz
    rw [Finset.sum_filter]
    simpa [Q, a] using hz
  have hlargeMass : ∀ e : C, a < w e → 0 < (Q c e : ℚ) →
      a * (Q c e : ℚ) = w e := by
    intro e hae hq
    have hsize : c.supp.ncard < e.supp.ncard := by
      have heSize : e.supp.ncard = p * (e.supp.ncard / p) :=
        (Nat.mul_div_cancel' (hall e)).symm
      dsimp only [a, w] at hae
      rw [hcSize, heSize]
      exact Nat.mul_lt_mul_of_pos_left (by exact_mod_cast hae) hpPos
    have hqNat : 0 < Q c e := by exact_mod_cast hq
    have hentries := secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree hd heven hminDegree hcard c e hsize hqNat
    have heSize : e.supp.ncard = p * (e.supp.ncard / p) :=
      (Nat.mul_div_cancel' (hall e)).symm
    have hnat : (c.supp.ncard / p) * Q c e = e.supp.ncard / p := by
      rw [hcSize, heSize] at hentries
      apply Nat.eq_of_mul_eq_mul_left hpPos
      simpa [mul_assoc] using hentries.2.2
    dsimp only [a, w, Q]
    exact_mod_cast hnat
  have hlargeTwo : ∀ e : C, a < w e → 0 < (Q c e : ℚ) →
      2 ≤ (Q c e : ℚ) := by
    intro e hae hq
    have hmass := hlargeMass e hae hq
    by_contra hnot
    have hqle : (Q c e : ℚ) < 2 := lt_of_not_ge hnot
    have hqone : (Q c e : ℕ) = 1 := by
      have hqNat : 0 < Q c e := by exact_mod_cast hq
      have hqLt : Q c e < 2 := by exact_mod_cast hqle
      omega
    rw [hqone] at hmass
    simp only [Nat.cast_one, mul_one] at hmass
    exact (ne_of_lt hae) hmass
  have hclosed := no_large_neighbor_of_square_minimum_layer
    w (fun x y ↦ (Q x y : ℚ)) c (s : ℚ) a
    (by exact_mod_cast hs7) haPos hwMin hwNonneg hQNonneg hweight hrow
    hexcess hlargeMass hlargeTwo (by
      dsimp only [a]
      exact_mod_cast haLarge)
  intro e hce
  by_contra hqne
  have hqpos : 0 < (Q c e : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero hqne
  have hae : a < w e := by
    have heSize : e.supp.ncard = p * (e.supp.ncard / p) :=
      (Nat.mul_div_cancel' (hall e)).symm
    dsimp only [a, w]
    rw [hcSize, heSize] at hce
    exact_mod_cast (Nat.lt_of_mul_lt_mul_left hce)
  exact hclosed ⟨e, hae, hqpos⟩

end

end Erdos85
