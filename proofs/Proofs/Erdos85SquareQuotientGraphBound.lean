import Proofs.Erdos85SquareQuotientCoefficientBound
import Proofs.Erdos85LargePrimeSectorClosure
import Proofs.Erdos85ResidueSignedCount
import Proofs.Erdos85DifferencePacking

/-!
# Graph-facing coefficient bound in the exact square family

This file transports the weighted kernel inequality to the component
quotient of an extremal graph.  If every defect-cycle order is `p` times a
positive coefficient and the coefficients sum to `N`, then in the exact
square factorization the coefficient at `c` is controlled by the diagonal
quotient entry at `c`.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Graph-facing exact-square coefficient bound.** -/
theorem secondOrder_square_coefficient_mul_prime_le
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
    (hdEq : d = s * s + 3) (hpEq : p = d + s) (hNEq : N = d - s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    p * (c.supp.ncard / p) ≤
      N * (s + componentQuotientMatrix G (secondOrderDefectGraph G) c c) := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let a : C → ℚ := fun i ↦ (i.supp.ncard / p : ℕ)
  let B : C → C → ℚ := fun i j ↦
    (Q i j : ℚ) + if i = j then s else 0
  have hpPos : 0 < p := hp.pos
  have hsPos : 0 < s := by
    by_contra hs0
    have : s = 0 := Nat.eq_zero_of_not_pos hs0
    rw [this, zero_mul, zero_add] at hdEq
    omega
  have hNPos : 0 < N := by
    have hsd : s < d := by rw [hdEq]; nlinarith
    omega
  have haPos : ∀ i : C, 0 < a i := by
    intro i
    have hiPos : 0 < i.supp.ncard := i.nonempty_supp.ncard_pos
    have hpLe : p ≤ i.supp.ncard := Nat.le_of_dvd hiPos (hall i)
    change (0 : ℚ) < (i.supp.ncard / p : ℕ)
    exact_mod_cast Nat.div_pos hpLe hpPos
  have hcoeffSum : ∑ i : C, i.supp.ncard / p = N := by
    have hsumSizes : (∑ i : C, i.supp.ncard) = N * p := by
      rw [sum_connectedComponent_supp_ncard (secondOrderDefectGraph G), hcard]
      exact hboundary
    have hmul : p * (∑ i : C, i.supp.ncard / p) = p * N := by
      calc
        p * (∑ i : C, i.supp.ncard / p) =
            ∑ i : C, p * (i.supp.ncard / p) := by rw [Finset.mul_sum]
        _ = ∑ i : C, i.supp.ncard := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Nat.mul_div_cancel' (hall i)
        _ = N * p := hsumSizes
        _ = p * N := Nat.mul_comm N p
    exact Nat.eq_of_mul_eq_mul_left hpPos hmul
  have haSum : ∑ i : C, a i = (N : ℚ) := by
    unfold a
    exact_mod_cast hcoeffSum
  have hrowB : ∀ i : C, ∑ j, B i j = (p : ℚ) := by
    intro i
    have hrowQ := sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hmin hcard i
    unfold B
    simp only [Nat.cast_ite, Nat.cast_zero]
    rw [Finset.sum_add_distrib]
    have hrowQ' : (∑ j, (Q i j : ℚ)) = d := by exact_mod_cast hrowQ
    rw [hrowQ']
    simp [hpEq]
  have hbalanceB : ∀ i j : C, a i * B i j = a j * B j i := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hbal := secondOrder_componentQuotientMatrix_balance
        G hfree hd heven hmin hcard i j
      have hiSize : i.supp.ncard = p * (i.supp.ncard / p) := by
        exact (Nat.mul_div_cancel' (hall i)).symm
      have hjSize : j.supp.ncard = p * (j.supp.ncard / p) := by
        exact (Nat.mul_div_cancel' (hall j)).symm
      change i.supp.ncard * Q i j = j.supp.ncard * Q j i at hbal
      have hbalNat :
          (i.supp.ncard / p) * Q i j =
            (j.supp.ncard / p) * Q j i := by
        rw [hiSize, hjSize] at hbal
        apply Nat.eq_of_mul_eq_mul_left hpPos
        simpa [mul_assoc, mul_comm, mul_left_comm] using hbal
      have hbalQ :
          ((i.supp.ncard / p : ℕ) : ℚ) * (Q i j : ℚ) =
            ((j.supp.ncard / p : ℕ) : ℚ) * (Q j i : ℚ) := by
        exact_mod_cast hbalNat
      simpa [a, B, hij, Ne.symm hij] using hbalQ
  have hdiagB : ∀ i : C, ∑ j, B i j * B j i =
      2 * (s : ℚ) * B i i + (p : ℚ) * a i := by
    intro i
    have hsq := secondOrder_componentQuotientMatrix_sq_apply
      G hfree hd heven hmin hcard i i
    have hQsqNat : (∑ j, Q i j * Q j i) = d - 3 + i.supp.ncard := by
      simpa only [Matrix.mul_apply, Q, if_pos, mul_one] using hsq
    have hQsq : (∑ j, (Q i j : ℚ) * (Q j i : ℚ)) =
        (s : ℚ) ^ 2 + (p : ℚ) * a i := by
      have hcast := congrArg (fun n : ℕ ↦ (n : ℚ)) hQsqNat
      push_cast at hcast
      have hiSize : i.supp.ncard = p * (i.supp.ncard / p) := by
        exact (Nat.mul_div_cancel' (hall i)).symm
      rw [hiSize] at hcast
      push_cast at hcast
      have hdSub : d - 3 = s * s := by omega
      rw [hdSub] at hcast
      push_cast at hcast
      simpa [a, pow_two] using hcast
    have hexpand : (∑ j, B i j * B j i) =
        (∑ j, (Q i j : ℚ) * (Q j i : ℚ)) +
          2 * (s : ℚ) * (Q i i : ℚ) + (s : ℚ) ^ 2 := by
      calc
        (∑ j, B i j * B j i) =
            ∑ j, ((Q i j : ℚ) * (Q j i : ℚ) +
              if j = i then 2 * (s : ℚ) * (Q i i : ℚ) + (s : ℚ) ^ 2
              else 0) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i
                · subst j
                  simp [B]
                  ring
                · simp [B, hji, Ne.symm hji]
        _ = (∑ j, (Q i j : ℚ) * (Q j i : ℚ)) +
              ∑ j, if j = i then
                2 * (s : ℚ) * (Q i i : ℚ) + (s : ℚ) ^ 2 else 0 := by
              rw [Finset.sum_add_distrib]
        _ = (∑ j, (Q i j : ℚ) * (Q j i : ℚ)) +
              2 * (s : ℚ) * (Q i i : ℚ) + (s : ℚ) ^ 2 := by
                simp
                ring
    rw [hexpand, hQsq]
    simp only [B, if_pos]
    ring
  have hpRat : (p : ℚ) = N + 2 * s := by
    rw [hpEq, hNEq]
    have hsd : s ≤ d := by rw [hdEq]; nlinarith
    push_cast
    rw [Nat.cast_sub hsd]
    ring
  have hbound := weightedKernel_coefficient_le_diagonal
    B a (p : ℚ) (N : ℚ) (s : ℚ) haPos (by exact_mod_cast hNPos)
      (by exact_mod_cast hsPos) haSum hrowB hbalanceB hdiagB hpRat c
  unfold a B at hbound
  simp only [if_pos] at hbound
  have hboundNat : p * (c.supp.ncard / p) ≤ N * (Q c c + s) := by
    exact_mod_cast hbound
  simpa [Q, add_comm] using hboundNat

/-- On an odd defect component the diagonal quotient is at most two, so the
coefficient bound becomes uniform: `p * (|c|/p) ≤ N(s+2)`. -/
theorem secondOrder_odd_square_coefficient_mul_prime_le
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
    (hdEq : d = s * s + 3) (hpEq : p = d + s) (hNEq : N = d - s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcOdd : Odd c.supp.ncard) :
    p * (c.supp.ncard / p) ≤ N * (s + 2) := by
  obtain ⟨u, hu, huRange, huD, hthree⟩ :=
    exists_mixed_cycle_labeling G hfree hd heven hmin hcard
  letI : NeZero c.supp.ncard :=
    ⟨Nat.ne_of_gt (by have := hthree c; omega)⟩
  have hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) c c ≤ 2 :=
    secondOrder_equalOddCycleComponent_diagonal_le_two
      G hfree hd heven hmin hcard (hthree c) hcOdd c
        (u c) (hu c) (huRange c) (huD c)
  calc
    p * (c.supp.ncard / p) ≤
        N * (s + componentQuotientMatrix G (secondOrderDefectGraph G) c c) :=
      secondOrder_square_coefficient_mul_prime_le G hfree hd heven hmin
        hcard hp hboundary hdEq hpEq hNEq hall c
    _ ≤ N * (s + 2) := Nat.mul_le_mul_left N (Nat.add_le_add_left hdiag s)

/-- For the relevant primes `p ≥ 7`, the preceding bound simplifies to
`|c|/p ≤ s`: indeed `N(s+2) - ps = 6-2s ≤ 0`. -/
theorem secondOrder_odd_square_coefficient_le_root
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s) (hNEq : N = d - s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcOdd : Odd c.supp.ncard) :
    c.supp.ncard / p ≤ s := by
  have hbase := secondOrder_odd_square_coefficient_mul_prime_le
    G hfree hd heven hmin hcard hp hboundary hdEq hpEq hNEq hall c hcOdd
  have hsOdd : Odd s := by
    rw [← Nat.not_even_iff_odd]
    intro hsEven
    have hsSqEven : Even (s * s) := (Nat.even_mul).2 (Or.inl hsEven)
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hsSqEven
    omega
  have hsTwo : 2 ≤ s := by
    by_contra hs
    have hsLe : s ≤ 1 := by omega
    nlinarith [hdEq, hpEq, hp7]
  have hsThree : 3 ≤ s := by
    obtain ⟨k, hk⟩ := hsOdd
    omega
  have hsd : s ≤ d := by rw [hdEq]; nlinarith
  have hNadd : N + s = d := by rw [hNEq, Nat.sub_add_cancel hsd]
  have hupper : N * (s + 2) ≤ p * s := by
    nlinarith [hdEq, hpEq, hNadd]
  have hmul : p * (c.supp.ncard / p) ≤ p * s := hbase.trans hupper
  exact Nat.le_of_mul_le_mul_left hmul hpPos
    where hpPos : 0 < p := hp.pos

end

end Erdos85
