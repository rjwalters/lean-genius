import Proofs.Erdos85SquareQuotientGraphBound
import Proofs.Erdos85BoundaryQuotientExcess

/-!
# A forced dense block at the minimum square component

In the exact square family, write the minimum component order as `p*a`.
The local excess identity says that its equal-size quotient blocks carry
total excess `p*a-3`.  If every such quotient entry were at most `a`, this
would be at most `(a-1)d`; but

`p*a - 3 - (a-1)d = s(a+s) > 0`

because `p=d+s` and `d=s²+3`.  Hence an equal-size block of multiplicity at
least `a+1` is forced.  This is a uniform quotient motif, not a cofactor
case split.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Minimum-component dense-block forcing.** -/
theorem secondOrder_square_minimum_exists_large_equalSize_entry
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hdEq : d = s * s + 3) (hpEq : p = d + s)
    (hall : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ e.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e.supp.ncard = c.supp.ncard ∧
        c.supp.ncard / p + 1 ≤
          componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let a := c.supp.ncard / p
  have hpPos : 0 < p := hp.pos
  have hsPos : 0 < s := by
    by_contra hs0
    have hsZero : s = 0 := Nat.eq_zero_of_not_pos hs0
    rw [hsZero, zero_mul, zero_add] at hdEq
    omega
  have hcPos : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
  have hpLe : p ≤ c.supp.ncard := Nat.le_of_dvd hcPos (hall c)
  have haPos : 0 < a := Nat.div_pos hpLe hpPos
  have hcSize : c.supp.ncard = p * a :=
    (Nat.mul_div_cancel' (hall c)).symm
  have hrowNat : ∑ e : C, Q c e = d :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hmin hcard c
  have hrowInt : ∑ e : C, (Q c e : ℤ) = d := by
    exact_mod_cast hrowNat
  have hexcess := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hmin hcard c hcmin
  by_contra hnone
  push Not at hnone
  have hterm (e : C) :
      (if e.supp.ncard = c.supp.ncard then
          (Q c e : ℤ) * ((Q c e : ℤ) - 1)
        else 0) ≤ ((a : ℤ) - 1) * (Q c e : ℤ) := by
    by_cases heq : e.supp.ncard = c.supp.ncard
    · rw [if_pos heq]
      have hq : Q c e ≤ a := by
        have := hnone e heq
        change Q c e < a + 1 at this
        omega
      have hqZ : (Q c e : ℤ) ≤ (a : ℤ) := by exact_mod_cast hq
      have hqNonneg : (0 : ℤ) ≤ (Q c e : ℤ) := by positivity
      have haOne : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast haPos
      nlinarith
    · rw [if_neg heq]
      have haOne : (1 : ℤ) ≤ a := by exact_mod_cast haPos
      positivity
  have hsumLe :
      (∑ e : C, if e.supp.ncard = c.supp.ncard then
          (Q c e : ℤ) * ((Q c e : ℤ) - 1) else 0) ≤
        ((a : ℤ) - 1) * d := by
    calc
      _ ≤ ∑ e : C, ((a : ℤ) - 1) * (Q c e : ℤ) :=
        Finset.sum_le_sum fun e _ ↦ hterm e
      _ = ((a : ℤ) - 1) * ∑ e : C, (Q c e : ℤ) := by
        rw [Finset.mul_sum]
      _ = ((a : ℤ) - 1) * d := by rw [hrowInt]
  rw [hexcess, hcSize] at hsumLe
  have hpEqInt : (p : ℤ) = d + s := by exact_mod_cast hpEq
  have hdEqInt : (d : ℤ) = s * s + 3 := by exact_mod_cast hdEq
  have haPosInt : (0 : ℤ) < a := by exact_mod_cast haPos
  push_cast at hsumLe
  rw [hpEqInt, hdEqInt] at hsumLe
  nlinarith

end

end Erdos85
