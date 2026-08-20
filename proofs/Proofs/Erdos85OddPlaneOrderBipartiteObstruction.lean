import Proofs.Erdos85GadgetDegreeSquares
import Proofs.Erdos101ProblemOQ02

/-!
# The plane-minus-two target cannot be a bipartite incidence graph

The existence jaw at an odd plane order seeks a `q`-regular C4-free graph on
`q^2 - 1` vertices.  If such a graph were bipartite, its two sides would have
the same size.  The theorem below isolates the resulting incidence structure
and proves that its parameters are impossible by counting pairs on the other
side.
-/

namespace Erdos85

/-- There is no regular linear incidence structure with two equally-sized
parts whose combined order is `q^2 - 1` and whose degree is `q`.

`huniq` is the incidence form of C4-freeness: two distinct points lie on at
most one common line.  The two cardinality equations say that each part has
size `(q^2 - 1) / 2`, without introducing natural-number division. -/
theorem false_of_planeMinusTwo_regular_linear_incidence
    {Point Line : Type*}
    [Fintype Point] [Fintype Line]
    [DecidableEq Point] [DecidableEq Line]
    (Inc : Point → Line → Prop) [DecidableRel Inc]
    (q : ℕ) (hq : 2 ≤ q)
    (hPoint : 2 * Fintype.card Point + 1 = q * q)
    (hLine : 2 * Fintype.card Line + 1 = q * q)
    (hregular : ∀ ell : Line,
      (Erdos101OQ02ST.pointsOn Inc Finset.univ ell).card = q)
    (huniq : ∀ p ∈ (Finset.univ : Finset Point),
      ∀ r ∈ (Finset.univ : Finset Point), p ≠ r →
      ∀ ell₁ ∈ (Finset.univ : Finset Line),
      ∀ ell₂ ∈ (Finset.univ : Finset Line),
      Inc p ell₁ → Inc r ell₁ → Inc p ell₂ → Inc r ell₂ → ell₁ = ell₂) :
    False := by
  have hpair := Erdos101OQ02ST.sum_choose_two_le Inc
    (Finset.univ : Finset Point) (Finset.univ : Finset Line) huniq
  simp only [Finset.sum_const, Finset.card_univ, hregular,
    nsmul_eq_mul] at hpair
  have hcards : Fintype.card Point = Fintype.card Line := by omega
  have hPointPos : 0 < Fintype.card Point := by
    by_contra hz
    have hz' : Fintype.card Point = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz'] at hPoint
    norm_num at hPoint
    nlinarith
  have hqChoose := two_mul_choose_two q
  have hPointChoose := two_mul_choose_two (Fintype.card Point)
  rw [hcards] at hPoint
  rw [hcards] at hPointChoose
  rw [hcards] at hpair
  have hscaled :
      Fintype.card Line * (q * (q - 1)) ≤
        Fintype.card Line * (Fintype.card Line - 1) := by
    calc
      _ = 2 * (Fintype.card Line * q.choose 2) := by
        rw [← hqChoose]
        ring
      _ ≤ 2 * (Fintype.card Line).choose 2 := Nat.mul_le_mul_left 2 hpair
      _ = _ := hPointChoose
  have hLinePos : 0 < Fintype.card Line := by simpa [hcards] using hPointPos
  have hcancel : q * (q - 1) ≤ Fintype.card Line - 1 :=
    Nat.le_of_mul_le_mul_left hscaled hLinePos
  have hqPred : q - 1 + 1 = q := by omega
  have hLinePred : Fintype.card Line - 1 + 1 = Fintype.card Line := by omega
  nlinarith

end Erdos85
