import Proofs.Erdos85OrderFortyNineMissBidegreeArithmetic

/-!
# Pairpoint-neighborhood profile arithmetic at order 49

The three disjoint degree-five pairpoint cells have total size fifteen and
total support weight nine.  Since the pairpoint matching core has zero or one
edge, the cells contain respectively zero or two support-two vertices.  These
two equations fix both the cell profile and its complement.
-/

namespace Erdos85

/-- The union `P` of the three pairpoint neighborhoods has profile
`(support0,support1,support2) = (6,9,0)` or `(8,5,2)`. -/
theorem pairpointNeighborhood_profile
    {p0 p1 p2 : ℕ}
    (hcard : p0 + p1 + p2 = 15)
    (hweight : p1 + 2 * p2 = 9)
    (hcore : p2 = 0 ∨ p2 = 2) :
    (p0 = 6 ∧ p1 = 9 ∧ p2 = 0) ∨
      (p0 = 8 ∧ p1 = 5 ∧ p2 = 2) := by
  rcases hcore with hp2 | hp2
  · left
    omega
  · right
    omega

/-- The complementary 31 vertices have profile `(19,9,3)` in the zero-edge
core and `(17,13,1)` in the one-edge core. -/
theorem outsidePairpointNeighborhood_profile
    {p0 p1 p2 : ℕ}
    (hcard : p0 + p1 + p2 = 15)
    (hweight : p1 + 2 * p2 = 9)
    (hcore : p2 = 0 ∨ p2 = 2) :
    (25 - p0 = 19 ∧ 18 - p1 = 9 ∧ 3 - p2 = 3) ∨
      (25 - p0 = 17 ∧ 18 - p1 = 13 ∧ 3 - p2 = 1) := by
  rcases pairpointNeighborhood_profile hcard hweight hcore with hp | hp
  · left
    rcases hp with ⟨rfl, rfl, rfl⟩
    norm_num
  · right
    rcases hp with ⟨rfl, rfl, rfl⟩
    norm_num

/-- Rectangle moment of the witness biclique decomposition.  A vertex of
support `s` outside `P` has `4-s` support-zero neighbors and three
support-one neighbors.  The moment is 432 in the zero-edge core and 426 in
the one-edge core. -/
theorem outsidePairpointNeighborhood_rectangleMoment
    {w0 w1 w2 : ℕ}
    (hprofile :
      (w0 = 19 ∧ w1 = 9 ∧ w2 = 3) ∨
      (w0 = 17 ∧ w1 = 13 ∧ w2 = 1)) :
    (w0 * Nat.choose 4 2 + w1 * Nat.choose 3 2 +
        w2 * Nat.choose 2 2) * Nat.choose 3 2 = 432 ∨
      (w0 * Nat.choose 4 2 + w1 * Nat.choose 3 2 +
        w2 * Nat.choose 2 2) * Nat.choose 3 2 = 426 := by
  rcases hprofile with hp | hp
  · left
    rcases hp with ⟨rfl, rfl, rfl⟩
    norm_num [Nat.choose]
  · right
    rcases hp with ⟨rfl, rfl, rfl⟩
    norm_num [Nat.choose]

end Erdos85

#print axioms Erdos85.pairpointNeighborhood_profile
#print axioms Erdos85.outsidePairpointNeighborhood_profile
#print axioms Erdos85.outsidePairpointNeighborhood_rectangleMoment
