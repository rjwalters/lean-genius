import Proofs.Erdos85OrderFortyNineGeneralHighProfile

/-!
# The seven-high incidence profile

The universal local and global profile laws specialize cleanly at seven
high vertices.  The only remaining parameter is the number of blocks in a
linear triple system on seven points; it is at most seven and every point
has triple degree at most three.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-high stratum, if `t=n₃`, then
`n₀=7-t`, `n₁=14+3t`, and `n₂=21-3t`, with `t≤7`. -/
theorem orderFortyNine_highIncidence_profile_of_seven_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 7) :
    let n := orderFortyNineHighIncidenceCount G
    n 0 + n 3 = 7 ∧ n 1 = 14 + 3 * n 3 ∧
      n 2 + 3 * n 3 = 21 ∧ n 3 ≤ 7 := by
  dsimp only
  let n := orderFortyNineHighIncidenceCount G
  change n 0 + n 3 = 7 ∧ n 1 = 14 + 3 * n 3 ∧
    n 2 + 3 * n 3 = 21 ∧ n 3 ≤ 7
  have hp := orderFortyNine_highIncidence_general_profile
    G hfree hmin hcard
  dsimp only at hp
  dsimp [n] at *
  rw [hHigh] at hp
  omega

/-- The parameterized seven-high profile consists of exactly eight numerical
possibilities.  Keeping this as a literal disjunction gives finite-search
consumers no arithmetic side condition to reconstruct. -/
set_option maxHeartbeats 800000 in
theorem orderFortyNine_highIncidence_profiles_of_seven_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 7) :
    let n := orderFortyNineHighIncidenceCount G
    (n 0 = 7 ∧ n 1 = 14 ∧ n 2 = 21 ∧ n 3 = 0) ∨
    (n 0 = 6 ∧ n 1 = 17 ∧ n 2 = 18 ∧ n 3 = 1) ∨
    (n 0 = 5 ∧ n 1 = 20 ∧ n 2 = 15 ∧ n 3 = 2) ∨
    (n 0 = 4 ∧ n 1 = 23 ∧ n 2 = 12 ∧ n 3 = 3) ∨
    (n 0 = 3 ∧ n 1 = 26 ∧ n 2 = 9 ∧ n 3 = 4) ∨
    (n 0 = 2 ∧ n 1 = 29 ∧ n 2 = 6 ∧ n 3 = 5) ∨
    (n 0 = 1 ∧ n 1 = 32 ∧ n 2 = 3 ∧ n 3 = 6) ∨
    (n 0 = 0 ∧ n 1 = 35 ∧ n 2 = 0 ∧ n 3 = 7) := by
  dsimp only
  have hp := orderFortyNine_highIncidence_profile_of_seven_high
    G hfree hmin hcard hHigh
  dsimp only at hp
  have hn3 : orderFortyNineHighIncidenceCount G 3 ≤ 7 := hp.2.2.2
  interval_cases orderFortyNineHighIncidenceCount G 3 <;> omega

/-- Every high point in the seven-high stratum lies in at most three triple
blocks; locally `a₁=a₃+2` and `a₂+2a₃=6`. -/
theorem orderFortyNine_highNeighborhood_profile_of_seven_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    {v : V} (hv : G.degree v = 8) :
    let a := fun i => ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = i).card
    a 1 = a 3 + 2 ∧ a 2 + 2 * a 3 = 6 ∧ a 3 ≤ 3 := by
  dsimp only
  have hp := orderFortyNine_highNeighborhood_general_profile
    G hfree hmin hcard hv
  dsimp only at hp
  rw [hHigh] at hp
  omega

end

end Erdos85
