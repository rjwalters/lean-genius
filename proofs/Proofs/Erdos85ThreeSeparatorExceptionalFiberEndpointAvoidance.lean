import Proofs.Erdos85ThreeSeparatorRFiberInternalCommonExclusion
import Proofs.Erdos85ThreeSeparatorUniformExceptionalMatchingCount

/-!
# Exceptional fibers do not join two path endpoints

Every center `z ∈ N_A(c)` has exactly two K-neighbors.  One is `c` itself.
When `c ∉ X`, at most one further K-neighbor can lie in the X-fiber of z.
Since `K ∩ X` is the degree-one locus of the first-slice internal graph,
this is the endpoint-avoidance assertion (B34).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Cardinal core of B34. -/
theorem exceptionalFiber_inter_endpointSet_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K : Finset V) (c z : V)
    (hcK : c ∈ K)
    (hcnotX : c ∉ X)
    (hzc : A.Adj z c)
    (hzKdegree : (A.neighborFinset z ∩ K).card = 2) :
    ((A.neighborFinset z ∩ X) ∩ K).card ≤ 1 := by
  have hcnotFiber : c ∉ (A.neighborFinset z ∩ X) ∩ K := by
    simp [hcnotX]
  have hsubset : insert c ((A.neighborFinset z ∩ X) ∩ K) ⊆
      A.neighborFinset z ∩ K := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with hvc | hv
    · subst v
      exact Finset.mem_inter.mpr
        ⟨(A.mem_neighborFinset z c).mpr hzc, hcK⟩
    · have hvZX := Finset.mem_inter.mp hv |>.1
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mp hvZX |>.1, Finset.mem_inter.mp hv |>.2⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hcnotFiber, hzKdegree] at hcard
  omega

/-- Pointwise B34: two X-points in the same exceptional fiber cannot both
be path endpoints (K-points). -/
theorem exceptionalFiber_no_two_distinct_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K : Finset V) (c z x y : V)
    (hcK : c ∈ K)
    (hcnotX : c ∉ X)
    (hzc : A.Adj z c)
    (hzKdegree : (A.neighborFinset z ∩ K).card = 2)
    (hxX : x ∈ X) (hxK : x ∈ K) (hzx : A.Adj z x)
    (hyX : y ∈ X) (hyK : y ∈ K) (hzy : A.Adj z y) :
    x = y := by
  by_contra hxy
  have hle := exceptionalFiber_inter_endpointSet_card_le_one
    A X K c z hcK hcnotX hzc hzKdegree
  have hpair : {x, y} ⊆ (A.neighborFinset z ∩ X) ∩ K := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvx | hvy
    · subst v
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨(A.mem_neighborFinset z x).mpr hzx, hxX⟩, hxK⟩
    · subst v
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨(A.mem_neighborFinset z y).mpr hzy, hyX⟩, hyK⟩
  have hcard := Finset.card_le_card hpair
  have htwo : ({x, y} : Finset V).card = 2 := by simp [hxy]
  rw [htwo] at hcard
  omega

end

end Erdos85

#print axioms Erdos85.exceptionalFiber_inter_endpointSet_card_le_one
#print axioms Erdos85.exceptionalFiber_no_two_distinct_endpoints
