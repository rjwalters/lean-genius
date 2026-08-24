import Proofs.Erdos85F2WalkWeightPotential

/-!
# Owner-free boundary potential census

In the additive branch of `(73rnz_cjibkq)`, every routed segment is priced
by its two endpoint potentials.  Summing a finite family therefore depends
only on the mod-two endpoint census, which is the endpoint term of
`(73rnz_cjibkzn)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Mod-two multiplicity with which `v` occurs as either endpoint of a
finite route family. -/
def f2RouteEndpointCensus
    {I V : Type*} [Fintype I] [DecidableEq V]
    (start finish : I → V) (v : V) : ZMod 2 :=
  ∑ i, ((if start i = v then 1 else 0) +
    (if finish i = v then 1 else 0))

/-- The sum of endpoint potentials is the potential paired with the endpoint
census. -/
theorem sum_endpointPotential_eq_endpointCensus_dot
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (start finish : I → V) (lam : V → ZMod 2) :
    (∑ i, (lam (start i) + lam (finish i))) =
      ∑ v, f2RouteEndpointCensus start finish v * lam v := by
  classical
  simp only [f2RouteEndpointCensus, Finset.sum_add_distrib, add_mul,
    Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp

/-- **Owner-free additive census (`73rnz_cjibkzn`).**  Total route price is
exactly the endpoint-census pairing with the additive potential. -/
theorem sum_f2WalkWeight_eq_endpointCensus_dot_of_potential
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {P : SimpleGraph V} (start finish : I → V)
    (route : ∀ i, P.Walk (start i) (finish i))
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, P.Adj u v → k u v = lam u + lam v) :
    (∑ i, f2WalkWeight k (route i)) =
      ∑ v, f2RouteEndpointCensus start finish v * lam v := by
  calc
    (∑ i, f2WalkWeight k (route i)) =
        ∑ i, (lam (start i) + lam (finish i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact f2WalkWeight_eq_endpointPotentialSum k lam hpotential (route i)
    _ = ∑ v, f2RouteEndpointCensus start finish v * lam v :=
      sum_endpointPotential_eq_endpointCensus_dot start finish lam

/-- If every endpoint occurs evenly, every additive owner-free route family
has zero total price. -/
theorem sum_f2WalkWeight_eq_zero_of_endpointCensus_zero
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {P : SimpleGraph V} (start finish : I → V)
    (route : ∀ i, P.Walk (start i) (finish i))
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, P.Adj u v → k u v = lam u + lam v)
    (hcensus : ∀ v, f2RouteEndpointCensus start finish v = 0) :
    (∑ i, f2WalkWeight k (route i)) = 0 := by
  rw [sum_f2WalkWeight_eq_endpointCensus_dot_of_potential
    start finish route k lam hpotential]
  simp [hcensus]

end

end Erdos85

#print axioms Erdos85.sum_endpointPotential_eq_endpointCensus_dot
#print axioms Erdos85.sum_f2WalkWeight_eq_endpointCensus_dot_of_potential
#print axioms Erdos85.sum_f2WalkWeight_eq_zero_of_endpointCensus_zero
