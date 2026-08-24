import Proofs.Erdos85OwnerFreeBoundaryPotentialCensus
import Proofs.Erdos85PoleOwnerOddCellObstruction

/-!
# Ordinary route census cannot absorb a pole-owner source

Every ordinary route has two endpoints.  Hence the aggregate parity of its
labelled endpoint census is zero, regardless of how endpoints are labelled.
The derived pole-owner source has aggregate parity one.  Consequently
ordinary routes alone cannot cancel that source cell by cell: a residual or
special endpoint is forced.
-/

namespace Erdos85

noncomputable section

/-- Endpoint parity of a route family, grouped by an arbitrary finite label. -/
def f2LabelledRouteEndpointCensus
    {I V L : Type*} [Fintype I] [DecidableEq L]
    (start finish : I → V) (label : V → L) (ell : L) : ZMod 2 :=
  ∑ i, ((if label (start i) = ell then 1 else 0) +
    (if label (finish i) = ell then 1 else 0))

/-- A complete family of two-ended routes has even total endpoint census,
after grouping by any finite label set. -/
theorem sum_f2LabelledRouteEndpointCensus_eq_zero
    {I V L : Type*} [Fintype I] [Fintype L] [DecidableEq L]
    (start finish : I → V) (label : V → L) :
    ∑ ell, f2LabelledRouteEndpointCensus start finish label ell = 0 := by
  classical
  calc
    (∑ ell, f2LabelledRouteEndpointCensus start finish label ell) =
        ∑ i, ∑ ell,
          ((if label (start i) = ell then 1 else 0) +
            (if label (finish i) = ell then 1 else 0)) := by
      simp only [f2LabelledRouteEndpointCensus]
      exact Finset.sum_comm
    _ = ∑ _i : I, ((1 : ZMod 2) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      rw [Finset.sum_add_distrib]
      simp [eq_comm]
    _ = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
      exact Finset.sum_const_zero

/-- Grouping the vertexwise endpoint census from the additive-potential
ledger gives the same labelled census. -/
theorem f2LabelledRouteEndpointCensus_eq_vertexCensus_sum
    {I V L : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] [DecidableEq L]
    (start finish : I → V) (label : V → L) (ell : L) :
    f2LabelledRouteEndpointCensus start finish label ell =
      ∑ v, (if label v = ell then f2RouteEndpointCensus start finish v else 0) := by
  classical
  simpa [f2LabelledRouteEndpointCensus, mul_ite] using
    (sum_endpointPotential_eq_endpointCensus_dot start finish
      (fun v => if label v = ell then (1 : ZMod 2) else 0))

/-- **Ordinary-route no-go (`73rnz_cjibko`).**  No labelled census of
ordinary two-ended routes can cancel the four derived source channels of one
pole owner cell by cell. -/
theorem not_poleOwnerSource_cancelled_by_routeEndpointCensus
    {I V : Type*} [Fintype I]
    (k sigma activity : ZMod 2) (hsource : k + sigma = 1)
    (start finish : I → V) (label : V → PoleOwnerChannelLabel) :
    ¬ ∀ ell,
      poleOwnerSourceAt (poleOwnerFlipChannels k sigma activity) ell +
        f2LabelledRouteEndpointCensus start finish label ell = 0 := by
  intro hcancel
  have hodd := poleOwner_downstream_odd_of_cellwise_cancel
    k sigma activity hsource
      (f2LabelledRouteEndpointCensus start finish label) hcancel
  have heven := sum_f2LabelledRouteEndpointCensus_eq_zero start finish label
  rw [heven] at hodd
  exact zero_ne_one hodd.1

end

end Erdos85

#print axioms Erdos85.sum_f2LabelledRouteEndpointCensus_eq_zero
#print axioms Erdos85.f2LabelledRouteEndpointCensus_eq_vertexCensus_sum
#print axioms Erdos85.not_poleOwnerSource_cancelled_by_routeEndpointCensus
