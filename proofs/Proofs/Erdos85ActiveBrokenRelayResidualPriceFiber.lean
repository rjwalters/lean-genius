import Proofs.Erdos85ActiveBrokenRelayEdgeWitness

/-!
# Witness fibers of residual-priced active relay edges

Restrict the canonical active witness label to `R_s ∩ K`.  Its label fibers
are the local price contributions `Theta_w`; they vanish at inactive
witnesses and sum exactly to the global residual price.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Forget that an edge lies in the right factor of an intersection. -/
def infEdgeFinsetToLeft
    {V : Type*} [Fintype V] [DecidableEq V]
    (R K : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel K.Adj]
    (e : (R ⊓ K).edgeFinset) : R.edgeFinset := by
  refine ⟨e.1, ?_⟩
  generalize heq : e.1 = z
  induction z using Sym2.inductionOn with
  | _ x y =>
      have hRK : (R ⊓ K).Adj x y := by
        have he : s(x, y) ∈ (R ⊓ K).edgeSet := by
          have he' : e.1 ∈ (R ⊓ K).edgeSet := by
            simpa only [SimpleGraph.mem_edgeFinset] using e.2
          rw [← heq]
          exact he'
        simpa only [SimpleGraph.mem_edgeSet] using he
      simpa only [SimpleGraph.mem_edgeFinset, heq,
        SimpleGraph.mem_edgeSet] using hRK.1

/-- Canonical witness label of an edge in `R_s ∩ K`. -/
def activeBrokenPricedRelayEdgeWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (e : ((activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed) ⊓
      binaryTransportResidualGraph A hq hreg).edgeFinset) : V :=
  activeBrokenRelayEdgeWitness A hfree active mate hclosed hinvol hfixed
    (infEdgeFinsetToLeft
      (activeBrokenWitnessRelayGraph A active mate hclosed hinvol hfixed)
      (binaryTransportResidualGraph A hq hreg) e)

/-- Local residual-price contribution at witness `w`. -/
def activeBrokenRelayResidualPriceFiberCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) (w : V) : ℕ :=
  ((Finset.univ : Finset
    (((activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed) ⊓
      binaryTransportResidualGraph A hq hreg).edgeFinset)).filter fun e =>
        activeBrokenPricedRelayEdgeWitness A hfree hq hreg active mate
          hclosed hinvol hfixed e = w).card

theorem activeBrokenPricedRelayEdgeWitness_active
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (e : ((activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed) ⊓
      binaryTransportResidualGraph A hq hreg).edgeFinset) :
    active (activeBrokenPricedRelayEdgeWitness A hfree hq hreg active mate
      hclosed hinvol hfixed e) := by
  exact (activeBrokenRelayEdgeWitness_spec A hfree active mate
    hclosed hinvol hfixed (infEdgeFinsetToLeft
      (activeBrokenWitnessRelayGraph A active mate hclosed hinvol hfixed)
      (binaryTransportResidualGraph A hq hreg) e)).1

/-- Inactive witnesses contribute no residual-priced relay edge. -/
theorem activeBrokenRelayResidualPriceFiberCard_eq_zero_of_not_active
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) {w : V} (hw : ¬ active w) :
    activeBrokenRelayResidualPriceFiberCard A hfree hq hreg active mate
      hclosed hinvol hfixed w = 0 := by
  apply Finset.card_eq_zero.mpr
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false]
  intro heq
  exact hw (heq ▸ activeBrokenPricedRelayEdgeWitness_active
    A hfree hq hreg active mate hclosed hinvol hfixed e)

/-- Exact scalar price decomposition: `|E(R_s ∩ K)| = Σ_w Theta_w`. -/
theorem activeBrokenRelay_inf_residual_card_eq_sum_priceFiberCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) :
    (((activeBrokenWitnessRelayGraph A active mate hclosed hinvol hfixed) ⊓
      binaryTransportResidualGraph A hq hreg).edgeFinset.card) =
      ∑ w : V, activeBrokenRelayResidualPriceFiberCard A hfree hq hreg
        active mate hclosed hinvol hfixed w := by
  rw [← Fintype.card_coe]
  apply Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
  intro e _
  exact Finset.mem_univ _

end

end Erdos85

#print axioms Erdos85.activeBrokenPricedRelayEdgeWitness_active
#print axioms Erdos85.activeBrokenRelayResidualPriceFiberCard_eq_zero_of_not_active
#print axioms Erdos85.activeBrokenRelay_inf_residual_card_eq_sum_priceFiberCard
