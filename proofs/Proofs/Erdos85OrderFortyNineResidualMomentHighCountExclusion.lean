import Proofs.Erdos85OrderFortyNineResidualLargeRoot
import Proofs.Erdos85OrderFortyNineResidualMomentLargeHighExclusion
import Proofs.Erdos85RealRootPowerSums

/-!
# Excluding 19 and 21 high vertices at order 49
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

theorem orderFortyNine_high_card_ne_nineteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    (squareOrderHighVertices G 7).card ≠ 19 := by
  intro hH
  obtain ⟨Q, lambda, hQmonic, _, hdegree, _, hsecond, hfourth,
      _, hsplit, hlambda, hlower⟩ :=
    exists_orderFortyNineSeven_residual_largeRoot
      G hfree hmin hcover hcard ha
  let Qr := Q.map (algebraMap ℚ ℝ)
  have hQne : Q ≠ 0 := hQmonic.ne_zero
  have hrootsCard : Qr.roots.card = 13 := by
    rw [← hsplit.natDegree_eq_card_roots]
    simpa [Qr, hH] using hdegree
  have hsecondR : realRootPowerSum Qr 2 = 110 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 2 hsplit hQne
    rw [hsecond, hH] at hc
    norm_num at hc
    exact_mod_cast hc.symm
  have hfourthR : realRootPowerSum Qr 4 = 3246 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 4 hsplit hQne
    rw [hfourth, hH] at hc
    norm_num at hc
    exact_mod_cast hc.symm
  have hcauchy := realRootPowerSum_cauchy_erase Qr hlambda
  rw [hrootsCard, hsecondR, hfourthR] at hcauchy
  norm_num at hcauchy
  have hcauchy' :
      (110 - lambda ^ 2) ^ 2 ≤ 12 * (3246 - (lambda ^ 2) ^ 2) := by
    convert hcauchy using 1 <;> ring
  apply false_of_orderFortyNine_h19_residualMoment_bounds (lambda ^ 2)
  · norm_num [hH] at hlower ⊢
    exact hlower
  · exact hcauchy'

theorem orderFortyNine_high_card_ne_twentyOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    (squareOrderHighVertices G 7).card ≠ 21 := by
  intro hH
  obtain ⟨Q, lambda, hQmonic, _, hdegree, _, hsecond, hfourth,
      _, hsplit, hlambda, hlower⟩ :=
    exists_orderFortyNineSeven_residual_largeRoot
      G hfree hmin hcover hcard ha
  let Qr := Q.map (algebraMap ℚ ℝ)
  have hQne : Q ≠ 0 := hQmonic.ne_zero
  have hrootsCard : Qr.roots.card = 9 := by
    rw [← hsplit.natDegree_eq_card_roots]
    simpa [Qr, hH] using hdegree
  have hsecondR : realRootPowerSum Qr 2 = 84 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 2 hsplit hQne
    rw [hsecond, hH] at hc
    norm_num at hc
    exact_mod_cast hc.symm
  have hfourthR : realRootPowerSum Qr 4 = 3108 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 4 hsplit hQne
    rw [hfourth, hH] at hc
    norm_num at hc
    exact_mod_cast hc.symm
  have hcauchy := realRootPowerSum_cauchy_erase Qr hlambda
  rw [hrootsCard, hsecondR, hfourthR] at hcauchy
  norm_num at hcauchy
  have hcauchy' :
      (84 - lambda ^ 2) ^ 2 ≤ 8 * (3108 - (lambda ^ 2) ^ 2) := by
    convert hcauchy using 1 <;> ring
  apply false_of_orderFortyNine_h21_residualMoment_bounds (lambda ^ 2)
  · norm_num [hH] at hlower ⊢
    exact hlower
  · exact hcauchy'

end

end Erdos85
