import Proofs.Erdos85ExceptionalBalancedLeakageAggregate

/-!
# Component growth at the half-empty endpoint

When the empty exceptional population reaches its incidence-capacity endpoint
`2e=q`, balanced leakage is too large to fit into only `q-c` additional
vertices.  Every mixed nonsaturated exceptional core therefore lies in a
defect component strictly larger than `q`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic endpoint of the balanced leakage inequality. -/
theorem halfEmpty_balancedLeakage_component_gt
    {q e f c t m : ℕ}
    (hqe : q = 2 * e) (hcf : c = f + e)
    (hf : 0 < f) (hcq : c < q)
    (hagg :
      2 * q * (e * (q - c)) + (q * q + f + q) * t ≤
        (2 * q * q + e) * t)
    (hcomponent : c + t ≤ m) :
    q < m := by
  subst q
  subst c
  have hePos : 0 < e := by omega
  have hefLe : f + e ≤ 2 * e := by omega
  by_contra hmq
  have hm : m ≤ 2 * e := by omega
  have ht : t ≤ e - f := by omega
  have haggZ :
    (2 * (2 * e) * (e * (2 * e - (f + e))) +
          ((2 * e) * (2 * e) + f + 2 * e) * t : ℤ) ≤
        (2 * (2 * e) * (2 * e) + e) * t := by
    exact_mod_cast hagg
  have hfe : f ≤ e := by omega
  have htZ : (t : ℤ) ≤ ((e - f : ℕ) : ℤ) := by exact_mod_cast ht
  rw [Int.ofNat_sub hfe] at htZ
  have hfZ : (0 : ℤ) < f := by exact_mod_cast hf
  have heZ : (0 : ℤ) < e := by exact_mod_cast hePos
  have hdZ : (0 : ℤ) < (e : ℤ) - f := by omega
  let K : ℤ := 4 * (e : ℤ) * e - e - f
  have hcoreZ : 4 * (e : ℤ) * e * ((e : ℤ) - f) ≤ K * t := by
    dsimp only [K]
    ring_nf at haggZ ⊢
    linarith
  have htPos : (0 : ℤ) < t := by
    by_contra ht0
    have : (t : ℤ) = 0 := by omega
    rw [this] at hcoreZ
    nlinarith [mul_pos (mul_pos (by positivity : (0 : ℤ) < 4 * e) heZ) hdZ]
  have hKlt : K < 4 * (e : ℤ) * e := by
    dsimp only [K]
    nlinarith
  have hgapPos : (0 : ℤ) < 4 * (e : ℤ) * e - K := by omega
  have hstrictProd : K * (t : ℤ) < 4 * (e : ℤ) * e * t := by
    nlinarith [mul_pos hgapPos htPos]
  have hcoefNonneg : (0 : ℤ) ≤ 4 * (e : ℤ) * e := by positivity
  have hupperZ := mul_le_mul_of_nonneg_left htZ hcoefNonneg
  nlinarith

/-- Graph-facing endpoint: a mixed nonsaturated final exceptional support
with exactly `q/2` empty centers forces its empty-pole defect component above
order `q`. -/
theorem binarySquare_finalDyadic_halfEmpty_mixed_component_card_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hhalfEmpty : q = 2 * (emptyLineCenters G S).card)
    (hfullNonempty : (fullLineCenters G S q).Nonempty)
    (hstrict :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card < q)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    q < ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  let E := emptyLineCenters G S
  let F := fullLineCenters G S q
  let C := F ∪ E
  let T := exceptionalEmptyLeakageBoundary G S q
  let m := ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard
  have hdisj := fullLineCenters_disjoint_emptyLineCenters
    G S (by omega : 0 < q)
  have hCcard : C.card = F.card + E.card := by
    dsimp only [C]
    rw [Finset.card_union_of_disjoint hdisj]
  have hagg :=
    binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_intrinsic
      G hfree hq hqa hreg hcard S hdiv hemptyClique
  change 2 * q * (E.card * (q - C.card)) +
      (q * q + F.card + q) * T.card ≤
    (2 * q * q + E.card) * T.card at hagg
  have hcomponent := exceptional_card_add_leakageBoundary_card_le_component
    G hfree (by omega) hreg S hemptyClique pole hpole
  change C.card + T.card ≤ m at hcomponent
  apply halfEmpty_balancedLeakage_component_gt
    hhalfEmpty hCcard
  · exact Finset.card_pos.mpr hfullNonempty
  · exact hstrict
  · exact hagg
  · exact hcomponent

end

end Erdos85

#print axioms Erdos85.halfEmpty_balancedLeakage_component_gt
#print axioms
  Erdos85.binarySquare_finalDyadic_halfEmpty_mixed_component_card_gt
