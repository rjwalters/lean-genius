import Proofs.Erdos85ConnectedNonbipartiteSpectralGap
import Proofs.Erdos85DesignatedTraceDimension

/-!
# Growing designated trace multiplicity in the connected stratum

This composes the connected-nonbipartite bottom spectral gap with the
Cauchy--Schwarz trace bound.  Once a finite family lists the designated
square-in-eigenfield adjacency roots (with multiplicity) and its residual
complement is sign-paired, its sum is `-q`; the family must then have size
growing at least on the order of `sqrt q`.
-/

open SimpleGraph

namespace Erdos85

/-- **Connected designated-sector growth.**  Let `D` be connected,
nonbipartite, and `(q-1)`-regular.  Any finite family of paired real roots
`theta_i² = q-1-mu_i`, carrying nonzero `mu_i`-eigenvectors of `D` and
having total trace `-q`, satisfies

`q² < 2(q-1) |s|²`.

The theorem is deliberately independent of how the designated family is
extracted from a rational primary factorization. -/
theorem connectedNonbipartite_designatedTrace_card_sq_growth
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (hnotbip : ¬D.IsBipartite)
    {q : ℕ} (hq : 2 ≤ q) (hreg : ∀ x, D.degree x = q - 1)
    (s : Finset ι) (μ θ : ι → ℝ) (w : ι → V → ℝ)
    (hw : ∀ i ∈ s, w i ≠ 0)
    (heigen : ∀ i ∈ s, ∀ x,
      ∑ y ∈ D.neighborFinset x, w i y = μ i * w i x)
    (hpair : ∀ i ∈ s, (θ i) ^ 2 = ((q - 1 : ℕ) : ℝ) - μ i)
    (hsum : ∑ i ∈ s, θ i = -(q : ℝ)) :
    (q : ℝ) ^ 2 < 2 * ((q : ℝ) - 1) * (s.card : ℝ) ^ 2 := by
  apply binarySquare_designatedTrace_card_sq_growth s θ (by omega) hsum
  intro i hi
  have hroot := paired_root_sq_lt_two_mul_degree_of_connected_nonbipartite
    D hconn hnotbip (q - 1) hreg (μ i) (θ i) (w i)
      (hw i hi) (heigen i hi) (hpair i hi)
  rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at hroot
  exact hroot

end Erdos85

#print axioms
  Erdos85.connectedNonbipartite_designatedTrace_card_sq_growth
