import Proofs.Erdos85ConnectedBlindSectorOddTrace
import Proofs.Erdos85GlobalOrbitSquare

/-!
# A nonblind designated orbit at odd dyadic degree

The global orbit-square theorem supplies a nonprincipal defect eigenvalue
`mu` for which `q-1-mu` already has a square root in `ℚ(mu)`.  At odd
dyadic degree this witness cannot be the incidence bottleneck's blind value
`mu=-1`: then `ℚ(mu)=ℚ`, and the certified root would make `q` a rational
square.
-/

open Polynomial SimpleGraph

namespace Erdos85

noncomputable section

/-- A square root of `q` lying in `ℚ(-1)=ℚ` makes `q` a rational square. -/
theorem isSquare_rat_of_root_mem_adjoin_neg_one
    (q : ℚ) (t : AlgebraicClosure ℚ)
    (htmem : t ∈ IntermediateField.adjoin ℚ
      {(-1 : AlgebraicClosure ℚ)})
    (htsq : t * t = (q : AlgebraicClosure ℚ)) :
    IsSquare q := by
  have hadjoin : IntermediateField.adjoin ℚ
      {(-1 : AlgebraicClosure ℚ)} = ⊥ := by
    simpa using (IntermediateField.adjoin_intCast
      (F := ℚ) (E := AlgebraicClosure ℚ) (-1))
  rw [hadjoin, IntermediateField.mem_bot] at htmem
  obtain ⟨u, rfl⟩ := htmem
  have hu : u * u = q :=
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by simpa using htsq)
  exact ⟨u, hu.symm⟩

/-- **Odd-dyadic nonblind designated orbit.**  Every positive regular
`C₄`-free graph at odd dyadic degree has a genuine nonprincipal designated
defect orbit away from `mu=-1`. -/
theorem exists_nonprincipal_nonblind_defectEigenvalue_with_square_of_oddDyadic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Nonempty V] (hfree : ¬ containsC4 V G)
    (q k : ℕ) (hq : 0 < q) (hqpow : q = 2 ^ k) (hk : Odd k)
    (hreg : ∀ x, G.degree x = q) :
    ∃ (μ : AlgebraicClosure ℚ) (v : V → AlgebraicClosure ℚ)
        (t : AlgebraicClosure ℚ),
      μ ≠ -1 ∧ v ≠ 0 ∧
      ((secondOrderDefectGraph G).adjMatrix
        (AlgebraicClosure ℚ)).mulVec v = μ • v ∧
      t ∈ IntermediateField.adjoin ℚ {μ} ∧
      t * t = (((q : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ) - μ := by
  obtain ⟨f, θ, μ, v, t, _hfirr, _hfmonic, _hfdvd, _hfasym,
      _hθroot, _hθne, hv0, _hvA, _hμ, hvD, htmem, htsq⟩ :=
    exists_nonprincipal_defectEigenvalue_with_square
      G hfree q hq hreg
  refine ⟨μ, v, t, ?_, hv0, hvD, htmem, htsq⟩
  intro hblind
  have htmem' : t ∈ IntermediateField.adjoin ℚ
      {(-1 : AlgebraicClosure ℚ)} := by
    simpa only [hblind] using htmem
  have hroot : t * t = (q : AlgebraicClosure ℚ) := by
    rw [hblind] at htsq
    simpa using htsq
  have hsq : IsSquare (q : ℚ) :=
    isSquare_rat_of_root_mem_adjoin_neg_one (q : ℚ) t htmem' hroot
  have hnonsquare : ¬ IsSquare (((2 ^ k : ℕ) : ℚ)) :=
    not_isSquare_twoPow_rat_of_odd k hk
  rw [hqpow] at hsq
  exact hnonsquare hsq

end


end Erdos85

#print axioms Erdos85.isSquare_rat_of_root_mem_adjoin_neg_one
#print axioms
  Erdos85.exists_nonprincipal_nonblind_defectEigenvalue_with_square_of_oddDyadic
