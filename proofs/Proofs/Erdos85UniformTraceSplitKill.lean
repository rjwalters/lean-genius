import Proofs.Erdos85UniformTraceSplitEngine

/-!
# The uniform trace-split kill

Assembly of the three-sector primary trace split against a hypothetical
`C₄`-free graph of even minimum degree `d` on the exact plateau boundary
`d(d-1)+3`.  When the conductor table at `c = d-1` has exactly one square
— the designated rational sector `μ₀` with `d - 1 - μ₀ = t²` and
`t ∤ d` — the graph forces `t ∣ d`, a contradiction.

The per-degree arithmetic input `harith` (every non-designated monic
irreducible factor of a boundary cycle polynomial evaluates to a
nonsquare at `d-1`) is discharged by the executable norm-certificate
chain in the degree-specific kill files.
-/

open Polynomial
open scoped Matrix

namespace Erdos85

open SimpleGraph

noncomputable section

set_option maxHeartbeats 1600000 in
/-- **The uniform trace-split kill.**  A single designated square sector
`μ₀` with `d - 1 - μ₀ = t²`, `t ∤ d` destroys the exact plateau boundary
at even degree `d`. -/
theorem uniform_trace_split_kill
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d t : ℕ} {μ0 : ℚ}
    (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3)
    (hμ0ne2 : μ0 ≠ 2) (ht : 0 < t)
    (hκμ : (d : ℚ) - 1 - μ0 = ((t * t : ℕ) : ℚ))
    (hnsq : ¬ IsSquare (d - 3))
    (hnd : ¬ t ∣ d)
    (harith : ∀ n : ℕ, 3 ≤ n → n ≤ d * (d - 1) + 3 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Polynomial.Chebyshev.C ℤ (n : ℤ) - 2).map (algebraMap ℤ ℚ) →
        f ≠ X - C μ0 → ¬ IsSquare (f.eval ((d : ℚ) - 1))) : False := by
  classical
  -- regularity at the exact boundary
  have hcardpos : 0 < Fintype.card V := by rw [hcard]; positivity
  haveI : Nonempty V := Fintype.card_pos_iff.mp hcardpos
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    calc Fintype.card V = d * (d - 1) + 3 := hcard
      _ < d * (d - 1) + (d - 1) + 1 := by omega
      _ = (d + 1) * (d - 1) + 1 := by ring
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by omega) hmin hbelow
  -- rational identity pack
  have hcommM := adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree hreg
  have hcommQ := toLin'_comm_of_matrix_comm hcommM
  have hcommR := adjMatrix_comm_secondOrderDefect_of_regular_real G hfree hreg
  have hsqM := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat G hfree hreg
  have hDreg2 : ∀ x, (secondOrderDefectGraph G).degree x = 2 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree (e := 0) hreg (by omega) x
    simpa using h
  have hJM := ratOnesMatrix_mul_adjMatrix_of_regular
    (secondOrderDefectGraph G) hDreg2
  -- endomorphism identities
  have hsqE : Matrix.toLin' (G.adjMatrix ℚ) * Matrix.toLin' (G.adjMatrix ℚ) =
      ((d : ℚ) - 1) • (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) +
        Matrix.toLin' (ratOnesMatrix V) -
        Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) := by
    apply LinearMap.ext
    intro v
    have hmat := congrArg (fun M : Matrix V V ℚ => M.mulVec v) hsqM
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hmat
    calc (Matrix.toLin' (G.adjMatrix ℚ) * Matrix.toLin' (G.adjMatrix ℚ)) v
        = (G.adjMatrix ℚ).mulVec ((G.adjMatrix ℚ).mulVec v) := by
          simp only [Module.End.mul_apply, Matrix.toLin'_apply]
      _ = (G.adjMatrix ℚ * G.adjMatrix ℚ).mulVec v :=
          Matrix.mulVec_mulVec v (G.adjMatrix ℚ) (G.adjMatrix ℚ)
      _ = ((d : ℚ) - 1) • v + (ratOnesMatrix V).mulVec v -
            ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec v := hmat
      _ = (((d : ℚ) - 1) • (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) +
            Matrix.toLin' (ratOnesMatrix V) -
            Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) v := by
          simp only [LinearMap.sub_apply, LinearMap.add_apply,
            LinearMap.smul_apply, Module.End.one_apply, Matrix.toLin'_apply]
  have hJTE : Matrix.toLin' (ratOnesMatrix V) *
      Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) =
      (2 : ℚ) • Matrix.toLin' (ratOnesMatrix V) := by
    apply LinearMap.ext
    intro v
    have hmat := congrArg (fun M : Matrix V V ℚ => M.mulVec v) hJM
    simp only [Matrix.smul_mulVec] at hmat
    calc (Matrix.toLin' (ratOnesMatrix V) *
        Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) v
        = (ratOnesMatrix V).mulVec
            (((secondOrderDefectGraph G).adjMatrix ℚ).mulVec v) := by
          simp only [Module.End.mul_apply, Matrix.toLin'_apply]
      _ = (ratOnesMatrix V *
            (secondOrderDefectGraph G).adjMatrix ℚ).mulVec v :=
          Matrix.mulVec_mulVec v _ _
      _ = ((2 : ℕ) : ℚ) • (ratOnesMatrix V).mulVec v := hmat
      _ = ((2 : ℚ) • Matrix.toLin' (ratOnesMatrix V)) v := by
          simp only [LinearMap.smul_apply, Matrix.toLin'_apply]
          norm_num
  -- sector factorization of the defect minimal polynomial
  have hDsymm : ((secondOrderDefectGraph G).adjMatrix ℚ).IsSymm :=
    SimpleGraph.isSymm_adjMatrix _
  obtain ⟨r, hr2, hrμ0, hrdvd, hpqr⟩ := exists_residual_factor hDsymm μ0
  have hcop_pq : IsCoprime (X - C (2 : ℚ)) (X - C μ0) := by
    rw [(irreducible_X_sub_C (2 : ℚ)).coprime_iff_not_dvd,
      Polynomial.dvd_iff_isRoot]
    intro hroot
    apply hμ0ne2
    have h20 : (2 : ℚ) - μ0 = 0 := by simpa using hroot
    linarith
  have hcop_pr : IsCoprime (X - C (2 : ℚ)) r := by
    rw [(irreducible_X_sub_C (2 : ℚ)).coprime_iff_not_dvd,
      Polynomial.dvd_iff_isRoot]
    exact hr2
  have hcop_qr : IsCoprime (X - C μ0) r := by
    rw [(irreducible_X_sub_C μ0).coprime_iff_not_dvd,
      Polynomial.dvd_iff_isRoot]
    exact hrμ0
  have hannM : Polynomial.aeval ((secondOrderDefectGraph G).adjMatrix ℚ)
      ((X - C 2) * (X - C μ0) * r) = 0 := by
    obtain ⟨s, hs⟩ := hpqr
    rw [hs, map_mul, minpoly.aeval, zero_mul]
  have hann : Polynomial.aeval
      (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
      ((X - C 2) * (X - C μ0) * r) = 0 := by
    rw [aeval_toLin', hannM, map_zero]
  -- total trace vanishes
  have htotal : LinearMap.trace ℚ (V → ℚ)
      (Matrix.toLin' (G.adjMatrix ℚ)) = 0 := by
    rw [trace_toLin'_eq_matrix_trace]
    exact adjMatrix_trace_rat_eq_zero G
  -- principal sector trace is d
  have hQtrace : (∑ c, componentQuotientMatrix G
      (secondOrderDefectGraph G) c c) = d := by
    have hns0 : ¬ IsSquare (d - 0 - 3) := by simpa using hnsq
    exact positiveExcess_componentQuotient_trace_eq_degree_of_nonsquare
      G hfree (e := 0) hd (Nat.zero_le _) hreg (by omega) hns0
  have hprincipal0 := trace_principal_kerAevalRestrict
    G (secondOrderDefectGraph G) hDreg2 hcommR hcommQ
  have hcast2 : ((2 : ℕ) : ℚ) = (2 : ℚ) := by norm_num
  rw [hcast2] at hprincipal0
  have hprincipal : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
        (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
        hcommQ (X - C (2 : ℚ))) = (d : ℚ) := by
    rw [hprincipal0, ← Nat.cast_sum, hQtrace]
  -- residual sector trace vanishes
  have harith' : ∀ n : ℕ, 3 ≤ n → n ≤ Fintype.card V →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Polynomial.Chebyshev.C ℤ (n : ℤ) - 2).map (algebraMap ℤ ℚ) →
        f ≠ X - C μ0 → ¬ IsSquare (f.eval ((d : ℚ) - 1)) := by
    intro n h3 hn
    rw [hcard] at hn
    exact harith n h3 hn
  have hresidual := residual_trace_eq_zero G hfree hd heven hmin hcard hreg
    harith' hcommQ hsqE hJTE hr2 hrμ0 hrdvd
  -- the unique square-sector terminal
  have hdvd : t ∣ d := dvd_of_unique_square_sector_trace_split
    (Matrix.toLin' (G.adjMatrix ℚ))
    (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
    (Matrix.toLin' (ratOnesMatrix V)) hcommQ (X - C 2) r
    hcop_pq hcop_pr hcop_qr hann hsqE hJTE hμ0ne2 ht hκμ
    hprincipal hresidual htotal
  exact hnd hdvd

end

end Erdos85
