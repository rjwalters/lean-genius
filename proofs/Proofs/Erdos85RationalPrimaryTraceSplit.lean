import Proofs.Erdos85UniqueSquareTraceTerminal
import Proofs.Erdos85ResidualTraceOrbit
import Proofs.CayleyHamiltonOQ01OQ04
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Rational primary trace split for a commuting pair

For commuting endomorphisms `S`, `T` of a finite-dimensional vector space,
every factorisation of an annihilating polynomial of `T` into pairwise
coprime factors splits the space into `S`-invariant primary sectors
`ker (gᵢ(T))`, and the trace of `S` is the sum of the sector traces.

This is the trace-decomposition bridge requested by the unique
square-sector terminal for the Erdős 85 defect spectrum: the total
adjacency trace equals the principal sector trace, plus the exceptional
rational square-sector trace, plus the residual trace.  The file also
packages:

* the square identity `(S|_{ker(T-μ)})² = (κ-μ)·id` on a linear sector,
  derived from the global identity `S² = κ·1 + J - T` and the column-sum
  relation `J·T = δ·J` with `μ ≠ δ`;
* more generally, the annihilation of every sector `ker (g(T))` with
  `g(δ) ≠ 0` by the all-ones operator `J`;
* the endomorphism form of the residual trace-to-orbit interface: a
  nonzero trace on an `S`-invariant sector yields an asymmetric
  irreducible factor of the restricted characteristic polynomial;
* the packaged terminal `t ∣ d` for a unique square sector, fed by the
  three-sector split.

The primary decomposition engine (`isInternal_ker_aeval`) is reused from
`CayleyHamiltonOQ01OQ04`; the per-sector traces are collected through
Mathlib's `LinearMap.trace_eq_sum_trace_restrict`.
-/

open Polynomial

namespace Erdos85

noncomputable section

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- An operator commuting with `T` commutes with every polynomial in `T`. -/
theorem commute_aeval_right (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (p : K[X]) : S * aeval T p = aeval T p * S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | monomial n a =>
      rw [aeval_monomial]
      have hST : Commute S T := hcomm
      have hSa : Commute S (algebraMap K (E →ₗ[K] E) a) :=
        (Algebra.commutes a S).symm
      exact hSa.mul_right (hST.pow_right n)

/-- Every primary sector `ker (p(T))` is invariant under any operator
commuting with `T`. -/
theorem mapsTo_ker_aeval_of_commute (S T : E →ₗ[K] E)
    (hcomm : S * T = T * S) (p : K[X]) :
    ∀ x ∈ LinearMap.ker (aeval T p), S x ∈ LinearMap.ker (aeval T p) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h := commute_aeval_right S T hcomm p
  calc aeval T p (S x) = ((aeval T p) * S) x := rfl
    _ = (S * aeval T p) x := by rw [h]
    _ = S (aeval T p x) := rfl
    _ = 0 := by rw [hx, map_zero]

/-- The restriction of `S` to the primary sector `ker (p(T))` of a
commuting operator `T`. -/
def kerAevalRestrict (S T : E →ₗ[K] E) (hcomm : S * T = T * S) (p : K[X]) :
    LinearMap.ker (aeval T p) →ₗ[K] LinearMap.ker (aeval T p) :=
  S.restrict (mapsTo_ker_aeval_of_commute S T hcomm p)

@[simp] theorem kerAevalRestrict_coe (S T : E →ₗ[K] E)
    (hcomm : S * T = T * S) (p : K[X]) (v : LinearMap.ker (aeval T p)) :
    (kerAevalRestrict S T hcomm p v : E) = S (v : E) := rfl

/-- Coprime sectors of a `T`-annihilating product are complementary. -/
theorem isCompl_ker_aeval_of_isCoprime (T : E →ₗ[K] E) {a b : K[X]}
    (hab : IsCoprime a b) (hann : aeval T (a * b) = 0) :
    IsCompl (LinearMap.ker (aeval T a)) (LinearMap.ker (aeval T b)) := by
  constructor
  · exact Polynomial.disjoint_ker_aeval_of_isCoprime T hab
  · rw [codisjoint_iff,
      Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hab, hann,
      LinearMap.ker_zero]

/-- **Primary trace split, general form.**  If `T` is annihilated by a
product of pairwise coprime polynomials, the trace of any commuting `S`
is the sum of its traces on the primary sectors `ker (gᵢ(T))`. -/
theorem trace_eq_sum_trace_restrict_ker_aeval [FiniteDimensional K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → K[X])
    (hpw : Pairwise fun i j => IsCoprime (g i) (g j))
    (hann : aeval T (∏ i, g i) = 0) :
    LinearMap.trace K E S =
      ∑ i, LinearMap.trace K (LinearMap.ker (aeval T (g i)))
        (kerAevalRestrict S T hcomm (g i)) := by
  have hint := CayleyHamiltonOQ01OQ04.isInternal_ker_aeval T g hpw hann
  rw [LinearMap.trace_eq_sum_trace_restrict hint
    (fun i => mapsTo_ker_aeval_of_commute S T hcomm (g i))]
  rfl

/-- Two-sector form of the primary trace split. -/
theorem trace_eq_add_trace_restrict_ker_aeval [FiniteDimensional K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S) {a b : K[X]}
    (hab : IsCoprime a b) (hann : aeval T (a * b) = 0) :
    LinearMap.trace K E S =
      LinearMap.trace K (LinearMap.ker (aeval T a))
          (kerAevalRestrict S T hcomm a) +
        LinearMap.trace K (LinearMap.ker (aeval T b))
          (kerAevalRestrict S T hcomm b) :=
  trace_eq_add_trace_restrict_of_isCompl S _ _
    (isCompl_ker_aeval_of_isCoprime T hab hann)
    (mapsTo_ker_aeval_of_commute S T hcomm a)
    (mapsTo_ker_aeval_of_commute S T hcomm b)

/-- The characteristic polynomial of `S` factors through two coprime
sectors of a commuting annihilated operator. -/
theorem charpoly_eq_mul_kerAevalRestrict [FiniteDimensional K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S) {a b : K[X]}
    (hab : IsCoprime a b) (hann : aeval T (a * b) = 0) :
    S.charpoly = (kerAevalRestrict S T hcomm a).charpoly *
      (kerAevalRestrict S T hcomm b).charpoly :=
  charpoly_eq_mul_restrict_of_isCompl S _ _
    (isCompl_ker_aeval_of_isCoprime T hab hann)
    (mapsTo_ker_aeval_of_commute S T hcomm a)
    (mapsTo_ker_aeval_of_commute S T hcomm b)

/-- **Three-sector trace split**: principal + exceptional + residual.
This is exactly the bookkeeping equation consumed by
`unique_square_sector_forces_dvd`. -/
theorem trace_eq_add_add_trace_restrict_ker_aeval [FiniteDimensional K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (p q r : K[X]) (hpq : IsCoprime p q) (hpr : IsCoprime p r)
    (hqr : IsCoprime q r) (hann : aeval T (p * q * r) = 0) :
    LinearMap.trace K E S =
      LinearMap.trace K (LinearMap.ker (aeval T p))
          (kerAevalRestrict S T hcomm p) +
        LinearMap.trace K (LinearMap.ker (aeval T q))
          (kerAevalRestrict S T hcomm q) +
          LinearMap.trace K (LinearMap.ker (aeval T r))
            (kerAevalRestrict S T hcomm r) := by
  have hpw : Pairwise fun i j : Fin 3 =>
      IsCoprime (![p, q, r] i) (![p, q, r] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact hpq
        | exact hpr
        | exact hqr
        | exact hpq.symm
        | exact hpr.symm
        | exact hqr.symm
  have hann' : aeval T (∏ i, ![p, q, r] i) = 0 := by
    rw [Fin.prod_univ_three]
    exact hann
  have h := trace_eq_sum_trace_restrict_ker_aeval S T hcomm
    ![p, q, r] hpw hann'
  rw [Fin.sum_univ_three] at h
  exact h

/-- Evaluation of a linear polynomial at an endomorphism. -/
theorem aeval_X_sub_C_eq (T : E →ₗ[K] E) (μ : K) :
    aeval T (X - C μ) = T - μ • (1 : E →ₗ[K] E) := by
  rw [map_sub, aeval_X, aeval_C, Module.algebraMap_end_eq_smul_id]
  rfl

/-- If `J·T = δ·J` and `g(δ) ≠ 0`, then `J` annihilates the sector
`ker (g(T))`: by Bezout every kernel vector lies in the range of
`T - δ·1`, which `J` kills. -/
theorem apply_eq_zero_of_mem_ker_aeval_of_eval_ne_zero
    (J T : E →ₗ[K] E) {δ : K} (hJT : J * T = δ • J)
    {g : K[X]} (hg : g.eval δ ≠ 0) :
    ∀ x ∈ LinearMap.ker (aeval T g), J x = 0 := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hJz : J * aeval T (X - C δ) = 0 := by
    rw [aeval_X_sub_C_eq T δ, mul_sub, hJT, mul_smul_comm, mul_one, sub_self]
  have hcop : IsCoprime (X - C δ) g := by
    rw [(irreducible_X_sub_C δ).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact hg
  obtain ⟨u, v, huv⟩ := hcop
  rw [mul_comm u (X - C δ)] at huv
  have happ := congrArg (fun q : K[X] => aeval T q x) huv
  simp only [map_add, map_mul, map_one, LinearMap.add_apply,
    Module.End.mul_apply, Module.End.one_apply] at happ
  rw [hx, map_zero, add_zero] at happ
  calc J x = J (aeval T (X - C δ) (aeval T u x)) := by rw [happ]
    _ = (J * aeval T (X - C δ)) (aeval T u x) := rfl
    _ = 0 := by rw [hJz]; rfl

/-- **Linear-sector square identity.**  On the sector `ker (T - μ·1)` of a
commuting pair with `S² = κ·1 + J - T` and `J·T = δ·J`, the restriction
of `S` squares to the scalar `κ - μ`, provided `μ ≠ δ`. -/
theorem kerAevalRestrict_X_sub_C_sq
    (S T J : E →ₗ[K] E) (hcomm : S * T = T * S) {κ δ μ : K}
    (hsq : S * S = κ • (1 : E →ₗ[K] E) + J - T)
    (hJT : J * T = δ • J) (hμ : μ ≠ δ) :
    kerAevalRestrict S T hcomm (X - C μ) *
        kerAevalRestrict S T hcomm (X - C μ) =
      (κ - μ) • LinearMap.id := by
  have hker : ∀ y : E, aeval T (X - C μ) y = 0 → T y = μ • y := by
    intro y hy
    rw [aeval_X_sub_C_eq T μ, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hy
    exact hy
  refine LinearMap.ext fun v => Subtype.ext ?_
  have hgδ : (X - C μ).eval δ ≠ 0 := by
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr (Ne.symm hμ)
  have hJv : J (v : E) = 0 :=
    apply_eq_zero_of_mem_ker_aeval_of_eval_ne_zero J T hJT hgδ (v : E) v.2
  have hTv : T (v : E) = μ • (v : E) := hker (v : E) v.2
  have hSS := LinearMap.congr_fun hsq (v : E)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply] at hSS
  rw [hJv, add_zero, hTv, ← sub_smul] at hSS
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    kerAevalRestrict_coe, SetLike.val_smul]
  exact hSS

/-- Endomorphism form of the residual trace-to-orbit interface: a nonzero
rational trace produces an asymmetric irreducible factor of the
characteristic polynomial. -/
theorem LinearMap.exists_asymmetric_charpoly_factor_of_trace_ne_zero
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (f : E →ₗ[ℚ] E) (htrace : LinearMap.trace ℚ E f ≠ 0) :
    ∃ q : ℚ[X], Irreducible q ∧ q.Monic ∧ q ∣ f.charpoly ∧
      Polynomial.signedReflection q ≠ q := by
  cases subsingleton_or_nontrivial E with
  | inl hE =>
      refine absurd ?_ htrace
      letI : Subsingleton E := hE
      rw [Subsingleton.elim f 0, map_zero]
  | inr hE =>
      letI : Nontrivial E := hE
      let b := Module.Free.chooseBasis ℚ E
      letI : Nonempty (Module.Free.ChooseBasisIndex ℚ E) :=
        Fintype.card_pos_iff.mp (by
          rw [← Module.finrank_eq_card_chooseBasisIndex]
          exact Module.finrank_pos)
      have hM : Matrix.trace (LinearMap.toMatrix b b f) ≠ 0 := by
        rw [← LinearMap.trace_eq_matrix_trace ℚ b]
        exact htrace
      obtain ⟨q, hqirr, hqmon, hqdvd, hqasym⟩ :=
        Matrix.exists_asymmetric_charpoly_factor_of_trace_ne_zero
          (LinearMap.toMatrix b b f) hM
      refine ⟨q, hqirr, hqmon, ?_, hqasym⟩
      rwa [LinearMap.charpoly_toMatrix f b] at hqdvd

/-- A nonzero residual sector trace produces an asymmetric irreducible
factor of the restricted characteristic polynomial.  This is the input
to the `AdjoinSquareConjugation` machinery for manufacturing a second
square-carrying defect orbit. -/
theorem exists_asymmetric_factor_of_kerAevalRestrict_trace_ne_zero
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S) (r : ℚ[X])
    (h : LinearMap.trace ℚ (LinearMap.ker (aeval T r))
      (kerAevalRestrict S T hcomm r) ≠ 0) :
    ∃ q : ℚ[X], Irreducible q ∧ q.Monic ∧
      q ∣ (kerAevalRestrict S T hcomm r).charpoly ∧
        Polynomial.signedReflection q ≠ q :=
  LinearMap.exists_asymmetric_charpoly_factor_of_trace_ne_zero _ h

/-- **Unique square-sector divisibility, fed by the primary trace
split.**  Suppose `T` is annihilated by `p·(X - μ)·r` with the three
factors pairwise coprime, the commuting operator `S` satisfies the
global quadratic identity `S² = κ·1 + J - T` with `J·T = δ·J` and
`μ ≠ δ`, and `κ - μ = t²`.  If the principal sector trace is `d`, the
residual sector trace vanishes, and the total trace of `S` is zero, then
`t ∣ d`. -/
theorem dvd_of_unique_square_sector_trace_split
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T J : E →ₗ[ℚ] E) (hcomm : S * T = T * S)
    (p r : ℚ[X]) {μ κ δ : ℚ}
    (hpq : IsCoprime p (X - C μ)) (hpr : IsCoprime p r)
    (hqr : IsCoprime (X - C μ) r)
    (hann : aeval T (p * (X - C μ) * r) = 0)
    (hsq : S * S = κ • (1 : E →ₗ[ℚ] E) + J - T)
    (hJT : J * T = δ • J) (hμ : μ ≠ δ)
    {d t : ℕ} (ht : 0 < t) (hκμ : κ - μ = ((t * t : ℕ) : ℚ))
    (hprincipal : LinearMap.trace ℚ (LinearMap.ker (aeval T p))
      (kerAevalRestrict S T hcomm p) = (d : ℚ))
    (hresidual : LinearMap.trace ℚ (LinearMap.ker (aeval T r))
      (kerAevalRestrict S T hcomm r) = 0)
    (htotal : LinearMap.trace ℚ E S = 0) :
    t ∣ d := by
  have hTsq := kerAevalRestrict_X_sub_C_sq S T J hcomm hsq hJT hμ
  rw [hκμ] at hTsq
  have hsplit := trace_eq_add_add_trace_restrict_ker_aeval S T hcomm
    p (X - C μ) r hpq hpr hqr hann
  exact unique_square_sector_forces_dvd
    (kerAevalRestrict S T hcomm (X - C μ)) ht hTsq _ _ _
    hprincipal hresidual htotal hsplit

end

end Erdos85
