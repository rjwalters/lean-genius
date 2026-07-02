import Mathlib
import Proofs.CauchyInterlacingPoincare

/-
# Poincaré separation, the literal principal-submatrix form

`CauchyInterlacingPoincare.lean` (#27247) proves the **abstract** Poincaré
separation theorem `poincare_separation`: for a symmetric operator `T` on an
`(n+m)`-dimensional inner product space `V` with descending eigenvalues `lam`,
and a subspace `H ≤ V` of dimension `n` carrying a symmetric operator `TH`
(descending eigenvalues `mu`) whose Rayleigh quotient agrees with `T`'s on `H`,
the eigenvalues separate as `lam ⟨k+m⟩ ≤ mu k ≤ lam ⟨k⟩`.

This file answers the parent entry's second open question: bridge that abstract
statement to the **literal matrix form**.  Let `A` be a Hermitian
`(n+m) × (n+m)` matrix and let `e : Fin n → Fin (n+m)` be an injective choice of
`n` retained coordinates (equivalently, delete the `m` complementary rows and
columns).  The **principal submatrix** `A.submatrix e e` is Hermitian, and its
eigenvalues `μ` interlace those `λ` of `A`:

  `λ ⟨k+m⟩ ≤ μ k`   and   `μ k ≤ λ ⟨k⟩`   for every `k : Fin n`.

## The bridge

We realise the matrix as the operator `T := toEuclideanLin A` on
`V := EuclideanSpace 𝕜 (Fin (n+m))`.  The retained coordinates span the subspace
`H := span {eₑ₍ⱼ₎}`.  There is a linear isometry
`L : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ H` sending the `j`-th standard basis vector to
the `(e j)`-th coordinate vector; it is the "zero-padding" embedding.  We push
the submatrix operator `Tsub := toEuclideanLin (A.submatrix e e)` through `L` to
get the compression operator `TH := L ∘ Tsub ∘ L⁻¹` on `H`, whose eigenvalues are
*by construction* the submatrix eigenvalues.

The only genuine computation is the **Rayleigh agreement**: for `y = L x ∈ H`,
the quadratic form of `A` on the zero-padded vector `↑y` equals the quadratic
form of `A.submatrix e e` on `x`.  This is `quad_form_submatrix` /
`quad_form_submatrix'`, an elementary `Finset`-sum identity: only the retained
coordinates carry mass, and the double sum collapses to
`∑ᵢⱼ conj(xᵢ) A₍ₑᵢ,ₑⱼ₎ xⱼ` on both sides.  Feeding this into `poincare_separation`
yields the matrix statement with no new spectral theory.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace Matrix
open Matrix WithLp CauchyInterlacing.Poincare

namespace CauchyInterlacing.PoincareSubmatrix

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-! ### The zero-padding embedding at the level of coordinate functions -/

/-- Zero-pad a length-`n` coordinate vector into a length-`(n+m)` one supported on
the image of `e`. -/
def pad (e : Fin n → Fin (n + m)) (xf : Fin n → 𝕜) : Fin (n + m) → 𝕜 :=
  fun p => ∑ j, if e j = p then xf j else 0

@[simp] lemma pad_apply_embed (e : Fin n → Fin (n + m)) (he : Function.Injective e)
    (xf : Fin n → 𝕜) (i : Fin n) : pad e xf (e i) = xf i := by
  unfold pad
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [he.ne hj]
  · simp

lemma mulVec_pad (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜) (e : Fin n → Fin (n + m))
    (xf : Fin n → 𝕜) (p : Fin (n + m)) :
    (A *ᵥ pad e xf) p = ∑ j, A p (e j) * xf j := by
  unfold pad Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (e j) (fun q => A p q * xf j)]
  simp

lemma star_pad_apply (e : Fin n → Fin (n + m)) (xf : Fin n → 𝕜) (p : Fin (n + m)) :
    (star (pad e xf) p : 𝕜) = ∑ i, if e i = p then star (xf i) else 0 := by
  simp only [Pi.star_apply, pad, star_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [apply_ite star, star_zero]

/-- **The key quadratic-form identity.** The quadratic form of `A` on a zero-padded
vector equals the quadratic form of the principal submatrix `A.submatrix e e` on
the original vector. -/
lemma quad_form_submatrix (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜)
    (e : Fin n → Fin (n + m)) (xf : Fin n → 𝕜) :
    star (pad e xf) ⬝ᵥ (A *ᵥ pad e xf) = star xf ⬝ᵥ (A.submatrix e e *ᵥ xf) := by
  have hLHS : star (pad e xf) ⬝ᵥ (A *ᵥ pad e xf)
      = ∑ i, ∑ j, star (xf i) * A (e i) (e j) * xf j := by
    rw [dotProduct]
    simp only [star_pad_apply, mulVec_pad]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single (e i)]
    · rw [if_pos rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    · intro p _ hp; rw [if_neg (Ne.symm hp)]; simp
    · simp
  have hRHS : star xf ⬝ᵥ (A.submatrix e e *ᵥ xf)
      = ∑ i, ∑ j, star (xf i) * A (e i) (e j) * xf j := by
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.star_apply, mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [submatrix_apply]; ring)
  rw [hLHS, hRHS]

/-- The conjugate-transposed variant, matching the `⟪T x, x⟫ = ofLp x ⬝ᵥ star (…)`
shape of `EuclideanSpace.inner_eq_star_dotProduct`. -/
lemma quad_form_submatrix' (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜)
    (e : Fin n → Fin (n + m)) (xf : Fin n → 𝕜) :
    pad e xf ⬝ᵥ star (A *ᵥ pad e xf) = xf ⬝ᵥ star (A.submatrix e e *ᵥ xf) := by
  have hLHS : pad e xf ⬝ᵥ star (A *ᵥ pad e xf)
      = ∑ i, ∑ j, xf i * star (A (e i) (e j)) * star (xf j) := by
    rw [dotProduct]
    simp only [Pi.star_apply, mulVec_pad, star_sum, star_mul', pad]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single (e i)]
    · rw [if_pos rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    · intro p _ hp; rw [if_neg (Ne.symm hp)]; simp
    · simp
  have hRHS : xf ⬝ᵥ star (A.submatrix e e *ᵥ xf)
      = ∑ i, ∑ j, xf i * star (A (e i) (e j)) * star (xf j) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.star_apply, mulVec, dotProduct, star_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [star_mul', submatrix_apply]; ring)
  rw [hLHS, hRHS]

/-- **Rayleigh agreement, matrix form.** The quadratic form of `A` on the zero-padded
Euclidean vector `toLp (pad e (ofLp x))` equals the quadratic form of the principal
submatrix on `x`.  Stated as an equality of inner products; it feeds the abstract
Poincaré separation's Rayleigh side condition. -/
lemma rayleigh_pad_eq (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜)
    (e : Fin n → Fin (n + m)) (x : EuclideanSpace 𝕜 (Fin n)) :
    (@inner 𝕜 (EuclideanSpace 𝕜 (Fin (n + m))) _
        ((toEuclideanLin A) (toLp 2 (pad e (ofLp x)))) (toLp 2 (pad e (ofLp x))))
      = @inner 𝕜 (EuclideanSpace 𝕜 (Fin n)) _ ((toEuclideanLin (A.submatrix e e)) x) x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    ofLp_toEuclideanLin_apply, ofLp_toEuclideanLin_apply, WithLp.ofLp_toLp]
  exact quad_form_submatrix' A e (ofLp x)

/-- Zero-padding preserves the dot product (it is the isometric coordinate embedding).
Injectivity of `e` is what forces the off-diagonal terms to cancel. -/
lemma pad_dot (e : Fin n → Fin (n + m)) (he : Function.Injective e) (u v : Fin n → 𝕜) :
    pad e v ⬝ᵥ star (pad e u) = v ⬝ᵥ star u := by
  rw [dotProduct]
  have hstep : (∑ p, pad e v p * star (pad e u) p)
      = ∑ j, v j * star (u j) := by
    simp only [star_pad_apply, pad]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single (e j)]
    · rw [if_pos rfl]
      rw [Finset.mul_sum, Finset.sum_eq_single j]
      · rw [if_pos rfl]
      · intro i _ hi; rw [if_neg (fun h => hi (he h))]; simp
      · simp
    · intro p _ hp; rw [if_neg (Ne.symm hp)]; simp
    · simp
  rw [hstep, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => by rw [Pi.star_apply])

/-- Zero-padding preserves the inner product: `⟪pad a, pad b⟫ = ⟪a, b⟫`.  This gives the
H-side numerator of the Rayleigh identity without invoking `inner_map_map` on `↥H` (which
trips the `Submodule.module` vs `InnerProductSpace.toNormedSpace.toModule` diamond). -/
lemma pad_preserves_inner (e : Fin n → Fin (n + m)) (he : Function.Injective e)
    (a b : EuclideanSpace 𝕜 (Fin n)) :
    (@inner 𝕜 (EuclideanSpace 𝕜 (Fin (n + m))) _
        (toLp 2 (pad e (ofLp a))) (toLp 2 (pad e (ofLp b))))
      = @inner 𝕜 (EuclideanSpace 𝕜 (Fin n)) _ a b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  exact pad_dot e he (ofLp a) (ofLp b)

/-! ### The matrix Poincaré separation theorem -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 4000000 in
/-- **Poincaré separation theorem — principal-submatrix form.**

Let `A` be a Hermitian `(n+m) × (n+m)` matrix over `𝕜`, with `T := toEuclideanLin A`
and descending eigenvalues `lam := hT.eigenvalues`.  Let `e : Fin n → Fin (n+m)`
be an injective choice of retained coordinates, so `A.submatrix e e` is the
principal submatrix obtained by deleting the `m` complementary rows and columns;
its descending eigenvalues are `mu := (toEuclideanLin (A.submatrix e e)).eigenvalues`.

Then for every `k : Fin n`,

  `lam ⟨k+m⟩ ≤ mu k`   and   `mu k ≤ lam ⟨k⟩`,

the Poincaré separation / Cauchy interlacing inequalities for a principal
submatrix. -/
theorem poincare_separation_submatrix
    (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜) (hA : A.IsHermitian)
    (e : Fin n → Fin (n + m)) (he : Function.Injective e) (k : Fin n) :
    (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin
        ⟨(k : ℕ) + m, by have := k.isLt; omega⟩
      ≤ (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix e)).eigenvalues
          finrank_euclideanSpace_fin k
    ∧ (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix e)).eigenvalues
          finrank_euclideanSpace_fin k
      ≤ (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin
          ⟨(k : ℕ), by have := k.isLt; omega⟩ := by
  classical
  -- Spectral data for `T := toEuclideanLin A` on `V := EuclideanSpace 𝕜 (Fin (n+m))`.
  have hT : (toEuclideanLin A).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hA
  have hb : ∀ i, (toEuclideanLin A) ((hT.eigenvectorBasis finrank_euclideanSpace_fin) i)
      = ((hT.eigenvalues finrank_euclideanSpace_fin i : ℝ) : 𝕜) •
        (hT.eigenvectorBasis finrank_euclideanSpace_fin) i :=
    hT.apply_eigenvectorBasis finrank_euclideanSpace_fin
  have hlam : Antitone (hT.eigenvalues finrank_euclideanSpace_fin) :=
    hT.eigenvalues_antitone finrank_euclideanSpace_fin
  -- Spectral data for `Tsub := toEuclideanLin (A.submatrix e e)`.
  have hTsub : (toEuclideanLin (A.submatrix e e)).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix e)
  have hbsub : ∀ i, (toEuclideanLin (A.submatrix e e))
      ((hTsub.eigenvectorBasis finrank_euclideanSpace_fin) i)
      = ((hTsub.eigenvalues finrank_euclideanSpace_fin i : ℝ) : 𝕜) •
        (hTsub.eigenvectorBasis finrank_euclideanSpace_fin) i :=
    hTsub.apply_eigenvectorBasis finrank_euclideanSpace_fin
  have hmu : Antitone (hTsub.eigenvalues finrank_euclideanSpace_fin) :=
    hTsub.eigenvalues_antitone finrank_euclideanSpace_fin
  -- The orthonormal frame spanning the coordinate subspace `H`.
  set f : Fin n → EuclideanSpace 𝕜 (Fin (n + m)) :=
    fun j => EuclideanSpace.single (e j) (1 : 𝕜) with hf_def
  have hf : Orthonormal 𝕜 f := EuclideanSpace.orthonormal_single.comp e he
  set H : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin (n + m))) := Submodule.span 𝕜 (Set.range f) with hH_def
  have hHdim : Module.finrank 𝕜 H = n :=
    (finrank_span_eq_card hf.linearIndependent).trans (Fintype.card_fin n)
  -- The corestricted frame is an orthonormal basis of `H`.
  set g : Fin n → H := fun j => ⟨f j, Submodule.subset_span (Set.mem_range_self j)⟩ with hg_def
  have hg_coe : ∀ j, (↑(g j) : EuclideanSpace 𝕜 (Fin (n + m))) = f j := fun _ => rfl
  have hg_on : Orthonormal 𝕜 g := orthonormal_span hf
  have hg_sp : ⊤ ≤ Submodule.span 𝕜 (Set.range g) :=
    (hg_on.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, hHdim])).ge
  set Lb : OrthonormalBasis (Fin n) 𝕜 H := OrthonormalBasis.mk hg_on hg_sp with hLb_def
  have hLb_apply : ∀ j, Lb j = g j := fun j => by rw [hLb_def, OrthonormalBasis.coe_mk]
  -- The zero-padding isometry `L : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ H`.
  set L : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] H := Lb.repr.symm with hL_def
  -- Coordinate description of `L`: `↑(L x)` is the zero-padding of `x`.
  have hL_ofLp : ∀ x : EuclideanSpace 𝕜 (Fin n),
      ofLp (↑(L x) : EuclideanSpace 𝕜 (Fin (n + m))) = pad e (ofLp x) := by
    intro x
    have hLx : (↑(L x) : EuclideanSpace 𝕜 (Fin (n + m))) = ∑ j, (x j) • f j := by
      rw [hL_def, ← Lb.sum_repr_symm x, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Submodule.coe_smul, hLb_apply, hg_coe]
    funext p
    rw [hLx, WithLp.ofLp_sum]
    simp only [hf_def, WithLp.ofLp_smul, EuclideanSpace.ofLp_single, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, pad]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases eq_or_ne (e j) p with h | h
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  -- The transported eigenbasis and compression operator on `H`.
  set bH : OrthonormalBasis (Fin n) 𝕜 H :=
    (hTsub.eigenvectorBasis finrank_euclideanSpace_fin).map L with hbH_def
  set TH : H →ₗ[𝕜] H := (L.toLinearEquiv.conj (toEuclideanLin (A.submatrix e e))) with hTH_def
  have hTHL : ∀ z, TH (L z) = L ((toEuclideanLin (A.submatrix e e)) z) := by
    intro z
    have hstep : TH (L z)
        = L ((toEuclideanLin (A.submatrix e e)) (L.symm (L z))) := by
      rw [hTH_def, LinearEquiv.conj_apply_apply]; rfl
    rw [hstep, L.symm_apply_apply]
  have hbH_eig : ∀ i, TH (bH i)
      = ((hTsub.eigenvalues finrank_euclideanSpace_fin i : ℝ) : 𝕜) • bH i := by
    intro i
    rw [hbH_def, OrthonormalBasis.map_apply, hTHL, hbsub i, map_smul]
  -- `L` as a zero-padding at the coordinate level.
  have hLpad : ∀ z : EuclideanSpace 𝕜 (Fin n),
      (↑(L z) : EuclideanSpace 𝕜 (Fin (n + m))) = toLp 2 (pad e (ofLp z)) :=
    fun z => by rw [← hL_ofLp z, WithLp.toLp_ofLp]
  -- Rayleigh agreement.  We convert the `↥H` inner product to the ambient one via
  -- `Submodule.coe_inner` (definitional), transport `TH` by `hTHL`, and zero-pad by `hLpad`;
  -- then both numerators land at `⟪A.submatrix e e • x, x⟫` (H-side by `pad_preserves_inner`,
  -- V-side by `rayleigh_pad_eq`) and both denominators at `‖pad x‖`.  This route sidesteps
  -- `inner_map_map` on `↥H`, whose `Submodule.module` vs `InnerProductSpace` diamond blocks
  -- unification.
  have hRayleigh : ∀ y : H, y ≠ 0 →
      RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 (EuclideanSpace 𝕜 (Fin (n + m))) _
            ((toEuclideanLin A) (y : EuclideanSpace 𝕜 (Fin (n + m)))) (y : EuclideanSpace 𝕜 (Fin (n + m)))) /
          ‖(y : EuclideanSpace 𝕜 (Fin (n + m)))‖ ^ 2 := by
    intro y _
    obtain ⟨x, rfl⟩ : ∃ x, y = L x := ⟨L.symm y, (L.apply_symm_apply y).symm⟩
    have hnc : ‖(↑(L x) : EuclideanSpace 𝕜 (Fin (n + m)))‖ = ‖L x‖ := rfl
    rw [Submodule.coe_inner, hTHL, ← hnc,
      hLpad ((toEuclideanLin (A.submatrix e e)) x), hLpad x,
      pad_preserves_inner e he, rayleigh_pad_eq A e x]
  -- Assemble via the abstract Poincaré separation theorem.
  exact poincare_separation (toEuclideanLin A) (hT.eigenvectorBasis finrank_euclideanSpace_fin)
    (hT.eigenvalues finrank_euclideanSpace_fin) hb hlam H hHdim TH bH
    (hTsub.eigenvalues finrank_euclideanSpace_fin) hbH_eig hmu hRayleigh k

end CauchyInterlacing.PoincareSubmatrix
