import Mathlib
import Proofs.CauchyInterlacingKeystone

/-
# Weyl's eigenvalue theorems from the Courant–Fischer keystone

This file derives the two classical **Weyl** spectral inequalities for symmetric
operators — *monotonicity* and the *subadditive (additive) inequality* — as pure
corollaries of the bound-form Courant–Fischer max–min keystone proved in
`CauchyInterlacingKeystone.lean` (#25063, 0-sorry/0-axiom). No new spectral
theory is introduced: every statement is obtained from the variational halves
`eigenvalue_maxmin_lower` / `eigenvalue_maxmin_upper` plus the eigenspan Rayleigh
bound `rayleigh_bounds_on_eigenspan` and the Grassmann dimension formula.

Throughout, an operator `T` is presented by its (orthonormal) eigenbasis `b` and
its descending eigenvalue enumeration `μ : Fin n → ℝ` (`Antitone μ`,
`T (b i) = μ i • b i`), matching the keystone's conventions. The eigenvalues of a
symmetric operator on `EuclideanSpace 𝕜 (Fin n)` always admit such a presentation
(spectral theorem); we take it as the input so the file stays purely variational.

## Results

* `rayleigh_le_on_upper_eigenspan` — on the eigenspan `span {b i, …, b (n-1)}`
  every nonzero Rayleigh quotient is `≤ μ i` (antitone `μ`). The reusable
  "upper-tail" companion to the keystone's lower half.

* `weyl_monotone` — **Weyl monotonicity.** If `⟪T x, x⟫ ≤ ⟪U x, x⟫` for all `x`
  (i.e. `T ⪯ U` in the Loewner order), then `μ k ≤ ν k` for every index `k`:
  the descending eigenvalues are monotone in the operator. Proof: feed the
  optimal `(k+1)`-dimensional subspace for `T` (lower half) into the upper half
  for `U`; the witness vector has `μ k ≤ R_T(x) ≤ R_U(x) ≤ ν k`.

* `weyl_add_le` — **Weyl's inequality.** For `i + j ≤ k`,
  `ρ k ≤ μ i + ν j` where `ρ` enumerates the eigenvalues of `T + U`. Proof:
  the optimal `(k+1)`-dimensional subspace for `T + U` (lower half) meets the two
  upper-tail eigenspans `span {b i,…}` and `span {c j,…}` (Grassmann count
  `(k+1) + (n-i) + (n-j) - 2n = k+1-i-j ≥ 1`); on a common nonzero vector
  `ρ k ≤ R_{T+U}(x) = R_T(x) + R_U(x) ≤ μ i + ν j`.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace

namespace CauchyInterlacing.Weyl

open CauchyInterlacing.Keystone

/-- **Grassmann lower bound for an intersection.** `finrank P + finrank Q ≤
finrank E + finrank (P ⊓ Q)`, i.e. `finrank (P ⊓ Q) ≥ finrank P + finrank Q −
finrank E`. Immediate from `finrank (P ⊔ Q) + finrank (P ⊓ Q) = finrank P +
finrank Q` and `finrank (P ⊔ Q) ≤ finrank E`. -/
theorem finrank_inf_lb
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] (P Q : Submodule 𝕜 E) :
    Module.finrank 𝕜 P + Module.finrank 𝕜 Q
      ≤ Module.finrank 𝕜 E + Module.finrank 𝕜 (P ⊓ Q : Submodule 𝕜 E) := by
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hle : Module.finrank 𝕜 (P ⊔ Q : Submodule 𝕜 E) ≤ Module.finrank 𝕜 E :=
    Submodule.finrank_le _
  omega

/-- **Upper-tail eigenspan bound.** For antitone `μ`, every nonzero vector in the
eigenspan `span {b i, …, b (n-1)}` (indices `≥ i`) has Rayleigh quotient `≤ μ i`.
This is the dual of the keystone's `rayleigh_ge_on_eigenspan_of_lb`: the supremum
of `μ` over `Finset.Ici i` is `μ i` because `μ` is antitone. -/
theorem rayleigh_le_on_upper_eigenspan
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ) (i : Fin n)
    (x : E)
    (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑(Finset.Ici i) : Set (Fin n))))
    (hx0 : x ≠ 0) :
    RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 ≤ μ i := by
  have hI : (Finset.Ici i).Nonempty := ⟨i, Finset.mem_Ici.2 le_rfl⟩
  have hbd := (rayleigh_bounds_on_eigenspan T b μ hb (Finset.Ici i) hI x hx hx0).2
  refine le_trans hbd ?_
  exact Finset.sup'_le hI μ (fun j hj => hμ (Finset.mem_Ici.1 hj))

/-! ## Weyl monotonicity -/

/-- **Weyl monotonicity theorem.** Let `T` and `U` be operators presented by
descending eigenvalue enumerations `μ` (basis `b`) and `ν` (basis `c`). If `T ⪯ U`
in the Loewner order — `re ⟪T x, x⟫ ≤ re ⟪U x, x⟫` for all `x` — then the
descending eigenvalues are pointwise monotone: `μ k ≤ ν k` for every `k`.

Proof. Take the optimal `(k+1)`-dimensional subspace `S` for `T` from the lower
keystone half (`μ k ≤ R_T(x)` on `S∖0`). The upper keystone half for `U` produces
`x ∈ S∖0` with `R_U(x) ≤ ν k`. Since `R_T(x) ≤ R_U(x)` (divide the hypothesis by
`‖x‖² > 0`), `μ k ≤ R_T(x) ≤ R_U(x) ≤ ν k`. -/
theorem weyl_monotone
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T U : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ)
    (c : OrthonormalBasis (Fin n) 𝕜 E) (ν : Fin n → ℝ)
    (hcU : ∀ i, U (c i) = (ν i : 𝕜) • c i) (hν : Antitone ν)
    (hle : ∀ x : E,
      RCLike.re (@inner 𝕜 E _ (T x) x) ≤ RCLike.re (@inner 𝕜 E _ (U x) x))
    (k : Fin n) :
    μ k ≤ ν k := by
  obtain ⟨S, hSdim, hSlb⟩ := eigenvalue_maxmin_lower T b μ hbT hμ k
  obtain ⟨x, hxS, hx0, hxub⟩ := eigenvalue_maxmin_upper U c ν hcU hν k S hSdim
  have hlb : μ k ≤ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 := hSlb x hxS hx0
  have hcinv : (0 : ℝ) ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  have hmid : RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2
      ≤ RCLike.re (@inner 𝕜 E _ (U x) x) / ‖x‖ ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hle x) hcinv
  exact le_trans hlb (le_trans hmid hxub)

/-! ## Weyl's additive inequality -/

/-- **Weyl's inequality** (subadditive form). Let `T`, `U`, and their sum `T + U`
be presented by descending eigenvalue enumerations `μ` (basis `b`), `ν`
(basis `c`), `ρ` (basis `d`). For any indices with `(i : ℕ) + (j : ℕ) ≤ (k : ℕ)`,
`ρ k ≤ μ i + ν j`.

This is the classical Weyl inequality `λ_{i+j+1}(A+B) ≤ λ_{i+1}(A) + λ_{j+1}(B)`
in 0-based descending form. Proof. Take the optimal `(k+1)`-dimensional subspace
`S` for `T + U` (lower half: `ρ k ≤ R_{T+U}` on `S∖0`). It meets the upper-tail
eigenspans `A = span {b i,…}` (dim `n-i`) and `B = span {c j,…}` (dim `n-j`): two
Grassmann counts give `finrank (S ⊓ A ⊓ B) ≥ (k+1) - i - j ≥ 1`. On a common
nonzero `x`: `R_T(x) ≤ μ i`, `R_U(x) ≤ ν j`, and `R_{T+U}(x) = R_T(x) + R_U(x)`,
so `ρ k ≤ R_{T+U}(x) ≤ μ i + ν j`. -/
theorem weyl_add_le
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T U : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ)
    (c : OrthonormalBasis (Fin n) 𝕜 E) (ν : Fin n → ℝ)
    (hcU : ∀ i, U (c i) = (ν i : 𝕜) • c i) (hν : Antitone ν)
    (d : OrthonormalBasis (Fin n) 𝕜 E) (ρ : Fin n → ℝ)
    (hdW : ∀ i, (T + U) (d i) = (ρ i : 𝕜) • d i) (hρ : Antitone ρ)
    (i j k : Fin n) (hk : (i : ℕ) + (j : ℕ) ≤ (k : ℕ)) :
    ρ k ≤ μ i + ν j := by
  have hEdim : Module.finrank 𝕜 E = n := by
    rw [Module.finrank_eq_card_basis d.toBasis, Fintype.card_fin]
  -- optimal (k+1)-dimensional subspace S for T + U (lower keystone half)
  obtain ⟨S, hSdim, hSlb⟩ := eigenvalue_maxmin_lower (T + U) d ρ hdW hρ k
  -- upper-tail eigenspans for T and U
  set A : Submodule 𝕜 E :=
    Submodule.span 𝕜 ((b : Fin n → E) '' (↑(Finset.Ici i) : Set (Fin n))) with hA
  set B : Submodule 𝕜 E :=
    Submodule.span 𝕜 ((c : Fin n → E) '' (↑(Finset.Ici j) : Set (Fin n))) with hB
  have hAdim : Module.finrank 𝕜 A = n - (i : ℕ) := by
    rw [hA, finrank_span_image_eq_card b (Finset.Ici i)]; simp [Fin.card_Ici]
  have hBdim : Module.finrank 𝕜 B = n - (j : ℕ) := by
    rw [hB, finrank_span_image_eq_card c (Finset.Ici j)]; simp [Fin.card_Ici]
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  -- Grassmann count 1: finrank (S ⊓ A) ≥ (k+1) - i
  have h1 := finrank_inf_lb S A
  rw [hSdim, hAdim, hEdim] at h1
  -- Grassmann count 2: finrank ((S ⊓ A) ⊓ B) ≥ 1
  have h2 := finrank_inf_lb (S ⊓ A) B
  rw [hBdim, hEdim] at h2
  have hpos : 0 < Module.finrank 𝕜 ((S ⊓ A) ⊓ B : Submodule 𝕜 E) := by omega
  have hne : ((S ⊓ A) ⊓ B : Submodule 𝕜 E) ≠ ⊥ := by
    intro hbot; rw [hbot] at hpos; simp at hpos
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  rw [Submodule.mem_inf, Submodule.mem_inf] at hxmem
  obtain ⟨⟨hxS, hxA⟩, hxB⟩ := hxmem
  -- the three Rayleigh facts
  have hTle : RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 ≤ μ i :=
    rayleigh_le_on_upper_eigenspan T b μ hbT hμ i x hxA hx0
  have hUle : RCLike.re (@inner 𝕜 E _ (U x) x) / ‖x‖ ^ 2 ≤ ν j :=
    rayleigh_le_on_upper_eigenspan U c ν hcU hν j x hxB hx0
  have hWlb : ρ k ≤ RCLike.re (@inner 𝕜 E _ ((T + U) x) x) / ‖x‖ ^ 2 :=
    hSlb x hxS hx0
  -- Rayleigh additivity for T + U
  have hadd : RCLike.re (@inner 𝕜 E _ ((T + U) x) x)
      = RCLike.re (@inner 𝕜 E _ (T x) x) + RCLike.re (@inner 𝕜 E _ (U x) x) := by
    rw [LinearMap.add_apply, inner_add_left, map_add]
  have hWeq : RCLike.re (@inner 𝕜 E _ ((T + U) x) x) / ‖x‖ ^ 2
      = RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2
        + RCLike.re (@inner 𝕜 E _ (U x) x) / ‖x‖ ^ 2 := by
    rw [hadd, add_div]
  calc ρ k ≤ RCLike.re (@inner 𝕜 E _ ((T + U) x) x) / ‖x‖ ^ 2 := hWlb
    _ = RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2
          + RCLike.re (@inner 𝕜 E _ (U x) x) / ‖x‖ ^ 2 := hWeq
    _ ≤ μ i + ν j := add_le_add hTle hUle

end CauchyInterlacing.Weyl
