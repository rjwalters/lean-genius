import Mathlib
import Proofs.CauchyInterlacingKeystone

/-
# Cauchy interlacing — assembly from the Courant–Fischer keystone

`CauchyInterlacingKeystone.lean` (#25063, 0-sorry/0-axiom) proves the genuine
Mathlib gap: the bound-form Courant–Fischer max–min characterisation of the
descending k-th eigenvalue of a symmetric operator,

* `eigenvalue_maxmin_lower` — an optimal `(k+1)`-dim subspace on which every
  Rayleigh quotient is `≥ μ k` exists, and
* `eigenvalue_maxmin_upper` — on *every* `(k+1)`-dim subspace some nonzero
  vector has Rayleigh quotient `≤ μ k`,

plus the index-set-parametrised `exists_rayleigh_le_in_subspace`.

This file closes the **assembly**: from those two halves we derive the actual
interlacing inequalities

  `lam (k.succ) ≤ mu k ≤ lam (k.castSucc)`

relating the descending eigenvalues `lam : Fin (n+1) → ℝ` of a symmetric
operator `T` on a space `V` of dimension `n+1` to the descending eigenvalues
`mu : Fin n → ℝ` of a symmetric operator `TH` on a codimension-one subspace
`H ≤ V` (`finrank H = n`).

## The compression interface

The only thing connecting `TH` to `T` is the **Rayleigh-agreement** hypothesis

  `hRayleigh : ∀ y : H, y ≠ 0 → R_{TH}(y) = R_T(↑y)`,

which is exactly the property satisfied by the orthogonal *compression*
`TH = P_H ∘ T ∘ ι` of `T` to `H` (the principal-submatrix operator):
for `y ∈ H`, `⟪TH y, y⟫_H = ⟪P_H (T ↑y), ↑y⟫ = ⟪T ↑y, ↑y⟫` because `↑y ∈ H`,
and `‖y‖_H = ‖↑y‖_V`. Stating it as a hypothesis keeps this file purely
order-theoretic / dimension-counting and reusable: the spectral theorem on `H`
supplies `bH, mu, hTH`, and the compression supplies `hRayleigh`.

## Proof

* **Upper** `mu k ≤ lam k.castSucc`: take the optimal `(k+1)`-dim subspace
  `SH ⊆ H` for `TH` (lower half, `TH`); push it into `V`; the upper half for `T`
  finds a vector in it with `R_T ≤ lam k.castSucc`; Rayleigh-agreement turns the
  `≥ mu k` lower bound on `SH` into the same bound for that vector.
* **Lower** `lam k.succ ≤ mu k`: take the optimal `(k+2)`-dim subspace `S` for
  `T` (lower half, `T`); `S ⊓ H` has dimension `≥ k+1` (codimension-one count);
  pull it back into `H` and apply `exists_rayleigh_le_in_subspace` for `TH` to
  find a vector with `R_{TH} ≤ mu k`; that vector lies in `S`, so
  `lam k.succ ≤ R_T = R_{TH} ≤ mu k`.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open CauchyInterlacing.Keystone

namespace CauchyInterlacing.Assembly

/-- **Cauchy interlacing (abstract / compression form).**

Let `T` be a symmetric operator on a `(n+1)`-dimensional inner product space `V`
with orthonormal eigenbasis `b` and antitone (descending) eigenvalues `lam`.
Let `H ≤ V` have dimension `n`, and let `TH` be a symmetric operator on `H` with
orthonormal eigenbasis `bH` and antitone eigenvalues `mu`, whose Rayleigh
quotient agrees with that of `T` on every nonzero `y ∈ H` (the defining property
of the orthogonal compression of `T` to `H`).

Then the eigenvalues interlace: for every `k : Fin n`,

  `lam (k.succ) ≤ mu k`  and  `mu k ≤ lam (k.castSucc)`.

In ascending textbook notation this is `λ_k ≤ μ_k ≤ λ_{k+1}`. -/
theorem cauchy_interlacing
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] {n : ℕ}
    (T : V →ₗ[𝕜] V) (b : OrthonormalBasis (Fin (n + 1)) 𝕜 V) (lam : Fin (n + 1) → ℝ)
    (hT : ∀ i, T (b i) = (lam i : 𝕜) • b i) (hlam : Antitone lam)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (TH : H →ₗ[𝕜] H) (bH : OrthonormalBasis (Fin n) 𝕜 H) (mu : Fin n → ℝ)
    (hTH : ∀ i, TH (bH i) = (mu i : 𝕜) • bH i) (hmu : Antitone mu)
    (hRayleigh : ∀ y : H, y ≠ 0 →
      RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2)
    (k : Fin n) :
    lam k.succ ≤ mu k ∧ mu k ≤ lam k.castSucc := by
  have hVdim : Module.finrank 𝕜 V = n + 1 := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  refine ⟨?_, ?_⟩
  · -- LOWER bound: lam k.succ ≤ mu k
    obtain ⟨S, hSdim, hSlb⟩ := eigenvalue_maxmin_lower T b lam hT hlam k.succ
    -- the compression-side subspace: pull `S ⊓ H` back into `H`
    set SH : Submodule 𝕜 H := (S ⊓ H).comap H.subtype with hSHdef
    have hmap : SH.map H.subtype = S ⊓ H := by
      rw [hSHdef, Submodule.map_comap_subtype, inf_of_le_right inf_le_right]
    have hSHfr : Module.finrank 𝕜 SH = Module.finrank 𝕜 (S ⊓ H : Submodule 𝕜 V) := by
      rw [← hmap, Submodule.finrank_map_subtype_eq]
    -- dimension count: finrank (S ⊓ H) ≥ k + 1
    have hks : (k.succ : ℕ) = (k : ℕ) + 1 := Fin.val_succ k
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq S H
    have hsuple : Module.finrank 𝕜 (S ⊔ H : Submodule 𝕜 V) ≤ n + 1 := by
      rw [← hVdim]; exact Submodule.finrank_le _
    have hk : (k : ℕ) < n := k.isLt
    have hge : (k : ℕ) + 1 ≤ Module.finrank 𝕜 (S ⊓ H : Submodule 𝕜 V) := by
      rw [hHdim] at hsum; omega
    have hSHge : (k : ℕ) + 1 ≤ Module.finrank 𝕜 SH := by rw [hSHfr]; exact hge
    have hdim : Module.finrank 𝕜 H < Module.finrank 𝕜 SH + (Finset.Ici k).card := by
      rw [hHdim, Fin.card_Ici]; omega
    have hc : ∀ i ∈ Finset.Ici k, mu i ≤ mu k := fun i hi => hmu (Finset.mem_Ici.1 hi)
    obtain ⟨y, hySH, hy0, hyle⟩ :=
      exists_rayleigh_le_in_subspace TH bH mu hTH (Finset.Ici k) (mu k) hc SH hdim
    -- the witness, pushed to `V`, lies in `S`
    have hyHS : (y : V) ∈ S ⊓ H := by
      have h := Submodule.mem_comap.1 (hSHdef ▸ hySH)
      simpa using h
    have hyS : (y : V) ∈ S := (Submodule.mem_inf.1 hyHS).1
    have hyv0 : (y : V) ≠ 0 := fun h => hy0 (Submodule.coe_eq_zero.1 h)
    calc lam k.succ
        ≤ RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2 := hSlb (y : V) hyS hyv0
      _ = RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2 := (hRayleigh y hy0).symm
      _ ≤ mu k := hyle
  · -- UPPER bound: mu k ≤ lam k.castSucc
    obtain ⟨SH, hSHdim, hSHlb⟩ := eigenvalue_maxmin_lower TH bH mu hTH hmu k
    set S : Submodule 𝕜 V := SH.map H.subtype with hSdef
    have hSdim : Module.finrank 𝕜 S = (k.castSucc : ℕ) + 1 := by
      rw [hSdef, Submodule.finrank_map_subtype_eq, hSHdim, Fin.coe_castSucc]
    obtain ⟨x, hxS, hx0, hxle⟩ := eigenvalue_maxmin_upper T b lam hT hlam k.castSucc S hSdim
    rw [hSdef, Submodule.mem_map] at hxS
    obtain ⟨y, hySH, hyx⟩ := hxS
    have hy0 : y ≠ 0 := fun h => hx0 (by rw [← hyx, h, map_zero])
    have hxv : x = (y : V) := by rw [← hyx]; rfl
    calc mu k
        ≤ RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2 := hSHlb y hySH hy0
      _ = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2 := hRayleigh y hy0
      _ = RCLike.re (@inner 𝕜 V _ (T x) x) / ‖x‖ ^ 2 := by rw [hxv]
      _ ≤ lam k.castSucc := hxle

end CauchyInterlacing.Assembly
