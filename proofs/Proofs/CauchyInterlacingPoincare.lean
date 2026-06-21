import Mathlib
import Proofs.CauchyInterlacingKeystone

/-
# Poincaré separation — Cauchy interlacing for an arbitrary-codimension compression

`CauchyInterlacingAssembly.lean` (#27236, 0-sorry/0-axiom) proves the
**codimension-one** Cauchy interlacing inequality

  `lam (k.succ) ≤ mu k ≤ lam (k.castSucc)`

relating the descending eigenvalues `lam` of a symmetric operator `T` on a
space `V` of dimension `n+1` to the descending eigenvalues `mu` of a symmetric
operator `TH` on a codimension-one subspace `H` (the orthogonal compression of
`T` to `H`).

This file answers the parent entry's **second open question**: the general
"delete `m` rows/columns" interlacing — the **Poincaré separation theorem**.
For a codimension-`m` compression (`dim V = n + m`, `dim H = n`),

  `lam ⟨k + m⟩ ≤ mu k`   and   `mu k ≤ lam ⟨k⟩`     (for every `k : Fin n`),

i.e. in ascending textbook notation `λ_k ≤ μ_k ≤ λ_{k+m}`. The codimension-one
file is exactly the `m = 1` case.

## What makes this free

The variational content — the bound-form Courant–Fischer max–min
characterisation of the descending `k`-th eigenvalue — lives entirely in
`CauchyInterlacingKeystone.lean`, and that keystone is already stated for an
*arbitrary* subspace dimension (it is parametrised by index sets / `finrank S`,
not by a fixed `+1`). So Poincaré separation needs **no new spectral theory**:
only the dimension arithmetic changes. The codimension-one count
`dim (S ⊓ H) ≥ dim S − 1` becomes `dim (S ⊓ H) ≥ dim S − m`, and the optimal
subspace for the lower bound is taken `(k+m+1)`-dimensional instead of
`(k+2)`-dimensional. Both bounds reuse the identical keystone halves.

## Proof

* **Upper** `mu k ≤ lam ⟨k⟩`: identical to the codimension-one case — the
  optimal `(k+1)`-dim subspace `SH ⊆ H` for `TH` pushes into a `(k+1)`-dim
  subspace of `V`, on which the keystone's upper half finds a vector with
  `R_T ≤ lam ⟨k⟩`; Rayleigh-agreement transfers the `≥ mu k` lower bound. The
  codimension `m` never enters.
* **Lower** `lam ⟨k+m⟩ ≤ mu k`: take the optimal `(k+m+1)`-dim subspace `S` for
  `T` (keystone lower half at index `k+m`). The codimension-`m` count gives
  `dim (S ⊓ H) ≥ (k+m+1) + n − (n+m) = k+1`, enough for the index-set keystone
  half on `TH` to find a vector in `S ⊓ H` with `R_{TH} ≤ mu k`; that vector
  lies in `S`, so `lam ⟨k+m⟩ ≤ R_T = R_{TH} ≤ mu k`.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open CauchyInterlacing.Keystone

namespace CauchyInterlacing.Poincare

/-- **Poincaré separation theorem (abstract / compression form).**

Let `T` be a symmetric operator on an `(n + m)`-dimensional inner product space
`V` with orthonormal eigenbasis `b` and antitone (descending) eigenvalues `lam`.
Let `H ≤ V` have dimension `n` (codimension `m`), and let `TH` be a symmetric
operator on `H` with orthonormal eigenbasis `bH` and antitone eigenvalues `mu`,
whose Rayleigh quotient agrees with that of `T` on every nonzero `y ∈ H` (the
defining property of the orthogonal compression of `T` to `H`).

Then the eigenvalues separate: for every `k : Fin n`,

  `lam ⟨k + m⟩ ≤ mu k`   and   `mu k ≤ lam ⟨k⟩`.

In ascending textbook notation this is `λ_k ≤ μ_k ≤ λ_{k+m}`. The
codimension-one Cauchy interlacing theorem is the special case `m = 1`. -/
theorem poincare_separation
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] {n m : ℕ}
    (T : V →ₗ[𝕜] V) (b : OrthonormalBasis (Fin (n + m)) 𝕜 V) (lam : Fin (n + m) → ℝ)
    (hT : ∀ i, T (b i) = (lam i : 𝕜) • b i) (hlam : Antitone lam)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (TH : H →ₗ[𝕜] H) (bH : OrthonormalBasis (Fin n) 𝕜 H) (mu : Fin n → ℝ)
    (hTH : ∀ i, TH (bH i) = (mu i : 𝕜) • bH i) (hmu : Antitone mu)
    (hRayleigh : ∀ y : H, y ≠ 0 →
      RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2)
    (k : Fin n) :
    lam ⟨(k : ℕ) + m, by have := k.isLt; omega⟩ ≤ mu k
      ∧ mu k ≤ lam ⟨(k : ℕ), by have := k.isLt; omega⟩ := by
  have hVdim : Module.finrank 𝕜 V = n + m := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hk : (k : ℕ) < n := k.isLt
  refine ⟨?_, ?_⟩
  · -- LOWER bound: lam ⟨k + m⟩ ≤ mu k
    obtain ⟨S, hSdim, hSlb⟩ :=
      eigenvalue_maxmin_lower T b lam hT hlam ⟨(k : ℕ) + m, by omega⟩
    -- read off the subspace dimension as a plain ℕ equation
    have hSv : Module.finrank 𝕜 S = (k : ℕ) + m + 1 := hSdim
    -- the compression-side subspace: pull `S ⊓ H` back into `H`
    set SH : Submodule 𝕜 H := (S ⊓ H).comap H.subtype with hSHdef
    have hmap : SH.map H.subtype = S ⊓ H := by
      rw [hSHdef, Submodule.map_comap_subtype, inf_of_le_right inf_le_right]
    have hSHfr : Module.finrank 𝕜 SH = Module.finrank 𝕜 (S ⊓ H : Submodule 𝕜 V) := by
      rw [← hmap, Submodule.finrank_map_subtype_eq]
    -- dimension count: finrank (S ⊓ H) ≥ k + 1  (codimension-m version)
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq S H
    have hsuple : Module.finrank 𝕜 (S ⊔ H : Submodule 𝕜 V) ≤ n + m := by
      rw [← hVdim]; exact Submodule.finrank_le _
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
    calc lam ⟨(k : ℕ) + m, by omega⟩
        ≤ RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2 := hSlb (y : V) hyS hyv0
      _ = RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2 := (hRayleigh y hy0).symm
      _ ≤ mu k := hyle
  · -- UPPER bound: mu k ≤ lam ⟨k⟩  (codimension m never enters)
    obtain ⟨SH, hSHdim, hSHlb⟩ := eigenvalue_maxmin_lower TH bH mu hTH hmu k
    set S : Submodule 𝕜 V := SH.map H.subtype with hSdef
    have hSdim : Module.finrank 𝕜 S = (k : ℕ) + 1 := by
      rw [hSdef, Submodule.finrank_map_subtype_eq, hSHdim]
    obtain ⟨x, hxS, hx0, hxle⟩ :=
      eigenvalue_maxmin_upper T b lam hT hlam ⟨(k : ℕ), by omega⟩ S hSdim
    rw [hSdef, Submodule.mem_map] at hxS
    obtain ⟨y, hySH, hyx⟩ := hxS
    have hy0 : y ≠ 0 := fun h => hx0 (by rw [← hyx, h, map_zero])
    have hxv : x = (y : V) := by rw [← hyx]; rfl
    calc mu k
        ≤ RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2 := hSHlb y hySH hy0
      _ = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2 := hRayleigh y hy0
      _ = RCLike.re (@inner 𝕜 V _ (T x) x) / ‖x‖ ^ 2 := by rw [hxv]
      _ ≤ lam ⟨(k : ℕ), by omega⟩ := hxle

/-- **Cauchy interlacing (codimension one) as the `m = 1` special case.**

Recovering the parent entry's inequality `lam k.succ ≤ mu k ≤ lam k.castSucc`
from Poincaré separation, confirming the latter is a faithful generalisation:
`k.succ` and `⟨k+1⟩` agree, as do `k.castSucc` and `⟨k⟩`. -/
theorem cauchy_interlacing_of_poincare
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
  obtain ⟨hlo, hup⟩ :=
    poincare_separation T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh k
  refine ⟨?_, ?_⟩
  · -- `k.succ = ⟨k + 1⟩`
    have : k.succ = (⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ : Fin (n + 1)) := by
      apply Fin.ext; simp
    rw [this]; exact hlo
  · -- `k.castSucc = ⟨k⟩`
    have : k.castSucc = (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (n + 1)) := by
      apply Fin.ext; simp
    rw [this]; exact hup

end CauchyInterlacing.Poincare
