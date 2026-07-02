import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Tactic

/-
# Graded Nakayama lemma via the irrelevant ideal

The parent entry `nakayama-lemma-oq-01` formalises the local-ring forms of
Nakayama's lemma: for a finitely generated module `M` over a local ring
`(R, 𝔪)`, `𝔪 M = M ⟹ M = 0`. Its second open question asks for the **graded**
analogue, where the irrelevant ideal `R₊ = ⨁_{i>0} Rᵢ` of an `ℕ`-graded ring
`R = ⨁_{i≥0} Rᵢ` plays the role of the maximal ideal:

> For an `ℕ`-graded ring `R` and an `ℕ`-graded `R`-module `M`, if `R₊ M = M`
> then `M = 0`.

## What makes the graded case free — and *stronger*

The local Nakayama lemma genuinely needs finite generation (its engine is the
determinant trick / Jacobson radical). The graded statement needs **no finite
generation at all**: it follows from a one-line degree argument.

Suppose `M ≠ 0`. Because `M = ⨁_{n} Mₙ` is `ℕ`-graded (hence bounded below by
degree `0`), the set of degrees carrying a nonzero homogeneous element is a
nonempty subset of `ℕ`, so it has a least element `d`. Pick `0 ≠ x ∈ M_d`. Since
`x ∈ M = R₊ M`, we may write `x = Σ rⱼ • mⱼ` with each `rⱼ ∈ R₊`. Every `rⱼ` has
zero degree-`0` component, so each `rⱼ • mⱼ` is a sum of products
`(rⱼ)_i • (mⱼ)_e` with `i ≥ 1`; such a product lives in `M_{i+e}`, and its
degree-`d` component is nonzero only if `i + e = d`, forcing `e = d - i < d`.
But `M_e = 0` for every `e < d` by minimality of `d`, so `(mⱼ)_e = 0`. Hence the
degree-`d` component of `x` vanishes — contradicting `0 ≠ x = x_d`.

So the "Jacobson-radical machinery" invoked for the local forms is *not*
required here: the grading itself, via the bottom nonzero degree, does all the
work. Concretely we only use the additive degree-`d` projection
`projM 𝓜 d : M →+ M`, the graded compatibility `Rᵢ • Mₑ ⊆ M_{i+e}`
(`SetLike.GradedSMul`), and `Nat.find` for the minimal degree.

## Formalisation notes

* `𝒜 : ℕ → σA` is an internally graded ring (`GradedRing 𝒜`) and `𝓜 : ℕ → σM`
  an internal graded module over it (`SetLike.GradedSMul 𝒜 𝓜` together with
  `DirectSum.Decomposition 𝓜`). The graded pieces `𝓜 n` are additive submonoids
  of `M` (not `R`-submodules) — the faithful model, in which degree shifting
  `Rᵢ • Mₑ ⊆ M_{i+e}` is nontrivial.
* The hypothesis `R₊ M = M` is `(HomogeneousIdeal.irrelevant 𝒜).toIdeal • ⊤ = ⊤`
  in `Submodule R M`.
* The conclusion `M = 0` is `Subsingleton M` (equivalently `⊤ = ⊥`).

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open DirectSum

namespace GradedNakayama

variable {R M σA σM : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [SetLike σA R] [AddSubmonoidClass σA R] (𝒜 : ℕ → σA) [GradedRing 𝒜]
variable [SetLike σM M] [AddSubmonoidClass σM M] (𝓜 : ℕ → σM)
variable [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]

/-- The degree-`i` projection of the graded module `M`, as an **additive**
homomorphism `M →+ M`. It is *not* `R`-linear: `R` acts by shifting degrees, so
projecting onto a fixed degree does not commute with the `R`-action. Modelled on
`GradedRing.proj`. -/
noncomputable def projM (i : ℕ) : M →+ M :=
  (AddSubmonoidClass.subtype (𝓜 i)).comp <|
    (DFinsupp.evalAddMonoidHom i).comp (DirectSum.decomposeAddEquiv 𝓜).toAddMonoidHom

@[simp]
theorem projM_apply (i : ℕ) (m : M) : projM 𝓜 i m = (decompose 𝓜 m i : M) := rfl

omit [AddSubmonoidClass σA R] [GradedRing 𝒜] in
/-- **Key vanishing lemma.** If every graded piece below degree `d` is trivial,
then for a homogeneous ring element `a ∈ 𝒜 i` of *positive* degree `i ≠ 0` and
any `n : M`, the degree-`d` component of `a • n` vanishes.

Reason: writing `n = Σ nₑ` in homogeneous pieces, `a • nₑ ∈ M_{i+e}`; its
degree-`d` component is nonzero only when `i + e = d`, i.e. `e = d - i < d`, and
then `nₑ = 0` by the hypothesis. -/
theorem projM_smul_deg {d : ℕ}
    (hmin : ∀ e, e < d → ∀ y ∈ 𝓜 e, y = 0)
    (a : R) (i : ℕ) (ha : a ∈ 𝒜 i) (hi : i ≠ 0) (n : M) :
    projM 𝓜 d (a • n) = 0 := by
  classical
  have hn : a • n = ∑ e ∈ (decompose 𝓜 n).support, a • (decompose 𝓜 n e : M) := by
    rw [← Finset.smul_sum, DirectSum.sum_support_decompose 𝓜 n]
  rw [hn, map_sum]
  apply Finset.sum_eq_zero
  intro e _
  have hmem : a • (decompose 𝓜 n e : M) ∈ 𝓜 (i + e) := by
    have h := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝓜) ha
      (SetLike.coe_mem (decompose 𝓜 n e))
    rwa [vadd_eq_add] at h
  rw [projM_apply]
  by_cases hd : i + e = d
  · have hlt : e < d := by omega
    have hze : (decompose 𝓜 n e : M) = 0 := hmin e hlt _ (SetLike.coe_mem _)
    rw [hze, smul_zero]
    simp
  · rw [decompose_of_mem_ne 𝓜 hmem hd]

include 𝓜 in
/-- **Graded Nakayama lemma.** For an `ℕ`-graded ring `𝒜` and an `ℕ`-graded
module `𝓜` over it, if the irrelevant ideal `𝒜₊` satisfies `𝒜₊ • M = M`, then
`M = 0`.

No finite-generation hypothesis is needed: the proof is a pure degree argument
using the least degree carrying a nonzero element. -/
theorem graded_nakayama
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal • (⊤ : Submodule R M) = ⊤) :
    Subsingleton M := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  classical
  -- The set of degrees carrying a nonzero homogeneous element is nonempty.
  have hDne : ∃ n : ℕ, ∃ y : M, y ∈ 𝓜 n ∧ y ≠ 0 := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    by_contra hcon
    have hcon' : ∀ n (y : M), y ∈ 𝓜 n → y = 0 := by
      intro n y hy
      by_contra hy0
      exact hcon ⟨n, y, hy, hy0⟩
    apply hm
    calc m = ∑ n ∈ (decompose 𝓜 m).support, (decompose 𝓜 m n : M) :=
            (DirectSum.sum_support_decompose 𝓜 m).symm
      _ = 0 := Finset.sum_eq_zero fun n _ => hcon' n _ (SetLike.coe_mem _)
  -- `d` is the least such degree; extract a nonzero homogeneous witness `x ∈ 𝓜 d`.
  set d := Nat.find hDne with hd_def
  obtain ⟨x, hxd, hx0⟩ := Nat.find_spec hDne
  have hmin : ∀ e, e < d → ∀ y ∈ 𝓜 e, y = 0 := by
    intro e he y hy
    by_contra hy0
    exact Nat.find_min hDne he ⟨y, hy, hy0⟩
  -- `x ∈ M = 𝒜₊ • M`.
  have hxmem : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal • (⊤ : Submodule R M) := by
    rw [h]; exact Submodule.mem_top
  -- The degree-`d` projection kills all of `𝒜₊ • M`.
  have key : projM 𝓜 d x = 0 := by
    refine Submodule.smul_induction_on hxmem ?_ ?_
    · intro r hr n _
      -- `r ∈ 𝒜₊` means its degree-`0` component is `0`.
      have hr0 : (decompose 𝒜 r 0 : R) = 0 := by
        have hmem0 := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 r).mp hr
        rwa [GradedRing.proj_apply] at hmem0
      rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [DFinsupp.mem_support_iff] at hi
        exact hi (ZeroMemClass.coe_eq_zero.mp hr0)
      exact projM_smul_deg 𝒜 𝓜 hmin (decompose 𝒜 r i : R) i
        (SetLike.coe_mem (decompose 𝒜 r i)) hi0 n
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  -- But the degree-`d` projection fixes the homogeneous `x`, so `x = 0`.
  rw [projM_apply, decompose_of_mem_same 𝓜 hxd] at key
  exact hx0 key

include 𝓜 in
/-- The submodule form: under the graded Nakayama hypothesis the whole module is
the zero submodule. -/
theorem graded_nakayama_top_eq_bot
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal • (⊤ : Submodule R M) = ⊤) :
    (⊤ : Submodule R M) = ⊥ := by
  haveI := graded_nakayama 𝒜 𝓜 h
  exact Subsingleton.elim _ _

end GradedNakayama
