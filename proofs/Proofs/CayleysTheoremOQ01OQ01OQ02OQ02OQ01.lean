/-
Proof: The holomorph decomposition of the normalizer of the left-regular
representation: `N_{Sym(G)}(L(G)) = L(G) · Aut(G)`, with the automorphisms
recovered exactly as the normalizing permutations that fix the identity.

Research: cayleys-theorem-oq-01-oq-01-oq-02-oq-02-oq-01

Open question (self-generated follow-up to `cayleys-theorem-oq-01-oq-01-oq-02-oq-02`):
  The parent file identifies the *centralizer* of the left-regular image `L(G)`
  inside `Equiv.Perm G` as the right-regular image `R(G)`, and remarks that this
  is "the structural fact underlying the holomorph of `G`".  The natural next
  structural object is the **normalizer** of `L(G)`: the holomorph
  `Hol(G) = N_{Sym(G)}(L(G))`.  Classical theory says `Hol(G) = L(G) ⋊ Aut(G)`,
  so that `N_{Sym(G)}(L(G)) / L(G) ≅ Aut(G)`.  This file proves the underlying
  set/subgroup identities over an *arbitrary* group `G` (no finiteness):

  * every automorphism normalizes `L(G)` and fixes `1`;
  * conversely a permutation that normalizes `L(G)` *and fixes `1`* is exactly an
    automorphism — so `Aut(G)` is realised precisely as the stabiliser of `1`
    inside the normalizer;
  * the full normalizer decomposes as `L(G) · Aut(G)`: every normalizing
    permutation is a left translation followed by (the permutation of) an
    automorphism.

The key computation is that an automorphism `φ` *intertwines* the left-regular
representation: `φ ∘ L_g = L_{φ g} ∘ φ`, i.e. `autPerm φ * leftReg g =
leftReg (φ g) * autPerm φ`.  Conjugating, `autPerm φ * leftReg g *
(autPerm φ)⁻¹ = leftReg (φ g)`, which shows `Aut(G)` permutes the generators of
`L(G)` and hence normalizes it.  The converse runs the classical "evaluate at
`1`" argument: a normalizing `σ` fixing `1` satisfies `σ (a*b) = σ a * σ b`,
so it *is* an automorphism.

Main results:

* `autPermHom`            : `MulAut G →* Equiv.Perm G`, the realisation of an
                            automorphism as a permutation of the underlying set,
                            with `autPermHom_injective` (the embedding `Aut(G) ↪
                            Sym(G)` of the holomorph).
* `autPerm_mem_normalizer`: every automorphism normalizes `L(G)`.
* `mem_normalizer_and_fixes_one_iff`:
    `σ ∈ N(L(G)) ∧ σ 1 = 1 ↔ ∃ φ : Aut(G), autPerm φ = σ`.
  Aut(G) is exactly the normalizer's stabiliser of the identity.
* `mem_normalizer_iff_exists`:
    `σ ∈ N(L(G)) ↔ ∃ (g : G) (φ : Aut(G)), σ = leftReg g * autPerm φ`.
  The holomorph decomposition `N(L(G)) = L(G) · Aut(G)`.
-/

import Mathlib

namespace Holomorph

variable {G : Type*} [Group G]

/-- The **left-regular representation** `g ↦ (x ↦ g * x)` as a group homomorphism
into the symmetric group on `G` (same construction as the parent file). -/
def leftReg (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := Equiv.mulLeft_one
  map_mul' := Equiv.mulLeft_mul

@[simp] theorem leftReg_apply (g x : G) : leftReg G g x = g * x := rfl

/-- The left-regular representation is faithful (Cayley's theorem). -/
theorem leftReg_injective : Function.Injective (leftReg G) := by
  intro a b hab
  have h := DFunLike.congr_fun hab 1
  rwa [leftReg_apply, leftReg_apply, mul_one, mul_one] at h

/-- The permutation of the underlying set `G` induced by an automorphism `φ`. -/
def autPerm (φ : MulAut G) : Equiv.Perm G := φ.toEquiv

@[simp] theorem autPerm_apply (φ : MulAut G) (x : G) : autPerm φ x = φ x := rfl

@[simp] theorem autPerm_symm_apply (φ : MulAut G) (x : G) :
    (autPerm φ)⁻¹ x = φ.symm x := rfl

/-- Realising an automorphism as a permutation is a group homomorphism
`MulAut G →* Equiv.Perm G`. -/
def autPermHom (G : Type*) [Group G] : MulAut G →* Equiv.Perm G where
  toFun := autPerm
  map_one' := by ext x; simp [autPerm_apply, MulAut.one_apply]
  map_mul' φ ψ := by ext x; simp [autPerm_apply, MulAut.mul_apply, Equiv.Perm.mul_apply]

@[simp] theorem autPermHom_apply (φ : MulAut G) : autPermHom G φ = autPerm φ := rfl

/-- The holomorph embedding `Aut(G) ↪ Sym(G)` is injective. -/
theorem autPermHom_injective : Function.Injective (autPermHom G) := by
  intro φ ψ h
  ext x
  have := DFunLike.congr_fun h x
  simpa [autPerm_apply] using this

/-- **Equivariance.**  An automorphism intertwines the left-regular
representation: `φ ∘ L_g = L_{φ g} ∘ φ`. -/
theorem autPerm_mul_leftReg (φ : MulAut G) (g : G) :
    autPerm φ * leftReg G g = leftReg G (φ g) * autPerm φ := by
  ext y
  simp [Equiv.Perm.mul_apply, leftReg_apply, autPerm_apply, map_mul]

/-- **Conjugation of generators.**  Conjugating a left translation by an
automorphism gives another left translation: `φ L_g φ⁻¹ = L_{φ g}`. -/
theorem autPerm_conj_leftReg (φ : MulAut G) (g : G) :
    autPerm φ * leftReg G g * (autPerm φ)⁻¹ = leftReg G (φ g) := by
  rw [autPerm_mul_leftReg, mul_assoc, mul_inv_cancel, mul_one]

/-- Every automorphism normalizes the left-regular image `L(G)`. -/
theorem autPerm_mem_normalizer (φ : MulAut G) :
    autPerm φ ∈ (leftReg G).range.normalizer := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, by rw [autPerm_conj_leftReg]⟩
  · intro hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨φ.symm b, ?_⟩
    have key : (autPerm φ)⁻¹ * leftReg G b * autPerm φ = h := by rw [hb]; group
    rw [← key]
    ext y
    simp [Equiv.Perm.mul_apply, leftReg_apply, autPerm_apply, autPerm_symm_apply,
      map_mul, MulEquiv.symm_apply_apply]

/-- An automorphism fixes the identity. -/
@[simp] theorem autPerm_one_eq (φ : MulAut G) : autPerm φ 1 = 1 := by
  simp [autPerm_apply]

/-- **Aut(G) as the stabiliser of `1` in the normalizer.**  A permutation of `G`
normalizes the left-regular image and fixes the identity **iff** it is the
permutation underlying an automorphism of `G`. -/
theorem mem_normalizer_and_fixes_one_iff (σ : Equiv.Perm G) :
    (σ ∈ (leftReg G).range.normalizer ∧ σ 1 = 1) ↔ ∃ φ : MulAut G, autPerm φ = σ := by
  constructor
  · rintro ⟨hN, h1⟩
    rw [Subgroup.mem_normalizer_iff] at hN
    -- The classical "evaluate at `1`" argument: `σ` is multiplicative.  From
    -- `σ L_a σ⁻¹ = L_c` we pass to the inverse-free form `L_c σ = σ L_a`, read
    -- off `c = σ a` at `1`, and read off `σ (a*b) = σ a * σ b` at `b`.
    have hmul : ∀ a b : G, σ (a * b) = σ a * σ b := by
      intro a b
      have hmemr : σ * leftReg G a * σ⁻¹ ∈ (leftReg G).range :=
        (hN (leftReg G a)).mp ⟨a, rfl⟩
      obtain ⟨c, hc⟩ := hmemr
      have hc' : leftReg G c * σ = σ * leftReg G a := by rw [hc]; group
      have hc1 := DFunLike.congr_fun hc' 1
      simp only [Equiv.Perm.mul_apply, leftReg_apply, h1, mul_one] at hc1
      have hcb := DFunLike.congr_fun hc' b
      simp only [Equiv.Perm.mul_apply, leftReg_apply] at hcb
      rw [hc1] at hcb
      exact hcb.symm
    -- Package `σ` as a monoid hom, then as an automorphism.
    let f : G →* G := { toFun := σ, map_one' := h1, map_mul' := hmul }
    refine ⟨MulEquiv.ofBijective f σ.bijective, ?_⟩
    ext x
    rfl
  · rintro ⟨φ, rfl⟩
    exact ⟨autPerm_mem_normalizer φ, autPerm_one_eq φ⟩

/-- **The holomorph decomposition.**  A permutation normalizes the left-regular
image **iff** it factors as a left translation composed with (the permutation of)
an automorphism: `N_{Sym(G)}(L(G)) = L(G) · Aut(G)`. -/
theorem mem_normalizer_iff_exists (σ : Equiv.Perm G) :
    σ ∈ (leftReg G).range.normalizer ↔
      ∃ (g : G) (φ : MulAut G), σ = leftReg G g * autPerm φ := by
  constructor
  · intro hN
    have hgN : leftReg G (σ 1) ∈ (leftReg G).range.normalizer :=
      Subgroup.le_normalizer ⟨σ 1, rfl⟩
    have hτN : (leftReg G (σ 1))⁻¹ * σ ∈ (leftReg G).range.normalizer :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hN
    have hτ1 : ((leftReg G (σ 1))⁻¹ * σ) 1 = 1 := by
      rw [Equiv.Perm.mul_apply, ← map_inv, leftReg_apply, inv_mul_cancel]
    obtain ⟨φ, hφ⟩ := (mem_normalizer_and_fixes_one_iff _).mp ⟨hτN, hτ1⟩
    refine ⟨σ 1, φ, ?_⟩
    rw [hφ, ← mul_assoc, mul_inv_cancel, one_mul]
  · rintro ⟨g, φ, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ⟨g, rfl⟩) (autPerm_mem_normalizer φ)

end Holomorph
