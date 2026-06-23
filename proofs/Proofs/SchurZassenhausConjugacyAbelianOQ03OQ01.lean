import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-!
# Schur–Zassenhaus, conjugacy half (abelian case)

The parent entry (`sylow-theorem-oq-03`, *Schur–Zassenhaus and the Splitting of Normal
Sylow Subgroups*) formalizes the **existence** half of the Schur–Zassenhaus theorem,
which Mathlib supplies as `Subgroup.exists_right_complement'_of_coprime`: a normal
subgroup `N ⊴ G` whose order is coprime to its index has a complement `K`
(`G = N ⋊ K`). Its first open question asks for the harder **conjugacy** half:

> *Formalize the conjugacy half of Schur–Zassenhaus: when `N` (or `G/N`) is solvable,
> all complements of `N` are conjugate.*

This file proves the **abelian base case**, which is the engine of the full solvable
result (the general case follows by induction along a chief/derived series, each step
of which is exactly the abelian case proved here):

> If `N ⊴ G` is **abelian**, finite, and has order coprime to its index, then any two
> complements of `N` are conjugate — indeed conjugate by an element of `N`.

Mathlib provides the abelian transfer machinery (`Subgroup.QuotientDiff`, the action
`MulAction G N.QuotientDiff`, and the transitivity lemma `Subgroup.exists_smul_eq`) but
does **not** state the conjugacy of complements; that is the new content here.

## Proof outline

* `complementTransversal` : a complement `K` of `N`, viewed as a set, is a left
  transversal of `N`, hence determines a point `α_K : N.QuotientDiff`.
* `le_stabilizer_complementTransversal` : `K ≤ stabilizer G α_K`. This is the only place
  where we use that `K` is a subgroup: right-translating the set `K` by one of its own
  elements leaves it invariant, so each `k ∈ K` fixes `α_K`.
* `stabilizer_complementTransversal_eq` : `stabilizer G α_K = K`. Mathlib's
  `isComplement'_stabilizer_of_coprime` shows `stabilizer G α_K` is *itself* a complement,
  so it has the same (finite) order as `K`; combined with the inclusion above this forces
  equality.
* `isComplement'_conj_of_isMulCommutative` : the main theorem. For two complements
  `K₁, K₂` the transitivity lemma `exists_smul_eq` gives `h ∈ N` with `h • α_{K₁} = α_{K₂}`,
  and `stabilizer_smul_eq_stabilizer_map_conj` turns this into
  `K₂ = stabilizer G α_{K₂} = (stabilizer G α_{K₁}) ^ h = K₁ ^ h`.

## Main results

* `SchurZassenhausConjugacy.stabilizer_complementPoint_eq`
* `SchurZassenhausConjugacy.isComplement'_conj_of_isMulCommutative`
* `SchurZassenhausConjugacy.exists_and_conj` — combined with Mathlib's existence half:
  a complement exists and all complements form a single `N`-conjugacy class.
-/

namespace SchurZassenhausConjugacy

open Subgroup MulAction MulOpposite Pointwise

variable {G : Type*} [Group G] {N : Subgroup G} {K K₁ K₂ : Subgroup G}

section Transversal

variable [N.Normal] [IsMulCommutative N] [N.FiniteIndex]

/-- A complement `K` of `N`, regarded as a subset of `G`, is a left transversal of `N`. -/
def complementTransversal (h : IsComplement' N K) : N.LeftTransversal :=
  ⟨(K : Set G), h.symm⟩

/-- The point of `N.QuotientDiff` determined by a complement `K`. -/
def complementPoint (h : IsComplement' N K) : N.QuotientDiff :=
  Quotient.mk'' (complementTransversal h)

/-- Right-translating the set `K` by one of its own elements leaves it invariant, so each
`k ∈ K` fixes the transversal `complementTransversal h`. This is the one step using that
`K` is a subgroup. -/
theorem le_stabilizer_complementPoint (h : IsComplement' N K) :
    K ≤ stabilizer G (complementPoint h) := by
  intro k hk
  rw [mem_stabilizer_iff]
  have hset : (op (k⁻¹) • (K : Set G)) = (K : Set G) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hop : (op (k⁻¹) : Gᵐᵒᵖ)⁻¹ = op k := by rw [← op_inv, inv_inv]
    rw [hop, op_smul_eq_mul, SetLike.mem_coe, SetLike.mem_coe]
    exact ⟨fun hx => by simpa using K.mul_mem hx (K.inv_mem hk),
      fun hx => K.mul_mem hx hk⟩
  -- `k • complementPoint h = Quotient.mk'' (op k⁻¹ • complementTransversal h)`
  show Quotient.mk'' (op (k⁻¹) • complementTransversal h) = complementPoint h
  exact congrArg Quotient.mk'' (Subtype.ext hset)

end Transversal

section Conjugacy

variable [Finite G] [N.Normal] [IsMulCommutative N]

/-- **Converse of the Schur–Zassenhaus construction.** Every complement of an abelian
normal subgroup of coprime order/index is the stabilizer of the corresponding point of
`N.QuotientDiff`. -/
theorem stabilizer_complementPoint_eq (hN : Nat.Coprime (Nat.card N) N.index)
    (h : IsComplement' N K) : stabilizer G (complementPoint h) = K := by
  haveI : N.FiniteIndex := inferInstance
  have hle : K ≤ stabilizer G (complementPoint h) := le_stabilizer_complementPoint h
  have hstab : IsComplement' N (stabilizer G (complementPoint h)) :=
    isComplement'_stabilizer_of_coprime hN
  have hstabcard : Nat.card (stabilizer G (complementPoint h)) = N.index := by
    simpa using IsComplement.card_right hstab
  have hKcard : Nat.card K = N.index := by
    simpa using IsComplement.card_right h
  have cardEq :
      Nat.card (stabilizer G (complementPoint h)) = Nat.card K := by
    rw [hstabcard, hKcard]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq cardEq)).symm

/-- **Conjugacy half of Schur–Zassenhaus, abelian case.** Any two complements of an
abelian normal subgroup `N` of coprime order/index are conjugate by an element of `N`. -/
theorem isComplement'_conj_of_isMulCommutative (hN : Nat.Coprime (Nat.card N) N.index)
    (h₁ : IsComplement' N K₁) (h₂ : IsComplement' N K₂) :
    ∃ g ∈ N, K₂ = K₁.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨h, hh⟩ := exists_smul_eq hN (complementPoint h₁) (complementPoint h₂)
  refine ⟨(h : G), h.2, ?_⟩
  have e₁ := stabilizer_complementPoint_eq hN h₁
  have e₂ := stabilizer_complementPoint_eq hN h₂
  calc
    K₂ = stabilizer G (complementPoint h₂) := e₂.symm
    _ = stabilizer G ((h : G) • complementPoint h₁) := by rw [← hh, Subgroup.smul_def]
    _ = (stabilizer G (complementPoint h₁)).map (MulAut.conj (h : G)).toMonoidHom :=
        stabilizer_smul_eq_stabilizer_map_conj _ _
    _ = K₁.map (MulAut.conj (h : G)).toMonoidHom := by rw [e₁]

/-- **Schur–Zassenhaus, abelian case, full form.** A complement of an abelian normal
subgroup of coprime order/index exists, and any complement is conjugate to it by an
element of `N`; hence the complements form a single `N`-conjugacy class. -/
theorem exists_and_conj (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ K₀ : Subgroup G, IsComplement' N K₀ ∧
      ∀ K : Subgroup G, IsComplement' N K →
        ∃ g ∈ N, K = K₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨K₀, hK₀⟩ := exists_right_complement'_of_coprime hN
  exact ⟨K₀, hK₀, fun K hK => isComplement'_conj_of_isMulCommutative hN hK₀ hK⟩

end Conjugacy

end SchurZassenhausConjugacy
