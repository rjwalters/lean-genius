/-
Proof: Sharper Cayley — a group with a subgroup of index k embeds in Sₖ
Research: cayleys-theorem-oq-01-oq-01-oq-01

Open question (from `cayleys-theorem-oq-01-oq-01`): "Sharpen n: a group of order
n with a subgroup of index k embeds in S_k (the coset action), often far smaller
than S_n; formalize the minimal-degree faithful permutation representation."

Method: replace the *left-regular* representation `G →* Sym(G)` (degree n = |G|)
by the *coset action* `G →* Sym(G ⧸ H)` (degree k = [G : H]).  The kernel of the
coset action is the **normal core** `H.normalCore` (the largest normal subgroup
of G contained in H), so the action is faithful exactly when H is *core-free*.
In that case G embeds into `Sym(G ⧸ H)`, and transporting along a relabelling
`G ⧸ H ≃ Fin k` lands G inside the standard symmetric group `Sₖ`.

Since `k = [G : H] ≤ |G| = n` (with equality only for `H = ⊥`), this is the
degree-`n!`-to-`k!` improvement over the parent's finite Cayley embedding; taking
`H = ⊥` recovers the regular representation as the special case.
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-
# Sharper Cayley: the coset action `G →* Sym(G ⧸ H)`

The parent entry embeds a finite group `G` of order `n` into `Sₙ` via the
left-regular representation.  Here we sharpen the degree: for any subgroup
`H ≤ G` of index `k`, the action of `G` on the set of left cosets `G ⧸ H` gives
a homomorphism `cosetActionHom H : G →* Equiv.Perm (G ⧸ H)` into the symmetric
group on `k` points.

* Its kernel is `H.normalCore` (`cosetActionHom_ker`).
* Hence it is injective iff `H` is core-free (`cosetActionHom_injective_iff`),
  and then `G ↪ Sym(G ⧸ H)` (`exists_faithful_coset_rep`).
* In every case `G ⧸ H.normalCore` embeds into `Sym(G ⧸ H)`
  (`exists_quotient_faithful_rep`).
* Transporting along `G ⧸ H ≃ Fin k` gives a representation into the concrete
  `Sₖ = Equiv.Perm (Fin k)` (`exists_faithful_rep_on_fin`).
* The degree drops from `n` to `k = [G : H] ≤ n` (`index_le_card`), i.e. from a
  symmetric group of size `n!` to one of size `k!` (`card_perm_coset`).
* Taking `H = ⊥` recovers the classical Cayley embedding (`bot_core_free`).
-/

namespace CayleyCoset

open Equiv MulAction

variable {G : Type*} [Group G] (H : Subgroup G)

/-- Conjugation by a fixed bijection `e : α ≃ β`, packaged as a multiplicative
isomorphism `Equiv.Perm α ≃* Equiv.Perm β` (relabelling of permutations). -/
def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toEquiv := Equiv.permCongr e
  map_mul' x y := by
    ext b
    simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-- The **coset action homomorphism**: `G` acts on the left cosets `G ⧸ H` by
left multiplication, giving the permutation representation `G →* Sym(G ⧸ H)`. -/
def cosetActionHom : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)

@[simp] theorem cosetActionHom_apply (g : G) (q : G ⧸ H) :
    cosetActionHom H g q = g • q := rfl

/-- The kernel of the coset action is the **normal core** of `H`: the largest
normal subgroup of `G` contained in `H`. -/
theorem cosetActionHom_ker : (cosetActionHom H).ker = H.normalCore :=
  (Subgroup.normalCore_eq_ker H).symm

/-- The coset action is faithful (injective) exactly when `H` is **core-free**
(`H.normalCore = ⊥`). -/
theorem cosetActionHom_injective_iff :
    Function.Injective (cosetActionHom H) ↔ H.normalCore = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, cosetActionHom_ker]

/-- **Sharper Cayley (faithful form).** If `H` is core-free, then `G` embeds into
the symmetric group on its `[G : H]` cosets `G ⧸ H`. -/
theorem exists_faithful_coset_rep (hcore : H.normalCore = ⊥) :
    ∃ f : G →* Equiv.Perm (G ⧸ H), Function.Injective f :=
  ⟨cosetActionHom H, (cosetActionHom_injective_iff H).mpr hcore⟩

/-- The coset action always realises the quotient `G ⧸ H.normalCore` as a
subgroup of `Sym(G ⧸ H)`: the first isomorphism theorem identifies it with the
image of the coset action, regardless of whether `H` is core-free. -/
noncomputable def cosetQuotientEquivRange :
    G ⧸ H.normalCore ≃* (cosetActionHom H).range :=
  (QuotientGroup.quotientMulEquivOfEq (cosetActionHom_ker H).symm).trans
    (QuotientGroup.quotientKerEquivRange (cosetActionHom H))

/-- For an arbitrary subgroup `H`, the quotient `G ⧸ H.normalCore` embeds into
`Sym(G ⧸ H)`. -/
theorem exists_quotient_faithful_rep :
    ∃ f : G ⧸ H.normalCore →* Equiv.Perm (G ⧸ H), Function.Injective f :=
  ⟨(cosetActionHom H).range.subtype.comp (cosetQuotientEquivRange H).toMonoidHom,
    (cosetActionHom H).range.subtype_injective.comp
      (cosetQuotientEquivRange H).injective⟩

/-- The coset action transported into the **concrete** symmetric group
`Sₖ = Equiv.Perm (Fin k)` along a relabelling `e : G ⧸ H ≃ Fin k`. -/
def cosetActionFinHom {k : ℕ} (e : G ⧸ H ≃ Fin k) : G →* Equiv.Perm (Fin k) :=
  (permCongrMulEquiv e).toMonoidHom.comp (cosetActionHom H)

theorem cosetActionFinHom_injective {k : ℕ} (e : G ⧸ H ≃ Fin k)
    (hcore : H.normalCore = ⊥) : Function.Injective (cosetActionFinHom H e) := by
  have h := (cosetActionHom_injective_iff H).mpr hcore
  exact ((permCongrMulEquiv e).injective).comp h

/-- **Sharper Cayley (concrete form).** A group with a core-free subgroup of
index `k` embeds in the standard symmetric group `Sₖ = Equiv.Perm (Fin k)`. -/
theorem exists_faithful_rep_on_fin [Fintype (G ⧸ H)] {k : ℕ}
    (hk : Fintype.card (G ⧸ H) = k) (hcore : H.normalCore = ⊥) :
    ∃ f : G →* Equiv.Perm (Fin k), Function.Injective f := by
  subst hk
  exact ⟨cosetActionFinHom H (Fintype.equivFin _),
    cosetActionFinHom_injective H (Fintype.equivFin _) hcore⟩

/-- The degree of the coset representation is `[G : H] = |G ⧸ H|`. -/
theorem coset_degree_eq_index : H.index = Nat.card (G ⧸ H) :=
  H.index_eq_card

/-- The coset degree `k = [G : H]` never exceeds the order `n = |G|`: the
coset action sits inside `Sₖ` with `Sₖ ≤ Sₙ`. -/
theorem index_le_card [Finite G] : H.index ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos H.index_dvd_card

/-- Lagrange in degree form: `[G : H] = |G| / |H|`, so the coset degree is a
proper divisor of `n` whenever `H` is nontrivial — the source of the
`n! → k!` shrink in the size of the ambient symmetric group. -/
theorem index_mul_card_eq : H.index * Nat.card H = Nat.card G :=
  H.index_mul_card

/-- The ambient symmetric group of the coset representation has order `k!`
(versus `n!` for the regular representation). -/
theorem card_perm_coset [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)] :
    Fintype.card (Equiv.Perm (G ⧸ H)) = Nat.factorial (Fintype.card (G ⧸ H)) :=
  Fintype.card_perm

/-- The trivial subgroup is core-free, and its index is `|G|`; thus the parent's
classical Cayley embedding `G ↪ Sₙ` is exactly the `H = ⊥` special case of the
coset construction (`G ⧸ ⊥ ≃ G`). -/
theorem bot_core_free : (⊥ : Subgroup G).normalCore = ⊥ :=
  Subgroup.normalCore_eq_self ⊥

example : (⊥ : Subgroup G).index = Nat.card G := Subgroup.index_bot

/-- Worked instance: `S₃ = Equiv.Perm (Fin 3)` has a core-free subgroup of index
`3` (any point-stabiliser), so it embeds back into `S₃` — degree `3`, far below
the regular degree `|S₃| = 6` that Cayley's theorem would give.  We state the
abstract guarantee the construction provides for any such subgroup. -/
example (H : Subgroup (Equiv.Perm (Fin 3))) [Fintype (Equiv.Perm (Fin 3) ⧸ H)]
    (hk : Fintype.card (Equiv.Perm (Fin 3) ⧸ H) = 3) (hcore : H.normalCore = ⊥) :
    ∃ f : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3), Function.Injective f :=
  exists_faithful_rep_on_fin H hk hcore

end CayleyCoset
