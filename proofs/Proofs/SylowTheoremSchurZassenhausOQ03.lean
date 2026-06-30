import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

/-!
# Sylow theorem OQ-03: The Schur–Zassenhaus splitting theorem and its Sylow corollary

The parent entry (`sylow-theorem`) lists as an explicit open question:

> *Can the Schur–Zassenhaus theorem (if `gcd(|H|, [G : H]) = 1` then `H` is complemented
> in `G`) be formalized as an extension of Sylow theory in this gallery?*

This file answers it. Mathlib proves the existence half of Schur–Zassenhaus
(`Subgroup.exists_right_complement'_of_coprime`); we package it in gallery form and,
crucially, derive the **Sylow extension** the question asks for:

> A **normal** Sylow `p`-subgroup is always complemented, and its complement is a
> Hall `p′`-subgroup (order coprime to `p`).

This is the bridge between Sylow theory and the theory of group extensions: whenever a
Sylow subgroup is normal, the group splits as an internal semidirect product
`G = P ⋊ K`.

## Main results

* `schurZassenhaus` : a normal subgroup of coprime order/index has a complement.
* `schurZassenhaus_structure` : the complement `K` satisfies `N ⊓ K = ⊥`, `N ⊔ K = ⊤`,
  and `|K| = [G : N]`.
* `complement_of_coprime_orders` : the order-factorization phrasing
  (`|N| = m`, `[G:N] = n`, `gcd(m,n)=1` ⟹ complement of order `n`).
* `normalSylow_isComplemented` : **a normal Sylow `p`-subgroup is complemented** (the
  Sylow extension).
* `normalSylow_complement_card` / `normalSylow_complement_not_dvd` /
  `normalSylow_complement_coprime` : the complement is a Hall `p′`-subgroup.
-/

namespace SylowTheoremSchurZassenhaus

open Subgroup

variable {G : Type*} [Group G]

/-- **Schur–Zassenhaus (existence).** A normal subgroup `N` whose order is coprime to
    its index `[G : N]` has a complement `K` (so the product `N × K → G` is a bijection).
    This is `Mathlib.GroupTheory.SchurZassenhaus`, restated in gallery form. -/
theorem schurZassenhaus {N : Subgroup G} [N.Normal]
    (h : Nat.Coprime (Nat.card N) N.index) :
    ∃ K : Subgroup G, IsComplement' N K :=
  Subgroup.exists_right_complement'_of_coprime h

/-- The complement of a coprime normal subgroup has order equal to the index `[G : N]`.
    Combined with `IsComplement'`, this exhibits `G` as an internal semidirect product. -/
theorem isComplement'_card_eq_index [Finite G] {N K : Subgroup G}
    (h : IsComplement' N K) : Nat.card K = N.index := by
  have hmul := h.card_mul                 -- Nat.card N * Nat.card K = Nat.card G
  have hidx := N.card_mul_index           -- Nat.card N * N.index = Nat.card G
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hcancel : Nat.card N * Nat.card K = Nat.card N * N.index := by rw [hmul, hidx]
  exact Nat.eq_of_mul_eq_mul_left hpos hcancel

/-- **Schur–Zassenhaus (structure).** A normal subgroup of coprime order/index has a
    complement `K` realizing an internal semidirect product: `N` and `K` are disjoint
    (`N ⊓ K = ⊥`), they generate `G` (`N ⊔ K = ⊤`), and `|K| = [G : N]`. -/
theorem schurZassenhaus_structure [Finite G] {N : Subgroup G} [N.Normal]
    (h : Nat.Coprime (Nat.card N) N.index) :
    ∃ K : Subgroup G, IsComplement' N K ∧ N ⊓ K = ⊥ ∧ N ⊔ K = ⊤ ∧ Nat.card K = N.index := by
  obtain ⟨K, hK⟩ := schurZassenhaus h
  refine ⟨K, hK, ?_, hK.sup_eq_top, isComplement'_card_eq_index hK⟩
  simpa [disjoint_iff] using hK.disjoint

/-- **Order-factorization phrasing.** If `|G| = m · n` is realized by a normal subgroup
    `N` of order `m` and index `n` with `gcd(m, n) = 1`, then `G` has a subgroup of
    order `n` complementing `N`. This is the classical "coprime order ⟹ splitting". -/
theorem complement_of_coprime_orders [Finite G] {N : Subgroup G} [N.Normal] {m n : ℕ}
    (hm : Nat.card N = m) (hn : N.index = n) (hmn : Nat.Coprime m n) :
    ∃ K : Subgroup G, IsComplement' N K ∧ Nat.card K = n := by
  obtain ⟨K, hK⟩ := schurZassenhaus (by rw [hm, hn]; exact hmn)
  exact ⟨K, hK, by rw [isComplement'_card_eq_index hK, hn]⟩

-- ============================================================
-- The Sylow extension: normal Sylow subgroups are complemented
-- ============================================================

variable {p : ℕ}

/-- **Sylow extension of Schur–Zassenhaus.** A *normal* Sylow `p`-subgroup is always
    complemented. Sylow `p`-subgroups are Hall subgroups (`Sylow.card_coprime_index`),
    so the coprimality hypothesis of Schur–Zassenhaus is automatic — the only extra
    input is normality. The complement `K` gives an internal semidirect product
    `G = P ⋊ K`. -/
theorem normalSylow_isComplemented [Finite G] [Fact p.Prime] (P : Sylow p G)
    [(P : Subgroup G).Normal] :
    ∃ K : Subgroup G, IsComplement' (P : Subgroup G) K :=
  schurZassenhaus P.card_coprime_index

/-- The complement of a normal Sylow `p`-subgroup has order equal to the index `[G : P]`. -/
theorem normalSylow_complement_card [Finite G] [Fact p.Prime] (P : Sylow p G)
    [(P : Subgroup G).Normal] {K : Subgroup G} (hK : IsComplement' (P : Subgroup G) K) :
    Nat.card K = (P : Subgroup G).index :=
  isComplement'_card_eq_index hK

/-- The complement of a normal Sylow `p`-subgroup is a **Hall `p′`-subgroup**: `p` does
    not divide its order. Thus normality of a Sylow subgroup forces the existence of a
    `p`-complement. -/
theorem normalSylow_complement_not_dvd [Finite G] [Fact p.Prime] (P : Sylow p G)
    [(P : Subgroup G).Normal] {K : Subgroup G} (hK : IsComplement' (P : Subgroup G) K) :
    ¬ p ∣ Nat.card K := by
  rw [normalSylow_complement_card P hK]
  exact P.not_dvd_index

/-- The complement's order is coprime to that of the Sylow subgroup. Together with
    `IsComplement'` this is exactly the statement that `G` is the internal semidirect
    product of the two coprime Hall subgroups `P` and `K`. -/
theorem normalSylow_complement_coprime [Finite G] [Fact p.Prime] (P : Sylow p G)
    [(P : Subgroup G).Normal] {K : Subgroup G} (hK : IsComplement' (P : Subgroup G) K) :
    Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card K) := by
  rw [normalSylow_complement_card P hK]
  exact P.card_coprime_index

end SylowTheoremSchurZassenhaus
