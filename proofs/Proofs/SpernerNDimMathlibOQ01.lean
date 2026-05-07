/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerNDimMathlib
import Proofs.SpernerNDimOQ01

/-!
# Concrete CellComplex Instances for Sperner's Lemma

Answers **OQ-01** from `sperner-ndim-mathlib`: which concrete structures instantiate
`SpernerAbstract.CellComplex` to recover the standard n-dimensional Sperner lemma?

## Part I: SpernerTriangulation → CellComplex Bridge (0 axioms, fully proved)

`SpernerNDim.SpernerTriangulation d N` (from `SpernerNDim.lean`) extends
`CellComplex (Vertex d N) d` with two boundary axioms (`adj_unique_facet`, `boundary_face`).
The bridge `toAbstractCellComplex` projects them away, and `SpernerAbstract.sperner` applies.
For Sperner colorings, both boundary conditions agree by `boundary_door_is_last_face`.

## Part II: Freudenthal CellComplex (4 axioms)

The Freudenthal triangulation of [0,1]^n gives `CellComplex (Finset (Fin n)) n`:
- **Simplex**: nodup lists of `Fin n` of length `n` (permutations)
- **Vertex k** of σ: `(σ.take k).toFinset` (prefix set of cardinality k)
- **Interior adjacency** (0 < k < n): swap positions k-1 and k in the permutation list
- **Boundary** (k = 0 or k = n): `none`

Four facts are axiomatized (each a ~40-line list-element argument):
1. `freud_simplex_fintype`: `FreudSimplex n` is Fintype (bijects with `Equiv.Perm (Fin n)`)
2. `swapAdj_nodup`: adjacent swap preserves `Nodup` (same multiset of elements)
3. `swapAdj_prefixSet_ne_pos_eq`: prefix sets agree at index ≠ k (key for `adj_vertices`)
4. `swapAdj_ne_self`: swapping adjacent distinct elements yields a different list

Proved: `adj_symm` (involution), `adj_vertices` (axiom 3), `adj_ne` (axiom 4),
`vertices_injective` (prefix cardinality), and the main `freudenthal_sperner` theorem.

## Tags

Sperner, CellComplex, Freudenthal triangulation, abstract triangulation, bridge
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace SpernerConcrete

open SpernerAbstract FreudenthalAdjacency Finset

-- ============================================================
-- PART I: SpernerTriangulation → CellComplex Bridge
-- ============================================================

section Bridge

variable {d N : ℕ}

/-- **Bridge**: every `SpernerTriangulation d N` gives a `CellComplex (Vertex d N) d`.
    Projects away the boundary-specific `adj_unique_facet` and `boundary_face` fields. -/
def toAbstractCellComplex (K : SpernerNDim.SpernerTriangulation d N) :
    CellComplex (SpernerNDim.Vertex d N) d where
  Simplex            := K.Simplex
  simplex_decidableEq := K.simplex_decidableEq
  simplex_fintype    := K.simplex_fintype
  vertices           := K.vertices
  vertices_injective := K.vertices_injective
  adj                := K.adj
  adj_symm           := K.adj_symm
  adj_vertices       := K.adj_vertices
  adj_ne             := K.adj_ne

theorem isFC_bridge (c : SpernerNDim.Coloring d N)
    (K : SpernerNDim.SpernerTriangulation d N) (s : K.Simplex) :
    SpernerNDim.IsFC c K s = SpernerAbstract.IsFC c (toAbstractCellComplex K) s := rfl

theorem isDoorAt_bridge (c : SpernerNDim.Coloring d N)
    (K : SpernerNDim.SpernerTriangulation d N) (s : K.Simplex) (k : Fin (d + 1)) :
    SpernerNDim.isDoorAt c K s k =
    SpernerAbstract.isDoorAt c (toAbstractCellComplex K) s k := rfl

/-- The abstract `SpernerAbstract.sperner` applies to every `SpernerTriangulation`. -/
theorem sperner_from_triangulation (c : SpernerNDim.Coloring d N)
    (K : SpernerNDim.SpernerTriangulation d N)
    (hbdry : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      SpernerAbstract.isDoorAt c (toAbstractCellComplex K) p.1 p.2 ∧
      K.adj p.1 p.2 = none)).card) :
    ∃ s : K.Simplex, SpernerAbstract.IsFC c (toAbstractCellComplex K) s :=
  SpernerAbstract.sperner c (toAbstractCellComplex K) hbdry

/-- For Sperner colorings, abstract boundary doors = concrete boundary doors (on face d). -/
theorem boundary_doors_agree (c : SpernerNDim.Coloring d N)
    (K : SpernerNDim.SpernerTriangulation d N) (hc : SpernerNDim.IsSperner c) :
    (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      SpernerAbstract.isDoorAt c (toAbstractCellComplex K) p.1 p.2 ∧
      K.adj p.1 p.2 = none)).card =
    (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      SpernerNDim.isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧
      p.2 = Fin.last d)).card := by
  congr 1; ext ⟨s, k⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isDoorAt_bridge]
  exact ⟨fun ⟨hd, hb⟩ => ⟨hd, hb, SpernerNDim.boundary_door_is_last_face c K hc s k hd hb⟩,
         fun ⟨hd, hb, _⟩ => ⟨hd, hb⟩⟩

end Bridge

-- ============================================================
-- PART II: Freudenthal CellComplex Instance
-- ============================================================

section FreudenthalInstance

variable {n : ℕ}

/-- Freudenthal simplices: nodup lists of `Fin n` of length `n`. -/
def FreudSimplex (n : ℕ) := {l : List (Fin n) // l.Nodup ∧ l.length = n}

instance : DecidableEq (FreudSimplex n) :=
  fun a b => decidable_of_iff (a.1 = b.1) Subtype.val_inj

/-- Adjacent transposition: swap positions k-1 and k. -/
def swapAdj (l : List (Fin n)) {k : ℕ} (hk0 : 0 < k) (hkn : k < l.length) : List (Fin n) :=
  (l.set (k - 1) (l.get ⟨k, hkn⟩)).set k (l.get ⟨k - 1, by omega⟩)

lemma swapAdj_length (l : List (Fin n)) {k : ℕ} (hk0 : 0 < k) (hkn : k < l.length) :
    (swapAdj l hk0 hkn).length = l.length := by simp [swapAdj, List.length_set]

/-- swapAdj applied twice is the identity.
    Proof: position k-1 gets l[k] in the first swap, then l[k] is swapped back to l[k-1];
    position k gets l[k-1] and is swapped back; all other positions are unchanged. -/
lemma swapAdj_invol (l : List (Fin n)) {k : ℕ} (hk0 : 0 < k) (hkn : k < l.length) :
    swapAdj (swapAdj l hk0 hkn) hk0 (swapAdj_length l hk0 hkn ▸ hkn) = l := by
  simp only [swapAdj]
  apply List.ext_getElem (by simp [List.length_set])
  intro i hi1 hi2
  simp only [List.length_set] at hi1
  simp only [List.getElem_set]
  by_cases hkm1 : i = k - 1 <;> by_cases hk' : i = k
  · omega
  · subst hkm1; simp [show k - 1 ≠ k from by omega]
  · subst hk'; simp [show k - 1 ≠ k from by omega]
  · simp [hk', hkm1]

-- ============================================================
-- Helpers
-- ============================================================

/-- swapAdj written as an explicit take-cons-cons-drop concatenation. -/
private lemma swapAdj_eq_split (l : List (Fin n)) {k : ℕ} (hk0 : 0 < k) (hkn : k < l.length) :
    swapAdj l hk0 hkn =
      l.take (k - 1) ++ l.get ⟨k, hkn⟩ :: l.get ⟨k - 1, by omega⟩ :: l.drop (k + 1) := by
  have hk1 : k - 1 < l.length := by omega
  have hkeq : k - 1 + 1 = k := by omega
  -- (l.set (k-1) l[k]) = take (k-1) ++ l[k] :: drop k
  have h1 : l.set (k - 1) (l.get ⟨k, hkn⟩) =
            l.take (k - 1) ++ l.get ⟨k, hkn⟩ :: l.drop k := by
    rw [List.set_eq_take_append_cons_drop, if_pos hk1, hkeq]
  show (l.set (k - 1) (l.get ⟨k, hkn⟩)).set k _ = _
  rw [h1]
  have hk1len : (l.take (k - 1)).length = k - 1 := by
    rw [List.length_take]; omega
  rw [List.set_append_right (h := by rw [hk1len]; omega), hk1len,
      show k - (k - 1) = 1 from by omega]
  show l.take (k - 1) ++ (l.get ⟨k, hkn⟩ :: l.drop k).set (0 + 1) _ = _
  rw [List.set_cons_succ]
  rw [show l.drop k = l.get ⟨k, hkn⟩ :: l.drop (k + 1) from
        (List.cons_get_drop_succ (l := l) (n := ⟨k, hkn⟩)).symm]
  rw [List.set_cons_zero]

/-- swapAdj produces a permutation of the original list. -/
private theorem swapAdj_perm (l : List (Fin n)) {k : ℕ} (hk0 : 0 < k) (hkn : k < l.length) :
    swapAdj l hk0 hkn ~ l := by
  have hk1 : k - 1 < l.length := by omega
  have hsucc : k - 1 + 1 = k := by omega
  rw [swapAdj_eq_split]
  -- Goal: l.take (k-1) ++ l[k] :: l[k-1] :: l.drop (k+1) ~ l
  conv_rhs => rw [← List.take_append_drop (k - 1) l]
  rw [show l.drop (k - 1) = l.get ⟨k - 1, hk1⟩ :: l.get ⟨k, hkn⟩ :: l.drop (k + 1) from ?_]
  · exact (List.Perm.swap _ _ _).append_left _
  · rw [show l.drop (k - 1) = l.get ⟨k - 1, hk1⟩ :: l.drop (k - 1 + 1) from
          (List.cons_get_drop_succ (l := l) (n := ⟨k - 1, hk1⟩)).symm]
    rw [hsucc, show l.drop k = l.get ⟨k, hkn⟩ :: l.drop (k + 1) from
        (List.cons_get_drop_succ (l := l) (n := ⟨k, hkn⟩)).symm]

-- ============================================================
-- Eliminated axioms (now theorems)
-- ============================================================

/-- swapAdj preserves Nodup (since it's a permutation). -/
private theorem swapAdj_nodup (l : List (Fin n)) {k : ℕ} (hl : l.Nodup)
    (hk0 : 0 < k) (hkn : k < l.length) : (swapAdj l hk0 hkn).Nodup :=
  (swapAdj_perm l hk0 hkn).nodup_iff.mpr hl

/-- Prefix sets are unchanged at index i ≠ k.
    For i ≤ k-1 the take is literally equal; for i ≥ k+1 it is a permutation. -/
private theorem swapAdj_prefixSet_eq (l : List (Fin n)) {k : ℕ} (hl : l.Nodup)
    (hl_len : l.length = n) {i : ℕ} (hi : i ≤ n) (hik : i ≠ k) (hk0 : 0 < k) (hkn : k < n) :
    prefixSet (swapAdj l hk0 (hl_len ▸ hkn)) i = prefixSet l i := by
  have hkn' : k < l.length := hl_len ▸ hkn
  have hi' : i ≤ l.length := hl_len ▸ hi
  unfold prefixSet
  apply List.toFinset_eq_of_perm
  rcases lt_or_gt_of_ne hik with hlt | hgt
  · -- i < k: take is literally equal
    have heq : (swapAdj l hk0 hkn').take i = l.take i := by
      show ((l.set (k - 1) (l.get ⟨k, hkn'⟩)).set k _).take i = _
      rw [List.take_set_of_le (by omega : i ≤ k)]
      rw [List.take_set_of_le (by omega : i ≤ k - 1)]
    exact heq ▸ List.Perm.refl _
  · -- i > k: split form + Perm.swap
    have hk1 : k - 1 < l.length := by omega
    have hsucc : k - 1 + 1 = k := by omega
    have hkp : k + 1 ≤ i := by omega
    have hk1le : k - 1 ≤ i := by omega
    -- LHS: (a ++ y :: x :: b).take i where a = take(k-1), b = drop(k+1), y = l[k], x = l[k-1]
    rw [swapAdj_eq_split l hk0 hkn']
    have hk1len : (l.take (k - 1)).length = k - 1 := by
      rw [List.length_take]; omega
    -- Split LHS via take_append + take_cons_succ twice
    rw [List.take_append, hk1len, List.take_of_length_le (by rw [hk1len]; omega)]
    rw [show i - (k - 1) = (i - (k + 1)) + 1 + 1 from by omega]
    rw [List.take_succ_cons, List.take_succ_cons]
    -- Split RHS similarly
    conv_rhs =>
      rw [show l = l.take (k - 1) ++ l.drop (k - 1) from (List.take_append_drop _ _).symm,
          show l.drop (k - 1) = l.get ⟨k - 1, hk1⟩ :: l.get ⟨k, hkn'⟩ :: l.drop (k + 1) from by
            rw [show l.drop (k - 1) = l.get ⟨k - 1, hk1⟩ :: l.drop (k - 1 + 1) from
                  (List.cons_get_drop_succ (l := l) (n := ⟨k - 1, hk1⟩)).symm]
            rw [hsucc, show l.drop k = l.get ⟨k, hkn'⟩ :: l.drop (k + 1) from
                (List.cons_get_drop_succ (l := l) (n := ⟨k, hkn'⟩)).symm]]
      rw [List.take_append, hk1len, List.take_of_length_le (by rw [hk1len]; omega),
          show i - (k - 1) = (i - (k + 1)) + 1 + 1 from by omega,
          List.take_succ_cons, List.take_succ_cons]
    -- Now both sides are: take(k-1) ++ y :: x :: rest  vs  take(k-1) ++ x :: y :: rest
    exact (List.Perm.swap _ _ _).append_left _

/-- swapAdj produces a different list (since k-1 ≠ k as positions in a Nodup list). -/
private theorem swapAdj_ne_self (l : List (Fin n)) {k : ℕ} (hl : l.Nodup)
    (hl_len : l.length = n) (hk0 : 0 < k) (hkn : k < n) :
    swapAdj l hk0 (hl_len ▸ hkn) ≠ l := by
  intro heq
  have hkn' : k < l.length := hl_len ▸ hkn
  have hk1 : k - 1 < l.length := by omega
  -- (swapAdj l)[k - 1] = l[k]
  have h1 : (swapAdj l hk0 hkn')[k - 1]'(by rw [swapAdj_length]; omega) = l[k] := by
    show ((l.set (k - 1) (l.get ⟨k, hkn'⟩)).set k _)[k - 1] = _
    rw [List.getElem_set_ne (by omega : k ≠ k - 1)]
    rw [List.getElem_set_self]
  -- transport via heq using getElem?
  have h_some : (swapAdj l hk0 hkn')[k - 1]? = some l[k] := by
    rw [List.getElem?_eq_getElem (by rw [swapAdj_length]; omega)]
    rw [h1]
  rw [heq] at h_some
  rw [List.getElem?_eq_getElem hk1] at h_some
  have h2 : l[k - 1] = l[k] := Option.some_inj.mp h_some
  have h3 := (List.Nodup.getElem_inj_iff hl (i := k - 1) (j := k) (hi := hk1) (hj := hkn')).mp h2
  omega

/-- The bijection from a nodup list of length n on Fin n to a permutation of Fin n. -/
private noncomputable def listToPermFun {n : ℕ} (l : List (Fin n)) (hl_nodup : l.Nodup)
    (hl_len : l.length = n) : Fin n → Fin n :=
  fun i => l.get ⟨i.val, hl_len ▸ i.isLt⟩

private theorem listToPermFun_injective {n : ℕ} (l : List (Fin n)) (hl_nodup : l.Nodup)
    (hl_len : l.length = n) : Function.Injective (listToPermFun l hl_nodup hl_len) := by
  intro a b hab
  apply Fin.ext
  have h2 : (⟨a.val, hl_len ▸ a.isLt⟩ : Fin l.length) = ⟨b.val, hl_len ▸ b.isLt⟩ :=
    (List.Nodup.get_inj_iff hl_nodup).mp hab
  exact Fin.val_eq_of_eq h2

private noncomputable def listToPerm {n : ℕ} (l : List (Fin n)) (hl_nodup : l.Nodup)
    (hl_len : l.length = n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (listToPermFun l hl_nodup hl_len)
    ⟨listToPermFun_injective l hl_nodup hl_len,
     Finite.injective_iff_surjective.mp (listToPermFun_injective l hl_nodup hl_len)⟩

/-- FreudSimplex n is Fintype: surjects from Equiv.Perm (Fin n) via permList. -/
private noncomputable instance freud_simplex_fintype (n : ℕ) : Fintype (FreudSimplex n) :=
  Fintype.ofSurjective
    (fun σ : Equiv.Perm (Fin n) =>
      (⟨FreudenthalAdjacency.permList σ, FreudenthalAdjacency.permList_nodup σ,
       FreudenthalAdjacency.permList_length σ⟩ : FreudSimplex n))
    (fun ⟨l, hnodup, hlen⟩ => by
      refine ⟨listToPerm l hnodup hlen, ?_⟩
      apply Subtype.ext
      show FreudenthalAdjacency.permList (listToPerm l hnodup hlen) = l
      unfold FreudenthalAdjacency.permList
      apply List.ext_getElem
      · simp [List.length_ofFn, hlen]
      intro i hi1 hi2
      rw [List.getElem_ofFn]
      show listToPermFun l hnodup hlen ⟨i, _⟩ = l[i]
      rfl)

-- ============================================================
-- CellComplex construction
-- ============================================================

variable (n)

/-- Freudenthal adjacency map. -/
private noncomputable def freudAdj (l : FreudSimplex n) (k : Fin (n + 1)) :
    Option (FreudSimplex n × Fin (n + 1)) :=
  if hk : 0 < k.val ∧ k.val < n then
    some ⟨⟨swapAdj l.1 hk.1 (l.2.2 ▸ hk.2),
           swapAdj_nodup l.1 l.2.1 hk.1 (l.2.2 ▸ hk.2),
           (swapAdj_length l.1 hk.1 (l.2.2 ▸ hk.2)).trans l.2.2⟩, k⟩
  else none

variable {n}

/-- Prefix sets have cardinality equal to their index, so the vertex map is injective. -/
private lemma prefixSet_inj (l : FreudSimplex n) :
    Function.Injective (fun k : Fin (n + 1) => prefixSet l.1 k.val) := fun a b hab => by
  apply Fin.ext
  have ha := prefixSet_card_eq l.2.1 (l.2.2 ▸ Nat.lt_succ_iff.mp a.isLt)
  have hb := prefixSet_card_eq l.2.1 (l.2.2 ▸ Nat.lt_succ_iff.mp b.isLt)
  linarith [congr_arg Finset.card hab]

/-- **Freudenthal CellComplex**: concrete `CellComplex (Finset (Fin n)) n`. -/
noncomputable def freudenthalCellComplex (n : ℕ) : CellComplex (Finset (Fin n)) n where
  Simplex := FreudSimplex n
  simplex_decidableEq := inferInstance
  simplex_fintype := freud_simplex_fintype n
  vertices := fun l k => prefixSet l.1 k.val
  vertices_injective := fun l => prefixSet_inj l
  adj := freudAdj n
  adj_symm := by
    intro l k l' k' h
    simp only [freudAdj] at h ⊢
    split_ifs at h with hk
    · obtain ⟨rfl, rfl⟩ := Option.some_inj.mp h
      simp only [dif_pos hk]
      congr 1; ext : 1
      exact swapAdj_invol l.1 hk.1 (l.2.2 ▸ hk.2)
    · exact absurd h (by simp)
  adj_vertices := by
    intro l k l' k' h
    simp only [freudAdj] at h
    split_ifs at h with hk
    · obtain ⟨rfl, rfl⟩ := Option.some_inj.mp h
      apply Finset.image_congr
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, true_and] at hj
      exact (swapAdj_prefixSet_eq l.1 l.2.1 l.2.2
        (Nat.lt_succ_iff.mp j.isLt) (fun h => hj (Fin.ext h)) hk.1 hk.2).symm
    · exact absurd h (by simp)
  adj_ne := by
    intro l k l' k' h
    simp only [freudAdj] at h
    split_ifs at h with hk
    · obtain ⟨rfl, rfl⟩ := Option.some_inj.mp h
      intro heq
      exact swapAdj_ne_self l.1 l.2.1 l.2.2 hk.1 hk.2
        (congr_arg Subtype.val heq).symm
    · exact absurd h (by simp)

/-- **Freudenthal Sperner's Lemma**: odd boundary doors imply a fully-colored simplex. -/
theorem freudenthal_sperner (n : ℕ) (c : Finset (Fin n) → Fin (n + 1))
    (hbdry : Odd (Finset.univ.filter (fun p : FreudSimplex n × Fin (n + 1) =>
      isDoorAt c (freudenthalCellComplex n) p.1 p.2 ∧
      (freudenthalCellComplex n).adj p.1 p.2 = none)).card) :
    ∃ s : FreudSimplex n, IsFC c (freudenthalCellComplex n) s :=
  sperner c (freudenthalCellComplex n) hbdry

end FreudenthalInstance

end SpernerConcrete
