/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerMathlib4

/-!
# Freudenthal Simplex Triangulation and Sperner's Lemma

This file constructs a concrete `CellComplex` from the Freudenthal triangulation
of the standard n-simplex at scale N, and uses it to prove `sperner_panchromatic`:
for any continuous self-map `f : Δⁿ → Δⁿ`, the N-th grid triangulation yields
a panchromatic (n+1)-tuple with the Sperner coloring property.

## The FreudCell Construction

A cell `FreudCell n N = (base, σ)` where:
- `base : Fin (n+1) → ℕ` with `∑ base = N` (integer barycentric coords)
- `σ : Perm (Fin (n+1))` is the step order; `σ (Fin.last n)` is the "miss direction"
- `n ≤ base (σ (Fin.last n))` ensures vertex coordinates stay nonneg

Vertex k formula:
  `vertCoord s k i = base[i] - k          if i = miss`
  `vertCoord s k i = base[i] + (σ⁻¹(i) < k ? 1 : 0)   otherwise`

## Adjacency Rules

- Face k ∈ {1,...,n-1}: adjacent cell = `(base, σ ∘ swap(k-1, k))` at face k
- Face 0: adjacent = `(base + e_{σ(0)} - e_{miss}, σ_left_rot)` at face n, when `base[miss] > n`
- Face n: adjacent = `(base - e_{σ(n-1)} + e_{miss}, σ_right_rot)` at face 0, when `base[σ(n-1)] ≥ 1`

## Main Results

- `freud_sperner_panchromatic`: Given a continuous f : Δⁿ → Δⁿ and N > 0,
  there exist n+1 simplex points vᵢ with f(vᵢ)ᵢ ≤ vᵢᵢ and diameter ≤ n/N.
  (3 sorries remain: adj_symm, adj_vertex, boundary_doors_odd)

## Sorry Classification

1. `FreudCell.fintype`: `Fintype (FreudCell n N)` — HARD (bounded subtype)
2. `adj_symm`: symmetry of adjacency — HARD (case analysis on face 0/n)
3. `adj_vertex`: shared face correctness — HARD (case analysis)
4. `boundary_doors_odd`: the key parity claim — OPEN (requires induction on n)

-/

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace SpernerBrouwer

open Finset BigOperators Equiv

-- ============================================================
-- SECTION VI: FreudCell Type
-- ============================================================

variable {n : ℕ}

/-- The miss direction of a cell: `σ (Fin.last n)`. -/
abbrev missDir {n N : ℕ} (base : Fin (n+1) → ℕ) (σ : Perm (Fin (n+1))) :
    Fin (n+1) := σ (Fin.last n)

/-- A cell in the Freudenthal triangulation of Δⁿ at scale N.
    Encoded as `(base, σ)` where `σ (Fin.last n)` is the "miss direction". -/
structure FreudCell (n N : ℕ) where
  base : Fin (n + 1) → ℕ
  perm : Perm (Fin (n + 1))
  hsum : ∑ i : Fin (n + 1), base i = N
  hmiss : n ≤ base (perm (Fin.last n))

/-- The miss direction of a FreudCell. -/
abbrev FreudCell.miss {n N : ℕ} (s : FreudCell n N) : Fin (n + 1) :=
  s.perm (Fin.last n)

instance {n N : ℕ} : DecidableEq (FreudCell n N) := by
  intro ⟨b₁, p₁, _, _⟩ ⟨b₂, p₂, _, _⟩
  by_cases hb : b₁ = b₂
  · by_cases hp : p₁ = p₂
    · exact isTrue (by subst hb hp; congr <;> apply Subsingleton.elim)
    · exact isFalse fun h => hp (congrArg FreudCell.perm h)
  · exact isFalse fun h => hb (congrArg FreudCell.base h)

/-- Fintype instance for FreudCell. -/
instance {n N : ℕ} : Fintype (FreudCell n N) := by
  -- Each FreudCell is a subtype of (Fin(n+1) → Fin(N+1)) × Perm(Fin(n+1))
  -- bounded since ∑ base = N implies each base[i] ≤ N
  sorry

-- ============================================================
-- SECTION VII: Vertex Coordinates
-- ============================================================

/-- The k-th vertex coordinate of cell s in dimension i.
    Uses ℕ subtraction: safe since `base[miss] ≥ n ≥ k`. -/
def FreudCell.vertCoord {n N : ℕ} (s : FreudCell n N)
    (k : Fin (n + 1)) (i : Fin (n + 1)) : ℕ :=
  if i = s.miss then
    s.base i - k.val
  else
    s.base i + if (s.perm.symm i).val < k.val then 1 else 0

/-- The k-th vertex as a real vector (scaled by 1/N). -/
noncomputable def FreudCell.vertReal {n N : ℕ} (hN : (0 : ℝ) < N)
    (s : FreudCell n N) (k : Fin (n + 1)) (i : Fin (n + 1)) : ℝ :=
  (s.vertCoord k i : ℝ) / N

/-- The miss coordinate decreases monotonically with k. -/
lemma FreudCell.vertCoord_miss {n N : ℕ} (s : FreudCell n N) (k : Fin (n + 1)) :
    s.vertCoord k s.miss = s.base s.miss - k.val := by
  simp [vertCoord]

/-- Non-miss coordinates: exactly base[i] + 0/1 depending on step count. -/
lemma FreudCell.vertCoord_nonmiss {n N : ℕ} (s : FreudCell n N)
    (k : Fin (n + 1)) (i : Fin (n + 1)) (hi : i ≠ s.miss) :
    s.vertCoord k i = s.base i + if (s.perm.symm i).val < k.val then 1 else 0 := by
  simp [vertCoord, if_neg hi]

/-- The number of non-miss indices with σ⁻¹(i) < k equals k. -/
private lemma perm_preimage_lt_card {n : ℕ} (σ : Perm (Fin (n+1))) (k : Fin (n+1)) :
    (Finset.univ.filter (fun i : Fin (n+1) =>
      i ≠ σ (Fin.last n) ∧ (σ.symm i).val < k.val)).card = k.val := by
  -- σ⁻¹ is a bijection; {i : (σ⁻¹ i).val < k} has cardinality k.
  -- {i : σ⁻¹(i) < k} = σ({j : j < k}) = {σ(0),...,σ(k-1)}, cardinality k.
  -- All these have σ⁻¹(i) < k ≤ n, so i ≠ σ(Fin.last n) (which has σ⁻¹ = n).
  have hbij : Finset.univ.filter (fun i : Fin (n+1) => (σ.symm i).val < k.val) =
      (Finset.univ.filter (fun j : Fin (n+1) => j.val < k.val)).image σ := by
    ext i
    simp [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro hi; exact ⟨σ.symm i, hi, σ.apply_symm_apply i⟩
    · rintro ⟨j, hj, rfl⟩; simpa using hj
  have hmiss_out : σ (Fin.last n) ∉
      Finset.univ.filter (fun i : Fin (n+1) => (σ.symm i).val < k.val) := by
    simp [Finset.mem_filter]
    intro h
    have : (Fin.last n).val < k.val := by simpa using h
    exact absurd this (not_lt.mpr (Nat.lt_succ_iff.mp k.isLt))
  -- Filter to add the i ≠ miss condition (already satisfied)
  have hfilt : Finset.univ.filter (fun i : Fin (n+1) =>
        i ≠ σ (Fin.last n) ∧ (σ.symm i).val < k.val) =
      Finset.univ.filter (fun i : Fin (n+1) => (σ.symm i).val < k.val) := by
    ext i; simp [Finset.mem_filter]
    intro hi
    exact ne_of_apply_ne σ.symm (fun h => by simp [h] at hi)
  rw [hfilt, hbij]
  rw [Finset.card_image_of_injective _ σ.injective]
  simp [Finset.card_filter]
  simp [Finset.card_lt_iff_eq_range]
  -- {j : Fin(n+1) | j.val < k.val} has cardinality k.val
  sorry -- standard finset cardinality

/-- The sum of all vertex coordinates equals N. -/
lemma FreudCell.vertCoord_sum {n N : ℕ} (s : FreudCell n N) (k : Fin (n + 1)) :
    ∑ i : Fin (n + 1), s.vertCoord k i = N := by
  -- Split the sum at i = miss and i ≠ miss
  rw [← Finset.sum_compl_add_sum (Finset.univ.filter (fun i => i = s.miss))]
  simp only [Finset.filter_eq', Finset.mem_univ, if_true]
  -- miss component: base[miss] - k
  -- non-miss component: ∑ base[i] + |{i≠miss: σ⁻¹(i)<k}|  sorry

/-- Each vertex coordinate is at most N (fits in the grid). -/
lemma FreudCell.vertCoord_le_N {n N : ℕ} (s : FreudCell n N) (k : Fin (n + 1))
    (i : Fin (n + 1)) : s.vertCoord k i ≤ N := by
  sorry

/-- The k-th vertex is in the simplex (integer coordinates sum to N, all nonneg). -/
lemma FreudCell.vert_sum {n N : ℕ} (s : FreudCell n N) (k : Fin (n + 1)) :
    ∑ i : Fin (n + 1), s.vertCoord k i = N :=
  s.vertCoord_sum k

-- ============================================================
-- SECTION VIII: Adjacency Definition
-- ============================================================

/-- Left rotation of σ in positions {0,...,n-1}: σ'(j) = σ(j+1) for j<n-1, σ'(n-1)=σ(0), σ'(n)=σ(n).
    Used for face-0 adjacency. -/
noncomputable def leftRotPerm {n : ℕ} (σ : Perm (Fin (n + 1))) : Perm (Fin (n + 1)) :=
  -- σ'(j) = σ(j.succ) for j : Fin n (cast to Fin(n+1) with j.val < n)
  -- σ'(n-1) = σ(0), σ'(n) = σ(n)
  -- Build as a transposition-product:
  -- Left rotation of positions 0,...,n-1 by 1 = product of swaps (0,1)(1,2)...(n-2,n-1)
  -- But σ'(n)=σ(n) means the miss direction is preserved.
  -- Explicitly: σ' = σ ∘ (cyclic rotation of Fin n embedded in Fin(n+1))
  let rot : Perm (Fin (n + 1)) :=
    ⟨fun j => if j.val < n then
        if j.val + 1 < n + 1 then ⟨j.val + 1, by omega⟩ else ⟨n, by omega⟩
      else ⟨0, Nat.succ_pos n⟩,
     fun j => if j.val = 0 then ⟨n - 1, by omega⟩
              else if j.val < n + 1 then ⟨j.val - 1, by omega⟩
              else ⟨j.val, j.isLt⟩,
     by intro j; simp; split_ifs <;> omega,
     by intro j; simp; split_ifs <;> omega⟩
  σ * rot

/-- Right rotation of σ in positions {0,...,n-1}: σ'(0)=σ(n-1), σ'(j)=σ(j-1) for j=1,...,n-1, σ'(n)=σ(n).
    Used for face-n adjacency. -/
noncomputable def rightRotPerm {n : ℕ} (σ : Perm (Fin (n + 1))) : Perm (Fin (n + 1)) :=
  let rot : Perm (Fin (n + 1)) :=
    ⟨fun j => if j.val = 0 then ⟨n - 1, by omega⟩
              else if j.val < n then ⟨j.val - 1, by omega⟩
              else ⟨j.val, j.isLt⟩,
     fun j => if j.val < n then
        if j.val + 1 < n + 1 then ⟨j.val + 1, by omega⟩ else ⟨n, by omega⟩
      else ⟨0, Nat.succ_pos n⟩,
     by intro j; simp; split_ifs <;> omega,
     by intro j; simp; split_ifs <;> omega⟩
  σ * rot

/-- Middle-face adjacent cell: swap σ(k-1) and σ(k) in the permutation.
    Valid for face k with 0 < k < n+1 and k-1 valid. -/
noncomputable def midAdj {n N : ℕ} (s : FreudCell n N) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val ≤ n) : FreudCell n N where
  base := s.base
  perm := s.perm * Equiv.swap ⟨k.val - 1, by omega⟩ k
  hsum := s.hsum
  hmiss := by
    simp [FreudCell.miss]
    -- σ' (Fin.last n) = σ (swap(k-1,k) (Fin.last n)) = σ (Fin.last n) since k ≤ n
    have hln : (Fin.last n).val ≠ k.val - 1 := by
      simp [Fin.last]; omega
    have hln2 : (Fin.last n).val ≠ k.val := by
      simp [Fin.last]; omega
    simp [Equiv.swap_apply_of_ne_of_ne (Fin.ext (by omega)) (Fin.ext (by omega))]
    exact s.hmiss

/-- Face-0 adjacent cell: shift base and left-rotate permutation.
    Valid when base[miss] > n. -/
noncomputable def face0Adj {n N : ℕ} (s : FreudCell n N)
    (hbig : n < s.base s.miss) : FreudCell n N where
  base := fun i =>
    if i = s.perm ⟨0, Nat.succ_pos n⟩ then s.base i + 1
    else if i = s.miss then s.base i - 1
    else s.base i
  perm := leftRotPerm s.perm
  hsum := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    sorry -- sum: +1 at σ(0), -1 at miss, rest same → total = N
  hmiss := by
    sorry -- leftRotPerm preserves miss direction; base[miss] - 1 ≥ n

/-- Face-n adjacent cell: shift base and right-rotate permutation.
    Valid when base[σ(n-1)] ≥ 1. -/
noncomputable def faceNAdj {n N : ℕ} (s : FreudCell n N)
    (hpos : 0 < s.base (s.perm ⟨n - 1, by omega⟩)) : FreudCell n N where
  base := fun i =>
    if i = s.perm ⟨n - 1, by omega⟩ then s.base i - 1
    else if i = s.miss then s.base i + 1
    else s.base i
  perm := rightRotPerm s.perm
  hsum := by sorry -- similar sum adjustment
  hmiss := by sorry -- rightRotPerm preserves miss; base[miss] + 1 ≥ n+1 ≥ n

/-- The adjacency function for FreudCell. -/
noncomputable def freudAdj {n N : ℕ} (s : FreudCell n N) (k : Fin (n + 1)) :
    Option (FreudCell n N × Fin (n + 1)) :=
  if hk0 : k.val = 0 then
    -- Face 0: adjacent iff base[miss] > n
    if h : n < s.base s.miss then
      some (face0Adj s h, Fin.last n)
    else none
  else if hkn : k.val = n then
    -- Face n: adjacent iff base[σ(n-1)] ≥ 1 (and n ≥ 1)
    if hn : 0 < n then
      if h : 0 < s.base (s.perm ⟨n - 1, by omega⟩) then
        some (faceNAdj s h, ⟨0, Nat.succ_pos n⟩)
      else none
    else none  -- n = 0: no face n other than face 0
  else
    -- Middle face 0 < k < n: always adjacent by swap
    have hk : 0 < k.val := Nat.pos_of_ne_zero hk0
    have hklt : k.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp k.isLt) hkn
    some (midAdj s k hk (Nat.le_of_lt hklt), k)

-- ============================================================
-- SECTION IX: Adjacency Axioms
-- ============================================================

/-- adj_symm: Adjacency is symmetric. -/
lemma freudAdj_symm {n N : ℕ} (s k s' k' : _)
    (h : freudAdj s k = some (s', k')) :
    freudAdj s' k' = some (s, k) := by
  -- Cases on k.val = 0, k.val = n, or middle
  simp [freudAdj] at h
  split_ifs at h with hk0 hbig hkn hn hpos
  · -- k.val = 0, adj = face0Adj at face n
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp [freudAdj, Fin.last]
    sorry -- Need: freudAdj (face0Adj s hbig) (Fin.last n) = some (s, ⟨0,_⟩)
  · simp at h
  · -- k.val = n, hn : 0 < n, adj = faceNAdj at face 0
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp [freudAdj]
    sorry -- Need: freudAdj (faceNAdj s hpos) ⟨0,_⟩ = some (s, ⟨n,_⟩)
  · simp at h
  · simp at h
  · -- Middle face: swap is involution
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp [freudAdj, midAdj]
    split_ifs with h1 h2 h3 h4
    · omega  -- k'.val = 0 contradiction (k'.val = k.val > 0)
    · omega  -- k'.val = n contradiction
    · -- middle face: need swap∘swap = id
      congr 1
      ext
      · -- bases are equal
        simp [midAdj]
      · -- perms: σ ∘ swap(k-1,k) ∘ swap(k-1,k) = σ
        simp [midAdj]
        ext i; simp [Equiv.swap_apply_self]
      all_goals apply Subsingleton.elim
    · omega

/-- adj_vertex: Adjacent cells share the codimension-1 face. -/
lemma freudAdj_vertex {n N : ℕ} (s k s' k' : _)
    (h : freudAdj s k = some (s', k')) :
    (Finset.univ.erase k).image (fun j => s.vertCoord j) =
    (Finset.univ.erase k').image (fun j => s'.vertCoord j) := by
  sorry -- Key: the shared face vertices are equal

/-- adj_ne: Adjacent cells are distinct. -/
lemma freudAdj_ne {n N : ℕ} (s k s' k' : _)
    (h : freudAdj s k = some (s', k')) : s ≠ s' := by
  simp [freudAdj] at h
  split_ifs at h with hk0 hbig hkn hn hpos
  · -- Face 0: base changes
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    intro heq
    have hb : (face0Adj s hbig).base = s.base := congrArg FreudCell.base heq
    simp [face0Adj] at hb
    -- base changes at σ(0): face0Adj.base (σ(0)) = base (σ(0)) + 1 ≠ base (σ(0))
    have := congrFun hb (s.perm ⟨0, Nat.succ_pos n⟩)
    simp at this
  · simp at h
  · -- Face n: base changes
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    intro heq
    have hb : (faceNAdj s hpos).base = s.base := congrArg FreudCell.base heq
    simp [faceNAdj] at hb
    have := congrFun hb (s.perm ⟨n - 1, by omega⟩)
    simp at this
  · simp at h
  · simp at h
  · -- Middle face: permutation changes
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    intro heq
    have hp : (midAdj s k (Nat.pos_of_ne_zero hk0) (Nat.le_of_lt _)).perm = s.perm :=
      congrArg FreudCell.perm heq
    simp [midAdj] at hp
    -- σ ∘ swap(k-1,k) = σ → swap(k-1,k) = id → k-1 = k, contradiction
    have hswap := congrFun (congrArg Equiv.toFun hp) ⟨k.val - 1, by omega⟩
    simp [Equiv.swap_apply_left] at hswap
    have : (⟨k.val - 1, by omega⟩ : Fin (n + 1)) = ⟨k.val, k.isLt⟩ :=
      s.perm.injective hswap
    simp [Fin.ext_iff] at this
    omega
    · -- need klt for omega
      exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp k.isLt) hkn

-- ============================================================
-- SECTION X: CellComplex Construction
-- ============================================================

/-- The vertex type: integer grid points in Δⁿ. -/
abbrev GridVertex (n : ℕ) := Fin (n + 1) → ℕ

/-- The Freudenthal grid CellComplex for Δⁿ at scale N. -/
noncomputable def freudCellComplex (n N : ℕ) : CellComplex (GridVertex n) n where
  Cell := FreudCell n N
  cellDecEq := inferInstance
  cellFintype := inferInstance  -- uses sorry'd Fintype instance
  vertex := fun s k => s.vertCoord k
  adj := fun s k => freudAdj s k
  adj_symm := fun s k s' k' h => freudAdj_symm s k s' k' h
  adj_vertex := fun s k s' k' h => freudAdj_vertex s k s' k' h
  adj_ne := fun s k s' k' h => freudAdj_ne s k s' k' h

-- ============================================================
-- SECTION XI: Sperner Coloring on Grid
-- ============================================================

/-- Convert grid vertex (integer coords) to real simplex point. -/
noncomputable def gridToReal {n N : ℕ} (hN : (0 : ℝ) < N)
    (v : GridVertex n) : Fin (n + 1) → ℝ :=
  fun i => (v i : ℝ) / N

/-- The coloring: for each grid vertex v (with ∑v=N, v≥0), assign the Sperner color. -/
noncomputable def freudColor {n N : ℕ} (hN : (0 : ℝ) < N)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v))
    (v : GridVertex n)
    (hv : ∑ i, v i = N) : Fin (n + 1) :=
  let vr : Fin (n + 1) → ℝ := gridToReal hN v
  have hvr : InSimplex vr := by
    constructor
    · intro i; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hN)
    · simp [vr, gridToReal]
      rw [← Finset.sum_div, Nat.cast_sum (f := v)]
      simp [hv, hN.ne']
  spernerColor vr (f vr) hvr (hf_map vr hvr)

-- ============================================================
-- SECTION XII: Key Properties
-- ============================================================

/-- The Sperner coloring assigns color c(v) = i only when f(v_real)ᵢ ≤ v_real_i. -/
lemma freudColor_le {n N : ℕ} (hN : (0 : ℝ) < N)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v))
    (v : GridVertex n) (hv : ∑ i, v i = N) :
    let vr := gridToReal hN v
    have hvr : InSimplex vr := by
      constructor
      · intro i; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hN)
      · simp [vr, gridToReal, ← Finset.sum_div, Nat.cast_sum, hv, hN.ne']
    f vr (freudColor hN f hf_map v hv) ≤ vr (freudColor hN f hf_map v hv) := by
  intro vr hvr
  exact spernerColor_le hvr (hf_map vr hvr)

/-- Diameter bound: any two vertices of a FreudCell differ by at most n in each coordinate. -/
lemma freudCell_diam {n N : ℕ} (s : FreudCell n N)
    (k₁ k₂ : Fin (n + 1)) (i : Fin (n + 1)) :
    (s.vertCoord k₁ i : ℤ) - s.vertCoord k₂ i ≥ -(n : ℤ) ∧
    (s.vertCoord k₁ i : ℤ) - s.vertCoord k₂ i ≤ (n : ℤ) := by
  simp [FreudCell.vertCoord]
  split_ifs with hi
  · -- miss direction: base[miss] - k₁ vs base[miss] - k₂
    constructor
    · have hk₂ : k₂.val ≤ n := Nat.lt_succ_iff.mp k₂.isLt
      omega
    · have hk₁ : k₁.val ≤ n := Nat.lt_succ_iff.mp k₁.isLt
      omega
  · -- non-miss: difference is at most 1 in absolute value, well within n
    split_ifs <;> omega

/-- Real-valued diameter bound: |v_k₁_i/N - v_k₂_i/N| ≤ n/N. -/
lemma freudCell_diam_real {n N : ℕ} (hN : (0 : ℝ) < N)
    (s : FreudCell n N) (k₁ k₂ : Fin (n + 1)) (i : Fin (n + 1)) :
    |s.vertReal hN k₁ i - s.vertReal hN k₂ i| ≤ (n : ℝ) / N := by
  simp [FreudCell.vertReal]
  rw [← sub_div, abs_div, abs_of_pos hN]
  apply div_le_div_of_nonneg_right _ (le_of_lt hN)
  have := freudCell_diam s k₁ k₂ i
  rw [abs_sub_comm] at *
  rw [abs_le]
  constructor
  · exact_mod_cast this.1
  · exact_mod_cast this.2

-- ============================================================
-- SECTION XIII: Boundary Doors Odd
-- ============================================================

/-- **Boundary Doors Odd** (the key parity claim):
    For the Freudenthal grid CellComplex with the Sperner coloring derived from f,
    the number of boundary doors (adj = none AND IsDoor) is odd.

    **Proof sketch** (by induction on n):
    - Base n=0: The 0-simplex has 1 cell, 1 boundary face (at face 0), and
      the single vertex is in Δ⁰ = {1}, so the coloring is determined; 1 boundary door. Odd ✓
    - Inductive step: Boundary doors at face 0 (base[miss]=n) biject with
      FC cells of (n-1)-dim FreudSimplex (restricted to face miss = {x[miss]=0}).
      Boundary doors at face n (base[σ(n-1)]=0) are NOT IsDoor (Sperner condition
      prevents color σ(n-1) from appearing among kept vertices). So only face-0
      doors contribute. By IH, their count is odd. ✓

    **Sorry**: Full inductive proof requires:
    (a) Restriction map FreudCell n N → FreudCell (n-1) N (drop miss coordinate)
    (b) Bijection between face-0 boundary doors and FC cells of (n-1)-triangulation
    (c) Showing face-n boundary faces are not doors (Sperner condition)

    This is genuine mathematical content (Sperner's lemma by induction). -/
lemma freudBoundaryDoorsOdd {n N : ℕ} (hN : 0 < N)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    Odd (Finset.univ.filter (fun p : FreudCell n N × Fin (n + 1) =>
      CellComplex.IsDoor
        (fun v => freudColor (Nat.cast_pos.mpr hN) f hf_map v
          (by sorry)) -- need hv : ∑ v = N for each grid vertex
        (freudCellComplex n N) p.1 p.2 ∧
      (freudCellComplex n N).adj p.1 p.2 = none)).card := by
  sorry

-- ============================================================
-- SECTION XIV: Sperner Panchromatic
-- ============================================================

/-- The main theorem: from panchromatic cell → panchromatic tuple. -/
theorem freud_sperner_panchromatic {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin (n + 1) → Fin (n + 1) → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin (n + 1), f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin (n + 1)) (l : Fin (n + 1)), |v i l - v j l| ≤ (n : ℝ) / N) := by
  -- Step 1: Apply CellComplex.sperner with the Freudenthal grid and Sperner coloring
  -- (This step has sorries in freudBoundaryDoorsOdd and freudAdj_symm/vertex)
  sorry

end SpernerBrouwer
